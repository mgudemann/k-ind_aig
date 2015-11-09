/*
Copyright (c) 2008 - 2010, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
*/

#include "../aiger/aiger.h"
#include "../picosat/picosat.h"

#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdarg.h>
#include <limits.h>
#include <ctype.h>
#include <signal.h>
#include <unistd.h>

#define SAT PICOSAT_SATISFIABLE
#define UNSAT PICOSAT_UNSATISFIABLE

/* #define _RUP_PROOF_ */

static aiger * model;
static int verbosity;
static double start;

static int witness;
static int ionly, bonly;
static int dcs, rcs, mix, ncs;
static unsigned * frames, sframes, nframes;
static unsigned nrcs;

#define SOLVER_NAME_MAX 256
#define SOLVER_RESULT_MAX 256
char solver_name[SOLVER_NAME_MAX];
char solver_result[SOLVER_RESULT_MAX];
char solver_cli[SOLVER_NAME_MAX * 2];

PicoSAT *solver;

static void
die (const char * fmt, ...)
{
  va_list ap;
  fprintf (stderr, "*** k-ind_aig: ");
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void
catch (int sig)
{
  fprintf (stderr, "*** k-ind_aig: caught signal(%d)\n", sig);
  fflush (stderr);

  if (verbosity > 1)
    picosat_stats (solver);

  fflush (stderr);

  kill (getpid (), sig);
}

static void
catchall (void)
{
  struct sigaction action;
  memset (&action, 0, sizeof action);
  action.sa_handler = catch;
  action.sa_flags = SA_NODEFER | SA_RESETHAND;
  sigaction (SIGSEGV, &action, 0);
  sigaction (SIGTERM, &action, 0);
  sigaction (SIGINT, &action, 0);
  sigaction (SIGABRT, &action, 0);
}

static void
msg (int level, int include_time, const char * fmt, ...)
{
  double delta;
  va_list ap;

  if (verbosity < level)
    return;

  fprintf (stderr, "[k-ind_aig] ");
  if (include_time)
    {
      delta = picosat_time_stamp () - start;
      fprintf (stderr, "%4.1f ", delta < 0.0 ? 0.0 : delta);
    }
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

static int
frame (int k)
{
  int res;

  res = k * model->maxvar + 2;
  if (dcs || rcs || mix)
    res += model->num_latches * k * (k - 1) / 2;

  return res;
}

static int
lit (unsigned k, unsigned l)
{
  int res;
  assert (0 <= l && l <= 2 * model->maxvar + 1);
  res =  (l <= 1) ? 1 : frame (k) + (int)((l - 2)/2);
  if (l & 1)
    res = -res;
  return res;
}

static int
input (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_inputs);
  return lit (k, model->inputs[i].lit);
}

static int
latch (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_latches);
  return lit (k, model->latches[i].lit);
}

static int
constraint (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_constraint);
  return lit (k, model->constraints[i].lit);
}

static int
next (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_latches);
  return lit (k, model->latches[i].next);
}

static int
bad_state (unsigned k, unsigned i)
{
  assert (0 <= i && i < model->num_bad);
  return lit (k, model->bad[i].lit);
}

static void
unary (int a)
{
  assert (a);
  picosat_add (solver, a);
  picosat_add (solver, 0);
}

static void
binary (int a, int b)
{
  assert (a);
  picosat_add (solver, a);
  assert (b);
  picosat_add (solver, b);
  picosat_add (solver, 0);
}

static void
ternary (int a, int b, int c)
{
  assert (a);
  picosat_add (solver, a);
  assert (b);
  picosat_add (solver, b);
  assert (c);
  picosat_add (solver, c);
  picosat_add (solver, 0);
}

static void
and (int lhs, int rhs0, int rhs1)
{
  binary (-lhs, rhs0);
  binary (-lhs, rhs1);
  ternary (lhs, -rhs0, -rhs1);
}

static void
eq (int lhs, int rhs)
{
  binary (-lhs, rhs);
  binary (lhs, -rhs);
}

static void
report (int verbosity, unsigned k, const char * phase)
{
  msg (verbosity, 1,
       "%4u %-10s %10d %11d %11u",
       k, phase,
       picosat_variables (solver), picosat_added_original_clauses (solver));
}

static void
connect (unsigned k)
{
  unsigned i;

  if (!k)
    return;

  for (i = 0; i < model->num_latches; i++)
    eq (next (k-1, i), latch (k, i));

  report (2, k, "connect");
}

static void
encode (unsigned k, unsigned po)
{
  aiger_and * a;
  unsigned i;

  if (!k)
      unary (lit (k, 1));		/* true */

  for (i = 0; i < model->num_ands; i++)
    {
      a = model->ands + i;
      and (lit (k, a->lhs), lit (k, a->rhs0), lit (k, a->rhs1));
    }

  /* encode constraints */
  for (i = 0; i < model->num_constraints; i++)
    {
      unary (constraint (k, i));
    }

  if (k)
    {
      for (i = 0; i < model->num_latches; i++)
        picosat_add (solver, latch (k, i));

      picosat_add (solver, 0);

      unary (-bad_state (k - 1, po));
    }

  report (2, k, "encode");
}

static int
diff (int k, int l, int i)
{
  assert (0 <= i && i < model->num_latches);
  assert (l < k);
  return frame (k + 1) - i - l * model->num_latches - 1;
}

static void
diffs (unsigned k, unsigned l)
{
  unsigned i, tmp;

  assert (k != l);

  if (l > k)
    {
      tmp = k;
      k = l;
      l = tmp;
    }

  for (i = 0; i < model->num_latches; i++)
    {
      ternary (latch (l, i), latch (k, i), -diff (k, l, i));
      ternary (-latch (l, i), -latch (k, i), -diff (k, l, i));
    }

  for (i = 0; i < model->num_latches; i++)
    picosat_add (solver, diff (k, l, i));

  picosat_add (solver, 0);

  msg (2, 1, "diffs %u %u", l, k);
}

static void
diffsk (unsigned k)
{
  unsigned l;

  if (!k)
    return;

  for (l = 0; l < k; l++)
    diffs (k, l);

  report (2, k, "diffsk");
}

static void
simple (unsigned k)
{
  if (dcs)
    diffsk (k);
  else
    assert (rcs || ncs);
}

static void
stimulus (unsigned k)
{
  unsigned i, j;
  int tmp;

  for (i = 0; i <= k; i++)
    {
      for (j = 0; j < model->num_inputs; j++)
        {
          tmp = picosat_deref (solver, input (i, j));
          fputc (tmp ? ((tmp < 0) ? '0' : '1') : 'x', stdout);
        }

      fputc ('\n', stdout);
    }
}

static void
bad (unsigned k, unsigned po)
{
  assert (model->num_bad > po);
  picosat_assume (solver, bad_state (k, po));
  report (2, k, "bad");
}

static void
init (unsigned k)
{
  unsigned i;
  int l;

  if (bonly && k)
    return;

  for (i = 0; i < model->num_latches; i++)
    {
      unsigned reset = model->latches[i].reset;

      /* treat cases with constant resets */
      if (reset <= 1)
        {
          if (reset == 0)
            l = -latch (0, i);
          else
            l = latch (0, i);
          if (bonly)
            unary (l);
          else
            picosat_assume (solver, l);
        }
      else
        {
          unsigned lit, reset;
          lit = model->latches[i].lit;
          reset = model->latches[i].reset;

          /* if equal, leave initial value undefined */
          /* if unequal -> fail, as unsupported by AIG */
          if (reset != lit)
            die ("reset of latch %s (%u / lit: %u) is undefined (%u)\n",
                 model->latches[i].name, i,
                 model->latches[i].lit,
                 model->latches[i].reset);
        }
    }

  report (2, k, "init");
}

static int
cmp_frames (const void * p, const void * q)
{
  unsigned k = *(unsigned *) p;
  unsigned l = *(unsigned *) q;
  int a, b, res;
  unsigned i;

  for (i = 0; i < model->num_latches; i++)
    {
      a = picosat_deref (solver, latch (k, i));
      b = picosat_deref (solver, latch (l, i));
      res = a - b;
      if (res)
        return res;
    }

  return 0;
}

static int
sat (unsigned k, unsigned po, char *cnf_file_name)
{
  unsigned i;
  int res, external_res;
  int cmp_res;
  char *fgets_res;
  FILE *fp;

  /* call solver and open pipe for communication */
  snprintf(solver_cli, 2*SOLVER_NAME_MAX, "%s %s", solver_name, cnf_file_name);
  if ((fp = popen(solver_cli, "r")) == NULL) {
    die ("Error opening pipe to solver");
  }

  /* read result from pipe */
  int next_char;
  while (1)
    {
      next_char = fgetc(fp);
      switch (next_char)
        {
        case EOF:
          die ("end of file from pipe before result from SAT query");
          break;
        default:
          switch ((char) next_char)
            {
              /* read result on "s $RESULT" */
            case 's':
              fgets_res = fgets(solver_result, SOLVER_RESULT_MAX, fp);
              cmp_res = strncmp(solver_result, " UNSATISFIABLE", 14);
              if (cmp_res == 0)
                {
                  external_res = PICOSAT_UNSATISFIABLE;
                  goto end;
                }
              cmp_res = strncmp(solver_result, " SATISFIABLE", 12);
              if (cmp_res == 0)
                {
                  external_res = PICOSAT_SATISFIABLE;
                  goto end;
                }
              die ("do not understand SAT solvers answer");
              break;
              /* skip whole line if not starting with 's' */
            default:
              while (next_char != '\n')
                  next_char = fgetc(fp);
            }
        }
    }
 end:

  pclose(fp);

  /*
    assume false to force picosat to return immediately
    TODO add real solution for this to simulate incremental solver
  */
  picosat_assume(solver, -1);
  picosat_assume(solver, 1);
  res = picosat_sat (solver, -1);

  return external_res;
}

static int
step (unsigned k, unsigned po)
{
  int res;
  bad (k, po);
  report (1, k, "step");

  char *cnfFileName = malloc(sizeof(char) * 30);
  snprintf(cnfFileName, 30, "step_k%u_po%u.cnf", k, po);
  FILE * cnfFile = fopen(cnfFileName, "w+");
  picosat_print(solver, cnfFile);
  fclose(cnfFile);

  res = (sat (k, po, cnfFileName) == UNSAT);
  free (cnfFileName);

  return res;
}

static int
base (unsigned k, unsigned po)
{
  int res;
#ifdef _DEBUG_
  printf ("encoding base k = %u\n", k);
#endif
#ifdef _DEBUG_
  printf ("encoding base / init k = %u\n", k);
#endif
  init (k);
#ifdef _DEBUG_
  printf ("encoding base / bad k = %u\n", k);
#endif
  bad (k, po);
  report (1, k, "base");
#ifdef _DEBUG_
  printf ("checking sat k = %u\n", k);
#endif

  char *cnfFileName = malloc(sizeof(char) * 30);
  snprintf(cnfFileName, 30, "base_k%u_po%u.cnf", k, po);
  FILE * cnfFile = fopen(cnfFileName, "w+");
  picosat_print(solver, cnfFile);
  fclose(cnfFile);

  res = (sat (k, po, cnfFileName) == SAT);
  free(cnfFileName);

  return res;
}

#define USAGE \
"k-ind_aig [<option> ...][<aiger>]\n" \
"\n" \
"where <option> is one of the following:\n" \
"\n" \
"  -h       print this command line summary and exit\n" \
"  -v       increase verbosity (default 0, max 3)\n" \
"  -b       base case only (only search for witnesses)\n" \
"  -w       print witness\n" \
"  -s <solver_CLI> command line of external DIMACS solver to use\n" \
"  <maxk>   maximum bound\n"

int
main (int argc, char ** argv)
{
  const char * name = 0, * err;
  unsigned k, maxk = UINT_MAX;
  int i, cs, res;
  double delta;

  start = picosat_time_stamp ();

  snprintf(solver_name, SOLVER_NAME_MAX, "glucose");

  for (i = 1; i < argc; i++)
    {
      if (!strcmp (argv[i], "-h"))
        {
          fprintf (stderr, USAGE);
          exit (0);
        }
      else if (!strcmp (argv[i], "-v"))
        verbosity++;
      else if (!strcmp (argv[i], "-b"))
        bonly = 1;
      else if (!strcmp (argv[i], "-w"))
        witness = 1;
      else if (isdigit (argv[i][0]))
        maxk = (unsigned) atoi (argv[i]);
      /* get name of external solver */
      else if (!strcmp (argv[i], "-s"))
        {
          snprintf(solver_name, SOLVER_NAME_MAX, "%s", argv[i+1]);
          i++;
        }
      else if (argv[i][0] == '-')
        die ("invalid command line option '%s'", argv[i]);
      else if (name)
        die ("multiple input files '%s' and '%s'", name, argv[i]);
      else
        name = argv[i];
    }

  if (ionly && bonly)
    die ("'-i' and '-b' can not be combined");

  cs = dcs + rcs + mix + ncs;
  if (cs > 1)
    die ("at most one of '-a', '-r', '-m', '-d', or '-n' can be used");

  if (bonly && (cs && !ncs))
    die ("can not combine '-b' with '-[armd]'");

  if (bonly)
    ncs = cs = 1;

  model = aiger_init ();

  msg (1, 0, "K-Ind_Aig Version 1 (based on McAiger version 2)");
  msg (1, 0, "parsing %s", name ? name : "<stdin>");

  if (name)
    err = aiger_open_and_read_from_file (model, name);
  else
    err = aiger_read_from_file (model, stdin);

  if (err)
    die (err);

  if (!model->num_bad)
    die ("no bad states found");

  int numberPOs = model->num_bad;
  if (numberPOs > 1)
    msg (1, 0, "more than one bad state found");

  aiger_reencode (model);

  msg (1, 0, "%u literals (MILOABC %u %u %u %u %u %u %u)",
       model->maxvar + 1,
       model->maxvar,
       model->num_inputs,
       model->num_latches,
       model->num_outputs,
       model->num_ands,
       model->num_bad,
       model->num_constraints);

  res = 0;

  for (int po = 0; po < numberPOs; po++)
    {

      solver = picosat_init ();
#ifdef _RUP_PROOF_
      picosat_enable_trace_generation (solver);
#endif

      catchall ();

      msg (1, 0, "checking po %u", po);

      picosat_set_prefix (solver, "[picosat] ");
      picosat_set_output (solver, stderr);

      if (verbosity > 2)
        picosat_set_verbosity (solver, verbosity);

      for (k = 0; k <= maxk; k++)
        {
#ifdef _DEBUG_
  printf("increasing k to %u\n", k);
#endif

#ifdef _DEBUG_
  printf("connecting k = %u\n", k);
#endif
          connect (k);
#ifdef _DEBUG_
          printf("encoding k = %u\n", k);
#endif
          encode (k, po);
#ifdef _DEBUG_
          printf("simple k = %u\n", k);
#endif
          simple (k);

#ifdef _DEBUG_
          printf("step k = %u\n", k);
#endif
          if (!bonly && step (k, po))
            {
              report (1, k, "inductive");
              fputs ("0\n", stdout);
#ifdef _RUP_PROOF_
              report (1, k, "writing CNF/RUP proof file");
              char *rupFileName = malloc(sizeof(char) * 30);
              char *cnfFileName = malloc(sizeof(char) * 30);
              snprintf(rupFileName, 30, "proof_po%u.rup", po);
              snprintf(cnfFileName, 30, "proof_po%u.cnf", po);
              FILE * rupFile = fopen(rupFileName, "w+");
              FILE * cnfFile = fopen(cnfFileName, "w+");
              picosat_write_rup_trace(solver, rupFile);
              picosat_print(solver, cnfFile);
              fclose(rupFile);
              fclose(cnfFile);
#ifdef _DEBUG_
              printf("written CNF / RUP files %s / %s\n", cnfFileName, rupFileName);
#endif
              free(rupFileName);
              free(cnfFileName);
#endif
              res = 20;
              break;
            }

#ifdef _DEBUG_
          printf("inconsistent k = %u\n", k);
#endif
          if (bonly && picosat_inconsistent (solver))
            {
              report (1, k, "inconsistent");
              fputs ("0\n", stdout);
              res = 20;
              break;
            }

#ifdef _DEBUG_
          printf("base k = %u\n", k);
#endif
          if (!ionly && base (k, po))
            {
              report (1, k, "reachable");
              fputs ("1\n", stdout);
              if (witness)
                stimulus (k);
              res = 10;
              break;
            }
        }

      if (k > maxk) {
        report (1, k, "indeterminate");
        fputs ("2\n", stdout);
      }

      fflush (stdout);

      if (verbosity > 1)
        picosat_stats (solver);

      picosat_reset (solver);
    }

  aiger_reset (model);

  free (frames);

  if (rcs || mix)
    msg (1, 0, "%u refinements of simple path constraints", nrcs);

  delta = picosat_time_stamp () - start;
  msg (1, 0, "%.1f seconds", delta < 0.0 ? 0.0 : delta);

  return res;
}

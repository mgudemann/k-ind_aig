CFLAGS=-Wall -DNDEBUG -O3
all: k-ind_aig
OBJ=k-ind_aig.o ../aiger/aiger.o ../picosat/picosat.o
k-ind_aig: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $(OBJ)
k-ind_aig.o: ../aiger/aiger.h ../picosat/picosat.h makefile
clean:
	rm -f k-ind_aig *.o
.PHONY: all clean

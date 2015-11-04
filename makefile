CFLAGS=-Wall -DNDEBUG -O3
all: k-ind_aig
OBJ=k-ind_aig.o ../aiger/aiger.o ../picosat-936/picosat.o
k-ind_aig: $(OBJ)
	$(CC) $(CFLAGS) -o $@ $(OBJ)
k-ind_aig.o: ../aiger/aiger.h ../picosat-936/picosat.h makefile
clean:
	rm -f k-ind_aig *.o
.PHONY: all clean

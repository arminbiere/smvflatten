SRC=../../../../src
OBJ=../../../../obj
CC=gcc
CFLAGS=-g -Wall -W -I$(SRC) -DLEAK
LD=gcc

OBJS=0006.o $(OBJ)/assoc.o $(OBJ)/prime.o $(OBJ)/node.o

a.out: 0006.o other-objs
	$(LD) $(OBJS) -leak

0006.o: ../0006.c $(SRC)/assoc.h $(SRC)/node.h
	$(CC) $(CFLAGS) -c -o $@ ../0006.c

other-objs:
	cd ../../../..; make obj/assoc.o obj/prime.o obj/node.o src/y.tab.c

.PHONY: other-objs

SRC=../../../../src
OBJ=../../../../obj
CC=gcc
CFLAGS=-g -Wall -W -I$(SRC) -DLEAK
LD=gcc

OBJS=0003.o $(OBJ)/node.o $(OBJ)/prime.o $(OBJ)/assoc.o

a.out: 0003.o other-objs
	$(LD) $(OBJS) -leak

0003.o: ../0003.c $(SRC)/node.h $(SRC)/prime.h $(SRC)/y.tab.h
	$(CC) $(CFLAGS) -c -o $@ ../0003.c

other-objs:
	cd ../../../..; make obj/node.o obj/prime.o obj/assoc.o

.PHONY: other-objs

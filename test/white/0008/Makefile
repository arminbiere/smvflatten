SRC=../../../../src
OBJ=../../../../obj
CC=gcc
CFLAGS=-g -Wall -W -I$(SRC) -DLEAK
LD=gcc

OBJS=0008.o $(OBJ)/node.o $(OBJ)/prime.o $(OBJ)/assoc.o

a.out: 0008.o other-objs
	$(LD) $(OBJS) -leak

0008.o: ../0008.c $(SRC)/node.h $(SRC)/prime.h
	$(CC) $(CFLAGS) -c -o $@ ../0008.c

other-objs:
	cd ../../../..; make obj/node.o obj/prime.o obj/assoc.o

.PHONY: other-objs

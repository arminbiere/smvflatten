SRC=../../../../src
OBJ=../../../../obj
CC=gcc
CFLAGS=-g -Wall -W -I$(SRC) -DLEAK
LD=gcc

OBJS=0004.o $(OBJ)/assoc.o $(OBJ)/prime.o

a.out: 0004.o other-objs
	$(LD) $(OBJS) -leak

0004.o: ../0004.c $(SRC)/assoc.h
	$(CC) $(CFLAGS) -c -o $@ ../0004.c

other-objs:
	cd ../../../..; make obj/assoc.o obj/prime.o

.PHONY: other-objs

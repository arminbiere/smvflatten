SRC=../../../../src
OBJ=../../../../obj
CC=gcc
CFLAGS=-g -Wall -W -I$(SRC) -DLEAK
LD=gcc

OBJS=0005.o $(OBJ)/assoc.o $(OBJ)/prime.o

a.out: 0005.o other-objs
	$(LD) $(OBJS) -leak

0005.o: ../0005.c $(SRC)/assoc.h
	$(CC) $(CFLAGS) -c -o $@ ../0005.c

other-objs:
	cd ../../../..; make obj/assoc.o obj/prime.o

.PHONY: other-objs

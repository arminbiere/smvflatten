#include <signal.h>
#include <stdio.h>

static void handler(int sig) { (void) sig; exit(1); }

#include "node.h"
#include "y.tab.h"

#include <leak.h>

#ifdef LEAK
int enable_nnf = 1, verbose = 0;
#else
int enable_nnf = 1, verbose = 10;
#endif

int simplification_level = 0;

int main()
{
  int res;
  Node * n[3];

  signal(SIGSEGV, &handler);
  signal(SIGABRT, &handler);
  signal(SIGBUS, &handler);

#ifdef LEAK
  leak_reset();
#endif

  init_Node();
  n[0] = atom("main");
  n[1] = cons(n[0], 0);
  n[2] = new(MODULE, n[1], 0);
#ifndef LEAK
  print(n[2]);
#endif
  delete(n[2]);
  res = (count_Node() > 0);
  exit_Node();

#ifdef LEAK
  if(leak_report()) exit(1);
#endif

  fputs("OK\n", stdout);
  exit(0);
  return 0;
}

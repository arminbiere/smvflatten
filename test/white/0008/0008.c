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
  Node * a, * b, * c;
  int res;

  signal(SIGSEGV, &handler);
  signal(SIGABRT, &handler);
  signal(SIGBUS, &handler);

#ifdef LEAK
  leak_reset();
#endif
  
  res = 1;
  init_Node();
  a = cons(number(0), cons(number(1), cons(number(2), 0)));
  if(res) res = (count_Node() == 6);
  b = cons(number(3), cons(number(4), cons(number(5), 0)));
  if(res) res = (count_Node() == 12);
  c = append(a, b);
  if(res) res = (count_Node() == 15);
  delete(b);
  if(res) res = (count_Node() == 15);
  delete(a);
  if(res) res = (count_Node() == 12);

#ifndef LEAK
  printnl(c);
#endif

  delete(c);
  if(res) res = !count_Node();
  exit_Node();

  if(!res) exit(1);

#ifdef LEAK
  if(leak_report()) exit(1);
#endif

  fputs("OK\n", stdout);
  exit(0);
  return 0;
}

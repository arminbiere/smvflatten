#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

static void handler(int sig) { (void) sig; exit(1); }

#include "assoc.h"
#include "node.h"
#include "y.tab.h"

#include <leak.h>

int enable_nnf = 1, verbose = 0;
int simplification_level = 0;

/*------------------------------------------------------------------------*/

int main()
{
  Node * a, * b, * l[2], * a_and_b, * b_and_a, * res;
  Assoc * sub;
  int ok;

  signal(SIGSEGV, &handler);
  signal(SIGABRT, &handler);
  signal(SIGBUS, &handler);

#ifdef LEAK
  leak_reset();
#endif

  ok = 1;
  init_Node();
  a = atom("a");
  b = atom("b");
  a_and_b = new(AND, a, b);
  l[0] = cons(a_and_b, cons(cons(copy(a), 0), cons(copy(a_and_b), 0)));
  b_and_a = new(AND, copy(b), copy(a));
  l[1] = cons(b_and_a, cons(cons(copy(b), 0), cons(copy(b_and_a), 0)));
  sub = new_Assoc();
  associate(sub, a, b);
  associate(sub, b, a);
  res = substitute(l[0], sub);
  ok = (res == l[1]);
  delete_Assoc(sub);
  delete(l[0]);
  delete(l[1]);
  delete(res);
  if(ok) ok = !count_Node();
  exit_Node();

  if(!ok) exit(1);

#ifdef LEAK
  if(leak_report()) exit(1);
#endif

  fputs("OK\n", stdout);
  exit(0);
  return 0;
}

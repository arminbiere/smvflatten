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
  Node * a, * b, * a_and_b, * res;
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
  sub = new_Assoc();
  associate(sub, a, b);
  associate(sub, b, a);
  res = substitute(a_and_b, sub);
  if(ok) ok = (res -> ref == 1);
  if(ok) ok = (res -> tag == AND);
  if(ok) ok = (count_Node() == 4);
  if(ok) ok = (car(res) == b);
  if(ok) ok = (cdr(res) == a);
  if(ok) ok = (car(res) -> ref == 2);
  if(ok) ok = (cdr(res) -> ref == 2);
  delete_Assoc(sub);
  delete(a_and_b);
  if(ok) ok = (count_Node() == 3);
  delete(res);
  if(ok) ok = (count_Node() == 0);
  exit_Node();

  if(!ok) exit(1);

#ifdef LEAK
  if(leak_report()) exit(1);
#endif

  fputs("OK\n", stdout);
  exit(0);
  return 0;
}

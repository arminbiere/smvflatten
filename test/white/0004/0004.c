#include <signal.h>
#include <stdio.h>

static void handler(int sig) { (void) sig; exit(1); }

#include "assoc.h"

#include <leak.h>

int main()
{
  Assoc * assoc;

#ifdef LEAK
  leak_reset();
#endif

  signal(SIGSEGV, &handler);
  signal(SIGABRT, &handler);
  signal(SIGBUS, &handler);

  assoc = new_Assoc();
  delete_Assoc(assoc);

#ifdef LEAK
  if(leak_report()) exit(1);
#endif

  fputs("OK\n", stdout);
  exit(0);
  return 0;
}

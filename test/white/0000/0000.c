#include <signal.h>
#include <stdio.h>

static void handler(int sig) { (void) sig; exit(1); }

int main()
{
  signal(SIGSEGV, &handler);
  signal(SIGABRT, &handler);
  signal(SIGBUS, &handler);

  *(int*)0 = 0;

  fputs("OK\n", stdout);
  exit(0);
  return 0;
}

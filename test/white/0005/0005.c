#include <signal.h>
#include <stdio.h>
#include <stdlib.h>

static void handler(int sig) { (void) sig; exit(1); }

#include "assoc.h"

#include <leak.h>

#define N 1000

static int data[N];

static int r()
{
  int res;

  res = rand();
  if(res < 0) res = - res;
  res = res % N;

  return res;
}

/*------------------------------------------------------------------------*/

static void sum_functor(int * sum, int s) { *sum += s; }

/*------------------------------------------------------------------------*/

static void sum_both(int * sum, int s, int d) { *sum += s + d; }

/*------------------------------------------------------------------------*/

int main()
{
  Assoc * assoc;
  int i, j, ok, s[2], d[2], both, found;

  signal(SIGSEGV, &handler);
  signal(SIGABRT, &handler);
  signal(SIGBUS, &handler);

  for(i = 0; i < N; i++) data[i] = r();

#ifdef LEAK
  leak_reset();
#endif

  ok = 1;
  assoc = new_Assoc();

  for(i = 0; i < N; i++)
    associate(assoc, (void*)data[i], (void*)(N - data[i]));

  for(i = 0; ok && i < N; i++) ok = is_associated(assoc, (void*)data[i]);

  for(i = 0; ok && i < N; i++)
    ok = (N - data[i] == (int)get_association(assoc, (void*)data[i]));

  for(i = 0, s[0] = 0; i < N; i++) s[0] += data[i];
  for(i = 0, d[0] = 0; i < N; i++) d[0] += N - data[i];

  for(i = 0; i < N - 1; i++)
    {
      for(j = i + 1, found = 0; !found && j < N; j++)
        found = (data[i] == data[j]);
      
      if(found) s[0] -= data[i];
      if(found) d[0] -= N - data[i];
    }

  s[1] = 0;
  map_src_in_Assoc(assoc, (void*)&s[1], (void(*)(void*,void*)) sum_functor);
  if(ok) ok = (s[0] == s[1]);

  d[1] = 0;
  map_dst_in_Assoc(assoc, (void*)&d[1], (void(*)(void*,void*)) sum_functor);
  if(ok) ok = (d[0] == d[1]);

  both = 0;
  map_Assoc(assoc, (void*)&both, (void(*)(void*,void*,void*)) sum_both);
  if(ok) ok = (both == s[0] + d[0]);

  delete_Assoc(assoc);

  if(!ok) exit(1);

#ifdef LEAK
  if(leak_report()) exit(1);
#endif

  fputs("OK\n", stdout);
  exit(0);
  return 0;
}

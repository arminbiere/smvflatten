/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "cache.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

extern int verbose;

/*------------------------------------------------------------------------*/

Cache * new_Cache(const char * name)
{
  Cache * res;

  res = (Cache*) malloc(sizeof(Cache));
  res -> assoc = new_Assoc();
  res -> lookups = res -> hits = 0.0;
  res -> name = (char*) strdup(name);
  
  return res;
}

/*------------------------------------------------------------------------*/

void delete_Cache(Cache * cache)
{
  double hit_rate;

  if(verbose >= 2)
    {
      fprintf(
        stderr,
        "-- [verbose]   %s: %.0f lookups",
	cache -> name,
	cache -> lookups);

      if(cache -> lookups > 0)
        {
	  hit_rate = cache -> hits / cache -> lookups;
	  fprintf(
	    stderr,
	    ", %.0f hits (%.1f%%)",
	    cache -> hits,
	    100.0 * hit_rate);
	}
      
      fputc('\n', stderr);
    }
  
  free(cache -> name);
  delete_Assoc(cache -> assoc);
  free(cache);
}

/*------------------------------------------------------------------------*/

void insert_Cache(Cache * cache, void * src, void * dst)
{
  assert(!is_associated(cache -> assoc, src));

  associate(cache -> assoc, src, dst);
}

/*------------------------------------------------------------------------*/

void * lookup_Cache(Cache * cache, void * src)
{
  void * res;

  assert(is_associated(cache -> assoc, src));
  res = get_association(cache -> assoc, src);

  return res;
}

/*------------------------------------------------------------------------*/

int is_cached(Cache * cache, void * src)
{
  int res;

  res = is_associated(cache -> assoc, src);
  cache -> lookups++;
  if(res) cache -> hits++;

  return res;
}

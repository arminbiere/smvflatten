#ifndef _cache_h_INCLUDED
#define _cache_h_INCLUDED

/*------------------------------------------------------------------------*/
/* Copyright 1999-2011 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"

/*------------------------------------------------------------------------*/

typedef struct Cache Cache;

struct Cache
{
  Assoc * assoc;
  double lookups, hits;
  char * name;
};

/*------------------------------------------------------------------------*/

extern Cache * new_Cache(const char *);
extern void delete_Cache(Cache *);

/*------------------------------------------------------------------------*/

extern void insert_Cache(Cache *, void *, void *);
extern void * lookup_Cache(Cache *, void *);
extern int is_cached(Cache *, void *);

/*------------------------------------------------------------------------*/

#endif

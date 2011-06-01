/*------------------------------------------------------------------------*/
/* Copyright 1999-2011 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/
#include "assoc.h"
#include "prime.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct AssocBucket AssocBucket;

/*------------------------------------------------------------------------*/

struct AssocBucket
{
  void * src;
  void * dst;
  AssocBucket * next;
};

/*------------------------------------------------------------------------*/

struct Assoc
{
  AssocBucket ** table;
  unsigned size, num;
};

/*------------------------------------------------------------------------*/

Assoc * new_Assoc(void)
{
  Assoc * res;

  res = (Assoc*) malloc(sizeof(Assoc));
  res -> size = next_prime(0);
  res -> num = 0;
  res -> table = (AssocBucket**) calloc(res -> size, sizeof(AssocBucket*));

  return res;
}

/*------------------------------------------------------------------------*/

void reset_Assoc(Assoc * assoc)
{
  AssocBucket * p, * tmp;
  unsigned i;

  for(i = 0; i < assoc -> size; i++)
    {
      tmp = assoc -> table[i];
      assoc -> table[i] = 0;
      for(p = tmp; p; p = tmp)
	{
	  tmp = p -> next;
	  free(p);
	}
    }
  
  assoc -> num = 0;
}

/*------------------------------------------------------------------------*/

void delete_Assoc(Assoc * assoc)
{
  reset_Assoc(assoc);
  free(assoc -> table);
  free(assoc);
}

/*------------------------------------------------------------------------*/

static void resize_Assoc(Assoc * assoc, unsigned new_size)
{
  AssocBucket ** old_table, * p, * tmp;
  unsigned old_size, i, h;

  old_size = assoc -> size;
  old_table = assoc -> table;

  assoc -> size = next_prime(new_size);
  assoc -> table = (AssocBucket**) calloc(assoc -> size, sizeof(AssocBucket*));

  for(i = 0; i < old_size; i++)
    for(p = old_table[i]; p; p = tmp)
      {
        tmp = p -> next;
	h = ((unsigned)(long)(p -> src)) % assoc -> size;
	p -> next = assoc -> table[h];
	assoc -> table[h] = p;
      }
  
  free(old_table);
}

/*------------------------------------------------------------------------*/

static AssocBucket ** find_Assoc(Assoc * assoc, void * src)
{
  AssocBucket ** p;
  unsigned h;

  h = ((unsigned) (long)src) % assoc -> size;
  for(p = &assoc -> table[h]; *p && (*p) -> src != src; p = &(*p) -> next)
    ;
  
  return p;
}

/*------------------------------------------------------------------------*/

void associate(Assoc * assoc, void * src, void * dst)
{
  AssocBucket ** p, * res;

  if(assoc -> num > 2 * assoc -> size) resize_Assoc(assoc, assoc -> num * 2);

  p = find_Assoc(assoc, src);

  if(*p)
    {
      res = *p;

      assert(res -> src == src);
    }
  else
    {
      res = (AssocBucket*) malloc(sizeof(AssocBucket));
      res -> src = src;
      res -> next = 0;

      *p = res;
      assoc -> num++;
    }

  res -> dst = dst;
}

/*------------------------------------------------------------------------*/

void deassociate(Assoc * assoc, void * src)
{
  AssocBucket ** p, * tmp;

  p = find_Assoc(assoc, src);
  tmp = *p;

  if(tmp)
    {
      *p = tmp -> next;
      free(tmp);
      assoc -> num--;
    }
}

/*------------------------------------------------------------------------*/

int is_associated(Assoc * assoc, void * src)
{
  int res;

  res = (*find_Assoc(assoc, src) != 0);

  return res;
}

/*------------------------------------------------------------------------*/

void * get_association(Assoc * assoc, void * src)
{
  AssocBucket ** p;
  void * res;

  p = find_Assoc(assoc, src);
  res = *p ? (*p) -> dst : (void*) 0;

  return res;
}

/*------------------------------------------------------------------------*/

void map_Assoc(Assoc * assoc, void * state, void(*f)(void*,void*,void*))
{
  AssocBucket * p;
  unsigned i;

  for(i = 0; i < assoc -> size; i++)
    for(p = assoc -> table[i]; p; p = p -> next)
      (*f)(state, p -> src, p -> dst);
}

/*------------------------------------------------------------------------*/

void map_dst_in_Assoc(Assoc * assoc, void * state, void(*f)(void*,void*))
{
  AssocBucket * p;
  unsigned i;

  for(i = 0; i < assoc -> size; i++)
    for(p = assoc -> table[i]; p; p = p -> next)
      (*f)(state, p -> dst);
}

/*------------------------------------------------------------------------*/

void map_src_in_Assoc(Assoc * assoc, void * state, void(*f)(void*,void*))
{
  AssocBucket * p;
  unsigned i;

  for(i = 0; i < assoc -> size; i++)
    for(p = assoc -> table[i]; p; p = p -> next)
      (*f)(state, p -> src);
}

/*------------------------------------------------------------------------*/

void forall_Assoc(Assoc * assoc, void(*f)(void*,void*))
{
  AssocBucket * p;
  unsigned i;

  for(i = 0; i < assoc -> size; i++)
    for(p = assoc -> table[i]; p; p = p -> next)
      (*f)(p -> src, p -> dst);
}

/*------------------------------------------------------------------------*/

void forall_dst_in_Assoc(Assoc * assoc, void(*f)(void*))
{
  AssocBucket * p;
  unsigned i;

  for(i = 0; i < assoc -> size; i++)
    for(p = assoc -> table[i]; p; p = p -> next)
      (*f)(p -> dst);
}

/*------------------------------------------------------------------------*/

void forall_src_in_Assoc(Assoc * assoc, void(*f)(void*))
{
  AssocBucket * p;
  unsigned i;

  for(i = 0; i < assoc -> size; i++)
    for(p = assoc -> table[i]; p; p = p -> next)
      (*f)(p -> src);
}

/*------------------------------------------------------------------------*/

unsigned count_Assoc(Assoc * assoc)
{
  return assoc -> num;
}


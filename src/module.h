#ifndef _module_h_INCLUDED
#define _module_h_INCLUDED

/*------------------------------------------------------------------------*/
/* Copyright 1999-2011 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "node.h"

/*------------------------------------------------------------------------*/

typedef struct Module_ Module;

/*------------------------------------------------------------------------*/

struct Module_
{
  Node * var;
  Node * define;
  Node * assign;
  Node * invar;
  Node * init;
  Node * trans;
  Node * fairness;
  Node * spec;
  Node * ltlspec;
  Node * compute;
};

/*------------------------------------------------------------------------*/

extern void init_Module(Module *);
extern Node * merge_Module(Module *);
extern void release_Module(Module *);
extern Node ** section_Module(Module *, Node * node);

/*------------------------------------------------------------------------*/

#endif

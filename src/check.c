#include "check.h"
#include "type.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

/*------------------------------------------------------------------------*/

extern int verbose;

/*------------------------------------------------------------------------*/

typedef struct CNCContext CNCContext;

/*------------------------------------------------------------------------*/

struct CNCContext
{
  Assoc * mark, * invar_assignments, * definitions;
};

/*------------------------------------------------------------------------*/

#define MARKED 1
#define IS_ON_STACK 2

/*------------------------------------------------------------------------*/

static void insert_in_CNCContext(CNCContext * context, Node * node)
{
  if(node)
    {
      switch(node -> tag)
        {
	  case LIST:
	    insert_in_CNCContext(context, car(node));
	    insert_in_CNCContext(context, cdr(node));
	    break;
	  
	  case MODULE:
	    insert_in_CNCContext(context, cdr(node));
	    break;
	  
	  case DEFINEASSIGNMENT:
	    associate(context -> definitions, car(node),  cdr(node));
	    break;
	  
	  case INVARASSIGNMENT:
	    associate(context -> invar_assignments, car(node),  cdr(node));
	    break;
	  
	  case ASSIGN:
	  case DEFINE:
	    insert_in_CNCContext(context, car(node));
	    break;
	  
	  default:
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void setup_CNCContext(CNCContext * context, Node * node)
{
  context -> mark = new_Assoc();
  context -> invar_assignments = new_Assoc();
  context -> definitions = new_Assoc();
  insert_in_CNCContext(context, node);
}

/*------------------------------------------------------------------------*/

static void release_CNCContext(CNCContext * context)
{
  delete_Assoc(context -> invar_assignments);
  delete_Assoc(context -> definitions);
  delete_Assoc(context -> mark);
}

/*------------------------------------------------------------------------*/

static void cnc(CNCContext * context, Node * node)
{
  unsigned mark;
  Node * def;

  if(node)
    {
      switch(node -> tag)
        {
	  case ACCESS:
	  case ATOM:
	    mark = (unsigned) get_association(context -> mark, node);
	    if(mark & IS_ON_STACK)
	      {
	        fputs("*** smvflatten: `", stderr);
		print(stderr, node);
		fputs("' recursively defined\n", stderr);
		exit(1);
	      }
	    else 
	    if(!mark)
	      {
		def = get_association(context -> invar_assignments, node);
		if(!def) def = get_association(context -> definitions, node);
		if(def)
		  {
		    associate(
		      context -> mark, node, (void*)(MARKED|IS_ON_STACK));
		    cnc(context, def);
		  }

	        associate(context -> mark, node, (void*)(MARKED));
	      }
	    break;
	  
	  case MODULE:
	    cnc(context, cdr(node));
	    break;
	  
	  case DEFINEASSIGNMENT:
	  case INVARASSIGNMENT:
	    cnc(context, car(node));
	    break;

	  case BOOLEAN:
	  case FAIRNESS:
	  case INIT:
	  case INVAR:
	  case NUMBER:
	  case SPEC:
	  case TRANS:
	  case VAR:
	    break;
	  
	  default:
	    cnc(context, car(node));
	    cnc(context, cdr(node));
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void check_non_recursive(Node * node)
{
  CNCContext context;

  if(verbose)
    {
      fputs("-- [verbose] checking for recursive definitions ...\n", stderr);
    }
  
  setup_CNCContext(&context, node);
  cnc(&context, node);
  release_CNCContext(&context);

  if(verbose)
    {
      fputs("-- [verbose] definitions are not recursive.\n", stderr);
    }
}

/*------------------------------------------------------------------------*/

Assoc * check(Node * node)
{
  Assoc * res;
  
  if(verbose) fputs("-- [verbose] phase 3: semantic checks ...\n", stderr);
  check_non_recursive(node);
  res = typify(node);
  if(verbose) fputs("-- [verbose] end of phase 3: checked.\n", stderr);

  return res;
}

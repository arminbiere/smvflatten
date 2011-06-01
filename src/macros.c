/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"
#include "macros.h"
#include "module.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>

/*------------------------------------------------------------------------*/

extern int verbose;

/*------------------------------------------------------------------------*/

typedef struct ExMacrosContext ExMacrosContext;

struct ExMacrosContext
{
  Assoc * node2macro, * occurences;
  Module module;
  unsigned num_extracted_macros;
};

/*------------------------------------------------------------------------*/

static void init_occurences(Assoc * occurences, Node * node)
{
  unsigned old;

  if(node)
    {
      old = (long) get_association(occurences, node);
      if(old < 2) associate(occurences, node, (void*)(long)(old + 1));

      switch(node -> tag)
        {
	  case ATOM:
	  case NUMBER:
	    break;
	  
	  default:
	    init_occurences(occurences, car(node));
	    init_occurences(occurences, cdr(node));
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void init_ExMacrosContext(ExMacrosContext * context, Node * node)
{
  context -> node2macro = new_Assoc();
  context -> occurences = new_Assoc();
  init_occurences(context -> occurences, node);
  context -> num_extracted_macros = 0;
  init_Module(&context -> module);
}

/*------------------------------------------------------------------------*/

static void release_ExMacrosContext(
  ExMacrosContext * context, Node * old, Node * new)
{
  double old_size, new_size, reduction;

  if(verbose >= 2)
    {
      old_size = term_size(old);
      new_size = term_size(new);

      reduction = 100 * (old_size - new_size) / old_size;

      fprintf(
        stderr,
	"-- [verbose]   extracted %u macros (%0.2f%% reduction)\n",
	context -> num_extracted_macros,
	reduction);
    }

  delete_Assoc(context -> occurences);
  delete_Assoc(context -> node2macro);
  release_Module(&context -> module);
}

/*------------------------------------------------------------------------*/

static int can_be_redefined(Node * node)
{
  int res;

  assert(node);

  if(node -> contains_temporal_operator) res = 0;
  else
    {
      switch(node -> tag)
	{
	  case LIST:
	  case COLON:
	    res = 0;
	    break;

	  default:
	    res = 1;
	    break;
	}
    }

  return res;
}

/*------------------------------------------------------------------------*/

static Node * em(ExMacrosContext * context, Node * node)
{
  Node * res, * a, * b, * macro, * rhs, * definition, * not_node;
  unsigned ref;
  Module * m;

  if(node)
    {
      if(is_literal(node) || is_constant(node)) res = copy(node);
      else
      if(is_associated(context -> node2macro, node))
	{
	  res = copy(get_association(context -> node2macro, node));
	}
      else
      if(can_be_redefined(node))
        {
	  /* If a term occurs negated and unnegated take the first
	   * occurence for generating a macro.  Just using the reference
	   * count did not work because of potential dead nodes with
	   * positive reference.
	   */
	  not_node = new_simplify(NOT, copy(node), 0);

	  if(is_associated(context -> node2macro, not_node))
	    {
	      res = copy(get_association(context -> node2macro, not_node));
	      delete(not_node);
	      res = new_simplify(NOT, res, 0);
	    }
	  else
	    {
	      ref = (long)get_association(context->occurences, node) +
		    (long)get_association(context->occurences, not_node);

	      delete(not_node);

	      if(ref >= 2)
		{
		  macro = new_macro();
		  a = em(context, car(node));
		  b = em(context, cdr(node));
		  rhs = new(node -> tag, a, b);
		  definition = new(DEFINEASSIGNMENT, macro, rhs);
		  m = &context -> module;
		  m -> define = cons(definition, m -> define);
		  associate(context -> node2macro, node, macro);
		  context -> num_extracted_macros++;
		  res = copy(macro);
		}
	      else
		{
		  a = em(context, car(node));
		  b = em(context, cdr(node));
		  res = new(node -> tag, a, b);
		}
	    }
	}
      else
	{
	  a = em(context, car(node));
	  b = em(context, cdr(node));
	  res = new(node -> tag, a, b);
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static void em_toplevel(ExMacrosContext * context, Node * node)
{
  Node * macro, * var, * assignment, * tmp, ** sptr;
  Module * m;
  int tag;

  if(node)
    {
      m = &context -> module;

      switch((tag = node -> tag))
        {
	  case MODULE:
	    em_toplevel(context, cdr(node));
	    break;

	  case LIST:
	    em_toplevel(context, car(node));
	    em_toplevel(context, cdr(node));
	    break;

	  case VAR:
	  case ASSIGN:
	  case DEFINE:
	    em_toplevel(context, car(node));
	    break;
	  
	  case DECL:
	    m -> var = cons(copy(node), m -> var);
	    break;
	  
	  case INITASSIGNMENT:
	  case TRANSASSIGNMENT:
	  case INVARASSIGNMENT:
	  case DEFINEASSIGNMENT:

	    var = copy(car(node));
	    macro = em(context, cdr(node));
	    assignment = new(tag, var, macro);

	    if(tag == DEFINEASSIGNMENT) sptr = &m -> define;
	    else sptr = &m -> assign;

	    *sptr = cons(assignment, *sptr);
	    break;

	  case INVAR:
	  case INIT:
	  case TRANS:

	    if(tag == INVAR) sptr = &m -> invar;
	    else if(tag == INIT) sptr = &m -> init;
	    else sptr = &m -> trans;

	    tmp = *sptr ? *sptr : number(1);
	    macro = em(context, car(node));

	    *sptr = new_simplify(AND, tmp, macro);
	    break;

	  case FAIRNESS:
	    macro = em(context, car(node));
	    m -> fairness = cons(macro, m -> fairness);
	    break;

	  case COMPUTE:
	    macro = em(context, car(node));
	    m -> compute = cons(macro, m -> compute);
	    break;

	  case SPEC:
	    macro = em(context, car(node));
	    m -> spec = cons(macro, m -> spec);
	    break;

	  default:
	    assert(!"valid tag");
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

Node * extract_macros(Node * node)
{
  ExMacrosContext context;
  Node * res;

  if(verbose) fputs("-- [verbose] phase 6: extracting macros ...\n", stderr);

  init_ExMacrosContext(&context, node);
  em_toplevel(&context, node);
  res = merge_Module(&context.module);
  release_ExMacrosContext(&context, node, res);

  if(verbose) fputs("-- [verbose] end of phase 6: macros extracted.\n", stderr);

  return res;
}

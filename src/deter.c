/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"
#include "deter.h"
#include "module.h"
#include "node.h"
#include "pp.h"
#include "type.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

/*------------------------------------------------------------------------*/

extern int verbose;
extern unsigned max_size_quantified_oracle;

/*------------------------------------------------------------------------*/

typedef struct DtContext DtContext;

struct DtContext
{
  unsigned max_next, num_oracles, num_oracle_bits;
  Module module;

  /* Assignment is a list of nodes, i.e. enumeration and range types.  The
   * first element of the first node on the list is taken as the assignment
   * for the first introduced oracle variable.  This allows us to reuse the
   * same determinization function for quantifying oracles out.  If the list
   * of types is empty then we really introduce a new oracle variable.
   */
  Node * assignment;
};

/*------------------------------------------------------------------------*/

static void add_oracle_decl(DtContext * context, Node * decl)
{
  unsigned bits;

  bits = num_bits(cdr(decl));

  context -> num_oracles++;
  context -> num_oracle_bits += bits;

  context -> module.var = cons(decl, context -> module.var);

  if(verbose >= 3)
    {
      fputs("-- [verbose]   new oracle: ", stderr);
      print(stderr, car(decl));
      fprintf(stderr, " (%u bits)\n", bits);
    }
}

/*------------------------------------------------------------------------*/

static int is_non_det(Node * node)
{
  int res;

  switch(node -> tag)
    {
      case ENUM:
      case TWODOTS:
      case UNION:
        res = 1;
	break;

      default:
        res = 0;
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static Node * dt(DtContext * context, Node * node);

/*------------------------------------------------------------------------*/
/* Avoid to introduce an oracle for `a = { 0, 1 }' etc.
 *
 * The last argument `swapped' is used to preserve the original order of
 * arguments as far as possible.
 */
static Node * dt_eq(DtContext * context, Node * lhs, Node * rhs, int swapped)
{
  Node * res, * tmp, * p, * a, * b;
  int l, r;

  if(!is_non_det(lhs) && is_non_det(rhs))
    {
      swapped ^= 1;
      tmp = lhs;
      lhs = rhs;
      rhs = tmp;
    }
  
  switch(lhs -> tag)
    {
      case ENUM:

        for(p = car(lhs), res = 0; p; p = cdr(p))
	  {
	    tmp = dt_eq(context, car(p), rhs, swapped);
	    res = res ? new(OR, res, tmp) : tmp;
	  }
	
	assert(res);
        break;
      
      case UNION:

        a = dt_eq(context, car(lhs), rhs, swapped);
        b = dt_eq(context, cdr(lhs), rhs, swapped);
	res = new(OR, a, b);
	break;

      case TWODOTS:

        range_bounds(lhs, &l, &r);

	tmp = number(l);
	if(swapped) tmp = new(GE, copy(rhs), tmp);
	else tmp = new(LE, tmp, copy(rhs));
	a = dt(context, tmp);
	delete(tmp);

	tmp = number(r);
	if(swapped) tmp = new(LE, copy(rhs), tmp);
	else tmp = new(GE, tmp, copy(rhs));
	b = dt(context, tmp);
	delete(tmp);

	res = new(AND, a, b);
        break;

      default:

	assert(!is_non_det(lhs));

	a = dt(context, swapped ? rhs : lhs);
	b = dt(context, swapped ? lhs : rhs);
	res = new(EQUAL, a, b);
        break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/
/* The next function relates to `gen_oracle_types' as `dt_eq' relates to
 * `dt'.
 */

static Node * gen_oracle_types(Node * node);

static Node * gen_oracle_types_eq(Node * lhs, Node * rhs)
{
  Node * tmp, * res, * a, * b;
  unsigned i, l;

  if(!is_non_det(lhs) && is_non_det(rhs))
    {
      tmp = lhs;
      lhs = rhs;
      rhs = tmp;
    }
  
  switch(lhs -> tag)
    {
      case ENUM:
        a = gen_oracle_types(rhs);
	for(i = 0, l = length(car(lhs)), res = 0; i < l; i++)
	  {
	    tmp = append(res, a);
	    delete(res);
	    res = tmp;
	  }
	delete(a);
	break;
      
      case UNION:
        a = gen_oracle_types_eq(car(lhs), rhs);
        b = gen_oracle_types_eq(cdr(lhs), rhs);
	res = append(a, b);
	delete(a);
	delete(b);
        break;

      case TWODOTS:
        a = gen_oracle_types(rhs);
	res = append(a, a);
	delete(a);
        break;
      
      default:
        a = gen_oracle_types(lhs);
        b = gen_oracle_types(rhs);
	res = append(a, b);
	delete(a);
	delete(b);
        break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/
/* Generate a list of types for oracles that would be introduced.  We have
 * to be careful to mimic the behaviour of `dt' and `dt_eq'.
 */
static Node * gen_oracle_types(Node * node)
{
  Node * res, * a, * b, * type;
  int tag;

  if(node)
    {
      switch((tag = node -> tag))
        {
	  case ATOM:
	  case NUMBER:
	  case BOOLEAN:
	    res = 0;
	    break;

	  case SETNOTIN:
	  case SETIN:
	  case EQUAL:
	    res = gen_oracle_types_eq(car(node), cdr(node));
	    break;

	  case ENUM:
	  case TWODOTS:
	  case UNION:
	    if(tag == UNION) type = new(ENUM, number(0), number(1));
	    else type = copy(node);
	    res = cons(type, 0);
	    break;
	  
	  default:
	    a = gen_oracle_types(car(node));
	    b = gen_oracle_types(cdr(node));
	    res = append(a, b);
	    delete(a);
	    delete(b);
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/
/* Compute the number of bits needed for representing the crosspoduct of
 * the types for the oracles with the given list of types.
 */
static unsigned compute_oracle_types_size(Node * oracle_types)
{
  unsigned res;
  Node * p;

  for(p = oracle_types, res = 0; p; p = cdr(p))
    res += num_bits(car(p));
  
  return res;
}

/*------------------------------------------------------------------------*/
/* The possible Assignments are enumerated as follows.  If the following
 * oracles would have been introduced
 *
 *  ORACLE0 : { one, two, three };
 *  ORACLE1 : boolean;
 *  ORACLE2 : -1..1;
 *
 * then the list of types is simply the RHS of theses declarations and the
 * enumerations of assignments, temporally stored in `context-> assignment'
 * is the following:
 *
 *   one, 0, -1
 *   one, 0, 0
 *   one, 0, 1
 *   one, 1, -1
 *   one, 1, 0
 *   one, 1, 1
 *   two, 0, -1
 *   two, 0, 0
 *   two, 0, 1
 *   two, 1, -1
 *   two, 1, 0
 *   two, 1, 1
 *   three, 0, -1
 *   three, 0, 0
 *   three, 0, 1
 *   three, 1, -1
 *   three, 1, 0
 *   three, 1, 1
 *
 * The function `init_Assignment' gets the list of types and generates the
 * first assignment of the enumeration.
 */
static Node * init_Assignment(Node * types)
{
  Node * res, * tmp, * first;

  if(types)
    {
      tmp = init_Assignment(cdr(types));
      first = get_first_type(car(types));
      res = cons(first, tmp);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/
/* This is a simple counter to enumerate all assignments.
 */
static Node * next_Assignment_aux(Node * old, Node * types, int * carry_out)
{
  Node * res, * p, * tmp, * next, * first, * type;
  int l, r, n, carry_in;
  
  assert(!old == !types);

  if(types)
    {
      tmp = next_Assignment_aux(cdr(old), cdr(types), &carry_in);

      if(carry_in)
        {
	  type = car(types);

	  if(car(types) -> tag == TWODOTS)
	    {
	      assert(car(old) -> tag == NUMBER);

	      n = (long) car(car(old));
	      range_bounds(type, &l, &r);

	      assert(l <= n);
	      assert(n <= r);

	      if(n == r)
	        {
		  res = cons(number(l), tmp);
		  *carry_out = 1;
		}
	      else
	        {
		  res = cons(number(n + 1), tmp);
		  *carry_out = 0;
		}
	    }
	  else
	    {
	      assert(type -> tag == ENUM);

	      /* search for position of `car(old)'
	       */
	      for(p = car(type); p && car(old) != car(p); p = cdr(p))
		;
	      
	      assert(p);

	      if(cdr(p))
		{
		  next = car(cdr(p));
		  res = cons(copy(next), tmp);
		  *carry_out = 0;
		}
	      else
		{
		  /* `car(old)' is last element of type.
		   */
		  first = car(car(type));
		  res = cons(copy(first), tmp);
		  *carry_out = 1;
		}
	    }
	}
      else 
        {
	  /* Keep old value.
	   */
	  res = cons(copy(car(old)), tmp);
	  *carry_out = 0;
	}
    }
  else
    {
      *carry_out = 1;
      res = 0;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/
/* Returns the next assignment.  For instance the next assignment after
 * `two, 1, 1' will be `three, 0, -1'.  The end of the enumeration is
 * flagged by a zero return value.
 */
static Node * next_Assignment(Node * old, Node * types)
{
  int carry_in;
  Node * res;

  assert(types);

  if(old)
    {
      res = next_Assignment_aux(old, types, &carry_in);
      if(carry_in) 
	{
	  delete(res);
	  res = 0;
	}
    }
  else res = init_Assignment(types);

  return res;
}

/*------------------------------------------------------------------------*/
/* Quantify oracles that would be introduced in `node'.
 */
static Node * dt_quantify(
  DtContext * context, Node * node, Node * oracle_types, Node * lhs)
{
# ifndef NDEBUG
  unsigned old_num_oracles = context -> num_oracles;
# endif

  Node * res, * tmp, * next, * old;

  res = 0;
  old = 0;

  while((next = next_Assignment(old, oracle_types)))
    {
      delete(old);
      context -> assignment = old = next;

      tmp = dt(context, node);
      if(lhs) tmp = new(EQUAL, copy(lhs), tmp);
      res = res ? new(OR, res, tmp) : tmp;

      assert(old_num_oracles == context -> num_oracles);
    }
  
  delete(old);
  
  return res;
}

/*------------------------------------------------------------------------*/
/* Unfortunately we have to traverse the tree and not the DAG.  For instance
 * if `{0, 1}' occurs in the same module twice then we still have to
 * introduce two oracles and can not share them.
 */
static Node * dt(DtContext * context, Node * node)
{
  Node * res, * a, * b, * oracle, * tmp, * decl, ** ptr, * oracle_types;
  unsigned oracle_types_size;
  int tag;

  if(node)
    {
      switch((tag = node -> tag))
	{
	  case ATOM:
	  case NUMBER:
	  case BOOLEAN:
	    res = copy(node);
	    break;

	  case TWODOTS:
	  case ENUM:

	    if(context -> assignment)
	      {
		/* Use the value of the quantification assignment instead of
		 * introducing an oracle.
		 */
	        res = copy(car(context -> assignment));

		/* Pop this used value.
		 */
		context -> assignment = cdr(context -> assignment);
	      }
	    else
	      {
		oracle = new_oracle();
		decl = new(DECL, oracle, normalize_type(node));
		add_oracle_decl(context, decl);
		res = copy(oracle);
	      }
	    break;

	  case UNION:

	    if(context -> assignment) res = copy(car(context -> assignment));
	    else
	      {
		oracle = new_oracle();
		decl = new(DECL, oracle, new(BOOLEAN,0,0));
		add_oracle_decl(context, decl);
		a = dt(context, car(node));
		b = dt(context, cdr(node));
		res = ite(copy(oracle), a, b);
	      }
	    break;
	  
	  case NEXT:
	    if(!context -> max_next) 
	      {
	        fprintf(stderr,
		  "*** smvflatten: nested or unexpected `next'\n");
		exit(1);
	      }
	    context -> max_next--;
	    a = dt(context, car(node));
	    res = new(NEXT, a, 0);
	    context -> max_next++;
	    break;

	  case DEFINEASSIGNMENT:
	  case INVARASSIGNMENT:
	  case INITASSIGNMENT:
	  case TRANSASSIGNMENT:
	    context -> max_next = 
	      (tag == TRANSASSIGNMENT || tag == DEFINEASSIGNMENT);
	    oracle_types = gen_oracle_types(cdr(node));
	    oracle_types_size = compute_oracle_types_size(oracle_types);
	    if(oracle_types_size &&
	       oracle_types_size <= max_size_quantified_oracle)
	      {
		a = copy(car(node));
		if(node -> tag == TRANSASSIGNMENT) a = new(NEXT, a, 0);
	        tmp = dt_quantify(context, cdr(node), oracle_types, a);
		delete(a);

		switch(node -> tag)
		  {
		    case DEFINEASSIGNMENT:
		    case INVARASSIGNMENT:
		      ptr = &context -> module.invar;
		      break;
		    
		    case INITASSIGNMENT:
		      ptr = &context -> module.init;
		      break;
		    
		    case TRANSASSIGNMENT:
		      ptr = &context -> module.trans;
		      break;
		    
		    default:
		      ptr = 0;
		      assert(0);
		  }
		
		*ptr = *ptr ? new(AND, *ptr, tmp) : tmp;
		res = 0;
	      }
	    else
	      {
		a = dt(context, cdr(node));
		context -> max_next = 0;
		tmp = new(tag, copy(car(node)), a);
		ptr = section_Module(&context -> module, node);
		*ptr = cons(tmp, *ptr);
	      }
	    delete(oracle_types);
	    res = 0;
	    break;

	  case SETNOTIN:
	    res = dt_eq(context, car(node), cdr(node), 0);
	    res = new(NOT, res, 0);
	    break;

	  case SETIN:
	  case EQUAL:
	    res = dt_eq(context, car(node), cdr(node), 0);
	    break;

	  case DECL:
	    context -> module.var = cons(copy(node), context -> module.var);
	    res = 0;
	    break;
	  
	  default:
	    a = dt(context, car(node));
	    b = dt(context, cdr(node));
	    res = new(node -> tag, a, b);
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static void dt_sections(DtContext * context, Node * node)
{
  Node * p, * tmp, * oracle_types, ** ptr;
  unsigned oracle_types_size;
  int tag;

  if(node)
    {
      context -> max_next = 0;

      switch((tag = node -> tag))
        {
	  case MODULE:
	    for(p = cdr(node); p; p = cdr(p)) dt_sections(context, car(p));
	    break;

	  case DEFINE:
	  case ASSIGN:
	  case VAR:
	    for(p = car(node); p; p = cdr(p)) (void) dt(context, car(p));
	    break;
	  
	  case INIT:
	  case INVAR:
	  case TRANS:
	    oracle_types = gen_oracle_types(car(node));
	    oracle_types_size = compute_oracle_types_size(oracle_types);

	    context -> max_next = (tag == TRANS);
	    if(oracle_types_size &&
	       oracle_types_size <= max_size_quantified_oracle)
	      {
		tmp = dt_quantify(context, car(node), oracle_types, 0);
	      }
	    else tmp = dt(context, car(node));
	    context -> max_next = 0;

	    ptr = section_Module(&context -> module, node);
	    *ptr = *ptr ? new(AND, tmp, *ptr) : tmp;
	    delete(oracle_types);
	    break;

	  case FAIRNESS:
	  case SPEC:
	  case COMPUTE:
	    ptr = section_Module(&context -> module, node);
	    tmp = dt(context, car(node));
	    *ptr = cons(tmp, *ptr);
	    break;
	  
	  default:
	    assert(0);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void init_DtContext(DtContext * context)
{
  context -> num_oracles = 0;
  context -> num_oracle_bits = 0;
  context -> assignment = 0;
  init_Module(&context -> module);
}

/*------------------------------------------------------------------------*/

static void release_DtContext(DtContext * context)
{
  release_Module(&context -> module);
}

/*------------------------------------------------------------------------*/

Node * determinize(Node * node)
{
  DtContext context;
  Node * res;

  assert(node -> tag == MODULE);

  if(verbose) fprintf(stderr, "-- [verbose] phase 2: determinization ...\n");

  init_DtContext(&context);
  dt_sections(&context, node);
  res = merge_Module(&context.module);

  if(verbose) 
    fprintf(stderr,
      "-- [verbose] end of phase 2: generated %u oracles (%u bits)\n",
      context.num_oracles,
      context.num_oracle_bits);

  release_DtContext(&context);

  return res;
}

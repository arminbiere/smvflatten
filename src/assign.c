/*------------------------------------------------------------------------*/
/* Copyright Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assign.h"
#include "assoc.h"
#include "module.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>

/*------------------------------------------------------------------------*/

extern int verbose;

/*------------------------------------------------------------------------*/

typedef struct ExAssignmentsContext ExAssignmentsContext;

struct ExAssignmentsContext
{
  Assoc * variables;
  Assoc * init_assignments;
  Assoc * trans_assignments;
  Assoc * definitions;
  Assoc * invar_assignments;

  Module module;

  unsigned num_extracted_init_assignments;
  unsigned num_extracted_trans_assignments;
};

/*------------------------------------------------------------------------*/

static void init_assignments(ExAssignmentsContext * context, Node * node)
{
  if(node)
    {
      switch(node -> tag)
        {
	  case MODULE:
	    init_assignments(context, cdr(node));
	    break;

	  case DEFINE:
	  case ASSIGN:
	  case VAR:
	    init_assignments(context, car(node));
	    break;
	  
	  case DECL:
	    associate(context -> variables, car(node), cdr(node));
	    break;

	  case DEFINEASSIGNMENT:
	    associate(context -> definitions, car(node), cdr(node));
	    break;

	  case INVARASSIGNMENT:
	    associate(context -> invar_assignments, car(node), cdr(node));
	    break;

	  case INITASSIGNMENT:
	    associate(context -> init_assignments, car(node), cdr(node));
	    break;

	  case TRANSASSIGNMENT:
	    associate(context -> trans_assignments, car(node), cdr(node));
	    break;
	  
	  case INIT:
	  case INVAR:
	  case TRANS:
	  case SPEC:
	  case FAIRNESS:
	  case COMPUTE:
	    break;

	  case LIST:
	    init_assignments(context, car(node));
	    init_assignments(context, cdr(node));
	    break;

	  default:
	    assert(0);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void init_ExAssignmentsContext(
  ExAssignmentsContext * context, Node * node)
{
  context -> num_extracted_init_assignments = 0;
  context -> num_extracted_trans_assignments = 0;

  context -> variables = new_Assoc();
  context -> init_assignments = new_Assoc();
  context -> trans_assignments = new_Assoc();
  context -> definitions = new_Assoc();
  context -> invar_assignments = new_Assoc();

  init_assignments(context, node);

  init_Module(&context -> module);
}

/*------------------------------------------------------------------------*/

static void release_ExAssignmentsContext(ExAssignmentsContext * context)
{
  if(verbose >= 2)
    {
      fprintf(
        stderr,
	"-- [verbose]   extracted %u init assignments\n",
	context -> num_extracted_init_assignments);

      fprintf(
        stderr,
	"-- [verbose]   extracted %u trans assignments\n",
	context -> num_extracted_trans_assignments);
    }

  release_Module(&context -> module);

  delete_Assoc(context -> variables);
  delete_Assoc(context -> init_assignments);
  delete_Assoc(context -> trans_assignments);
  delete_Assoc(context -> invar_assignments);
  delete_Assoc(context -> definitions);
}

/*------------------------------------------------------------------------*/

static int is_permanently_assigned(ExAssignmentsContext * context, Node * var)
{
  return 
    is_associated(context -> definitions, var) ||	/* may be omitted */
    is_associated(context -> invar_assignments, var);
}

/*------------------------------------------------------------------------*/

static int can_be_initialized(ExAssignmentsContext * context, Node * var)
{
  int res;

  if(is_associated(context -> variables, var))
    {
      res = 
        !is_permanently_assigned(context, var) &&
        !is_associated(context -> init_assignments, var);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static void ea_and_section(Node ** section_ptr, Node * node)
{
  if(*section_ptr)
    {
      *section_ptr = new_simplify(AND, *section_ptr, node);
    }
  else *section_ptr = node;
}

/*------------------------------------------------------------------------*/

static Node * ea_init(ExAssignmentsContext * context, Node * node)
{
  Node * a, * b, * res, * var, * lhs, * rhs, * assignment;

  if(node -> tag == AND)
    {
      a = ea_init(context, car(node));
      b = ea_init(context, cdr(node));
      res = new_simplify(AND, a, b);
    }
  else
  if(is_literal(node))
    {
      if(node -> tag == NOT) var = car(node);
      else var = node;

      assert(is_atom(var));

      if(can_be_initialized(context, var))
        {
	  if(verbose >= 2)
	    {
	      fputs(
	        "-- [verbose]   init(",
	        stderr);
	      print(stderr, var);
	      fputs(") := ...\n", stderr);
	    }

	  lhs = copy(var);
	  rhs = number(node -> tag != NOT);
	  assignment = new(INITASSIGNMENT, lhs, rhs);
	  context -> module.assign =
	    cons(assignment, context -> module.assign);
	  context -> num_extracted_init_assignments++;
	  res = number(1);
	}
      else res = copy(node);
    }
  else res = copy(node);

  return res;
}

/*------------------------------------------------------------------------*/

static int may_have_trans_assignment(
  ExAssignmentsContext * context, Node * var)
{
  int res;

  assert(is_atom(var));

  if(is_associated(context -> variables, var))
    {
      res =
        !is_permanently_assigned(context, var) &&
	!is_associated(context -> trans_assignments, var);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * ea_trans(ExAssignmentsContext * context, Node * node)
{
  Node * res, * lhs, * rhs, * u, * v, * var, * value, * assignment;
  Node * a, * b;

  switch(node -> tag)
    {
      case AND:
	a = ea_trans(context, car(node));
	b = ea_trans(context, cdr(node));
	res = new_simplify(AND, a, b);
	break;
      
      case IFF:
        lhs = car(node);
	rhs = cdr(node);
	u = (lhs -> tag == NEXT) ? car(lhs) : (Node*) 0;
	v = (rhs -> tag == NEXT) ? car(rhs) : (Node*) 0;
	assert(!u || is_atom(u));
	assert(!v || is_atom(v));
	if(u && 
	   !rhs -> contains_next &&
	   may_have_trans_assignment(context, u))
	  {
	    var = u;
	    value = rhs;
	  }
	else
	if(v &&
	   !lhs -> contains_next &&
	   may_have_trans_assignment(context, v))
	  {
	    var = v;
	    value = lhs;
	  }
	else
	  {
	    var = 0;
	    value = 0;
	  }

	assert(!value == !var);

	if(var)
	  {
	    assignment = new(TRANSASSIGNMENT, copy(var), copy(value));
	    context -> module.assign =
	      cons(assignment, context -> module.assign);

	    if(verbose >= 3)
	      {
		fputs(
		  "-- [verbose]   next(",
		  stderr);
		print(stderr, var);
		fputs(") := ...\n", stderr);
	      }
	    
	    context -> num_extracted_trans_assignments++;
	    res = number(1);
	  }
	else res = copy(node);
        break;
      
      /* TODO: case NEXT: */
      /* TODO: case NOT: */
      
      default:
	res = copy(node);
	break;
    }

  /* TODO: if(!res -> contains_next) "move to INVAR" */

  return res;
}

/*------------------------------------------------------------------------*/

static void ea(ExAssignmentsContext * context, Node * node)
{
  Node * tmp, ** ptr, * p;
  Module * m;

  if(node)
    {
      m = &context -> module;
      switch(node -> tag)
        {
	  case MODULE:
	    ea(context, cdr(node));
	    break;
	  
	  case DEFINE:
	  case VAR:
	  case ASSIGN:
	    ptr = section_Module(m, node);
	    for(p = car(node); p; p = cdr(p)) *ptr = cons(copy(car(p)), *ptr);
	    break;

	  case COMPUTE:
	  case FAIRNESS:
	  case SPEC:
	    ptr = section_Module(m, node);
	    *ptr = cons(copy(car(node)), *ptr);
	    break;

	  case INVAR:
	    ea_and_section(&m -> invar, copy(car(node)));
	    break;

	  case INIT:
	    tmp = ea_init(context, car(node));
	    if(is_true(tmp)) delete(tmp);
	    else ea_and_section(&m -> init, tmp);
	    break;
	  
	  case TRANS:
	    tmp = ea_trans(context, car(node));
	    if(is_true(tmp)) delete(tmp);
	    else ea_and_section(&m -> trans, tmp);
	    break;
	  
	  case LIST:
	    ea(context, car(node));
	    ea(context, cdr(node));
	    break;

	  default:
	    assert(0);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

Node * extract_assignments(Node * node)
{
  ExAssignmentsContext context;
  Node * res;

  if(verbose)
    fputs("-- [verbose] phase 5: extracting assignments ...\n", stderr);

  init_ExAssignmentsContext(&context, node);
  ea(&context, node);
  res = merge_Module(&context.module);
  release_ExAssignmentsContext(&context);

  if(verbose)
    fputs("-- [verbose] end of phase 5: assignments extracted.\n", stderr);

  return res;
}

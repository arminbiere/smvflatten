/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"
#include "node.h"
#include "module.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/

static Node * add_reverse(int tag, Node * section, Node * sections)
{
  Node * res, * tmp;

  if(section)
    {
      tmp = new(tag, reverse(section), 0);
      res = new(LIST, tmp, sections);
    }
  else res = sections;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * unique_trans_assignments(Node * section, Assoc * trans_assigns)
{
  Node * res, * tmp, * assignment, * lhs;
  int add_head;
  
  if(section)
    {
      assignment = car(section);
      add_head = 1;

      if(assignment -> tag == TRANSASSIGNMENT)
	{
	  lhs = car(assignment);

	  if(is_associated(trans_assigns, lhs)) add_head = 0;
	  else associate(trans_assigns, lhs, (void*) 1);
	}

      tmp = unique_trans_assignments(cdr(section), trans_assigns);

      if(add_head) res = new(LIST, copy(assignment), tmp);
      else res = tmp;
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * add_assign_section(Node * section, Node * sections)
{
  Assoc * trans_assigns;
  Node * res, * tmp;

  if(section)
    {
      trans_assigns = new_Assoc();
      tmp = unique_trans_assignments(section, trans_assigns);
      res = new(LIST, new(ASSIGN, reverse(tmp), 0), sections);
      delete(tmp);
      delete_Assoc(trans_assigns);
    }
  else res = sections;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * add_sections(int tag, Node * section, Node * sections)
{
  Node * res, * tmp;

  if(section)
    {
      tmp = new(LIST, new(tag, copy(car(section)), 0), sections);
      res = add_sections(tag, cdr(section), tmp);
    }
  else res = sections;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * add_section(int tag, Node * section, Node * old)
{
  Node * res;

  if(section) res = new(LIST, new(tag, copy(section), 0), old);
  else res = old;

  return res;
}

/*------------------------------------------------------------------------*/


Node * merge_Module(Module * module)
{
  Node * res;

  res = 0;

  /* Do not change the order unless you change the insertion of the
   * additional INVAR sections in `enc' as well.
   */
  res = add_sections(COMPUTE, module -> compute, res);
  res = add_sections(SPEC, module -> spec, res);
  res = add_sections(FAIRNESS, module -> fairness, res);
  res = add_section(TRANS, module -> trans, res);
  res = add_section(INVAR, module -> invar, res);
  res = add_section(INIT, module -> init, res);
  res = add_assign_section(module -> assign, res);
  res = add_reverse(DEFINE, module -> define, res);
  res = add_reverse(VAR, module -> var, res);

  /* Finally add the module declaration.
   */
  res = new(MODULE, cons(atom("main"), 0), res);

  return res;
}

/*------------------------------------------------------------------------*/

void init_Module(Module * module)
{
  module -> var = 0;
  module -> define = 0;
  module -> assign = 0;
  module -> invar = 0;
  module -> init = 0;
  module -> trans = 0;
  module -> fairness = 0;
  module -> spec = 0;
  module -> compute = 0;
}

/*------------------------------------------------------------------------*/

void release_Module(Module * module)
{
  delete(module -> compute);
  delete(module -> spec);
  delete(module -> fairness);
  delete(module -> trans);
  delete(module -> init);
  delete(module -> invar);
  delete(module -> assign);
  delete(module -> define);
  delete(module -> var);
}

/*------------------------------------------------------------------------*/

Node ** section_Module(Module * module, Node * node)
{
  Node ** res;

  switch(node -> tag)
    {
      case COMPUTE: res = &module -> compute; break;
      case SPEC: res = &module -> spec; break;
      case FAIRNESS: res = &module -> fairness; break;
      case TRANS: res = &module -> trans; break;
      case INIT: res = &module -> init; break;
      case INVAR: res = &module -> invar; break;
      case INITASSIGNMENT:
      case INVARASSIGNMENT:
      case TRANSASSIGNMENT:
      case ASSIGN: res = &module -> assign; break;
      case DEFINEASSIGNMENT:
      case DEFINE: res = &module -> define; break;
      case DECL:
      case VAR: res = &module -> var; break;
      default: res = 0; break;
    }
  
  return res;
}

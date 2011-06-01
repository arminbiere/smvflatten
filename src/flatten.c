/*------------------------------------------------------------------------*/
/* Copyright 1999-2011 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"
#include "cache.h"
#include "flatten.h"
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

/*------------------------------------------------------------------------*/

typedef struct Context Context;
typedef struct Result Result;

/*------------------------------------------------------------------------*/

#define MARKED 1
#define IS_ON_STACK 2

/*------------------------------------------------------------------------*/

struct Result
{
  Assoc * modules, * used_modules;
  Node * running, * self, * processes;

  Module module;

  Assoc * invar_assignments;
  Assoc * init_assignments;
  Assoc * trans_assignments;
  Assoc * define_assignments;

  Assoc * parameters;
  Assoc * constants;
  Assoc * variables;
};

/*------------------------------------------------------------------------*/

struct Context
{
  Result * result;
  Node * access, * variable, * module, * process;
};

/*------------------------------------------------------------------------*/

static void add_constant(Node * node, Result * res)
{
  if(!is_associated(res -> constants, node))
    {
      if(verbose >= 3)
	{
	  fputs("-- [verbose]     found constant `", stderr);
	  print(stderr, node);
	  fputs("'\n", stderr);
	}

      associate(res -> constants, node, (void*) 1);
    }
}

/*------------------------------------------------------------------------*/

static void gen_constants(Node * node, Result * res)
{
  if(node)
    {
      switch(node -> tag)
        {
	  case INIT:
	  case INVAR:
	  case TRANS:
	  case FAIRNESS:
	  case SPEC:
	  case LTLSPEC:
	  case COMPUTE:
	  case ASSIGN:
	  case DEFINE:
	  case BOOLEAN:
	  case TWODOTS:
	  case INSTANCE:
	  case NUMBER:
	  case ISA:
	    break;
	  
	  case ARRAY:
	  case DECL:
	  case MODULE:
	    gen_constants(cdr(node), res);
	    break;

	  case ATOM:
	    add_constant(node, res);
	    break;
	  
	  default:				/* includes ENUM */
	    gen_constants(car(node), res);
	    gen_constants(cdr(node), res);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void gp(Assoc * modules, Node * node, Node * context, Node ** res_ptr)
{
  Node * module, * name, * tmp, * inner;
  int i, l, r, tag;

  if(node)
    {
      switch((tag = node -> tag))
        {
	  case NUMBER:
	  case TWODOTS:
	  case ENUM:
	  case ATOM:
	  case BOOLEAN:
	    break;

	  case ASSIGN:
	  case DEFINE:
	  case FAIRNESS:
	  case INIT:
	  case INVAR:
	  case SPEC:
	  case LTLSPEC:
	  case COMPUTE:
	  case TRANS:
	    break;

	  case ARRAY:

	    l = (long)car(car(car(node)));
	    r = (long)car(cdr(car(node)));
	    assert(l <= r);

	    for(i = l; i <= r; i++)
	      {
		tmp = number(i);
	        inner = append_tagged(ACCESS, context, tmp);
		delete(tmp);
		gp(modules, cdr(node), inner, res_ptr);
		delete(inner);
	      }

	    break;

	  case DECL:
	    
	    inner = append_tagged(ACCESS, context, car(node));
	    gp(modules, cdr(node), inner, res_ptr);
	    delete(inner);
	    break;
	  
	  case INSTANCE:
	  case ISA:

	    if(tag == ISA) name = car(node);
	    else name = car(car(node));

	    module = get_association(modules, name);

	    if(!module)
	      {
	        fputs("*** smvflatten: module `", stderr);
		print(stderr, name);
		fputs("' undefined\n", stderr);
		exit(1);
	      }

	    gp(modules, module, context, res_ptr);
	    break;
	  
	  case PROCESS:

	    if(verbose >= 3)
	      {
	        fputs("-- [verbose]     found process `", stderr);
		print(stderr, context);
		fputs("'\n", stderr);
	      }
	    
	    *res_ptr = cons(copy(context), *res_ptr);
	    gp(modules, car(node), context, res_ptr);
	    break;

	  case VAR:
	  case MODULE:
	  default:
	    gp(modules, car(node), context, res_ptr);
	    gp(modules, cdr(node), context, res_ptr);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void check_non_recursive_modules(
  Assoc * modules, Node * node, Assoc * cache)
{
  Node * name, * module;
  unsigned mark;
  int tag;

  if(node)
    {
      switch((tag = node -> tag))
        {
	  case BOOLEAN:
	  case ENUM:
	  case TWODOTS:
	  case INVAR:
	  case INIT:
	  case TRANS:
	  case FAIRNESS:
	  case SPEC:
	  case LTLSPEC:
	  case COMPUTE:
	  case DEFINE:
	  case ASSIGN:
	    break;

	  case ISA:
	  case INSTANCE:

	    if(tag == INSTANCE) name = car(car(node));
	    else name = car(node);

	    mark = (long)get_association(cache, name);
	    if(mark & IS_ON_STACK)
	      {
	        fputs("*** smvflatten: module `", stderr);
		print(stderr, name);
		fputs("' is defined recursively\n", stderr);
		exit(1);
	      }

	    if(!mark)
	      {
		module = get_association(modules, name);
		associate(cache, name, (void*)(MARKED | IS_ON_STACK));
		check_non_recursive_modules(modules, module, cache);
		associate(cache, name, (void*)MARKED);
	      }
	    break;

	  case DECL:
	  case MODULE:
	    check_non_recursive_modules(modules, cdr(node), cache);
	    break;

	  default:
	    check_non_recursive_modules(modules, car(node), cache);
	    check_non_recursive_modules(modules, cdr(node), cache);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static Assoc * gen_modules(Node * node)
{
  Node * p, * module, * module_atom;
  Assoc * res, * cache;
 
  res = new_Assoc();
 
  for(p = node; p; p = cdr(p))
    {
      assert(p -> tag == LIST);
      module = car(p);
      assert(module -> tag == MODULE);
      module_atom = car(car(module));
      assert(module_atom -> tag == ATOM);
      if(is_associated(res, module_atom))
        {
          fputs("*** smvflatten: module `", stderr);
          print(stderr, module_atom);
          fputs("' defined twice\n", stderr);
          exit(1);
        }
      else associate(res, module_atom, module);
    }

  cache = new_Assoc();
  check_non_recursive_modules(res, node, cache);
  delete_Assoc(cache);

  if(verbose >= 2)
    fprintf(stderr, "-- [verbose]   found %u modules\n", count_Assoc(res));

  return res;
}

/*------------------------------------------------------------------------*/

static Node * gen_processes(Assoc * modules, Node * main_module)
{
  Node * res, * tmp;

  tmp = cons(atom("main"), 0);
  gp(modules, main_module, 0, &tmp);
  res = reverse(tmp);
  delete(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * init_Result(Result * result, Node * node)
{
  Node * main_atom, * main_module, * decl, * type, * tmp, * p;

  result -> modules = gen_modules(node);
  result -> used_modules = new_Assoc();

  main_atom = atom("main");
  main_module = get_association(result -> modules, main_atom);
  if(!main_module)
    {
      fprintf( stderr, "*** smvflatten: no `main' module found\n");
      exit(1);
    }
  
  associate(result -> used_modules, main_module, main_module);

  result -> processes = gen_processes(result -> modules, main_module);

  if(verbose >= 2)
    fprintf(stderr,
      "-- [verbose]   found %u processes\n",
      length(result -> processes));

  result -> running = new(ATOM, (Node*) "running", 0);
  result -> self = new(ATOM, (Node*) "self", 0);

  init_Module(&result -> module);

  if(cdr(result -> processes))
    {
      tmp = new(ENUM, copy(result -> processes), 0);
      type = normalize_type(tmp);
      delete(tmp);
      decl = new(DECL, copy(result -> running), type);
      result -> module.var = new(LIST, decl, 0);
    }

  result -> invar_assignments = new_Assoc();
  result -> init_assignments = new_Assoc();
  result -> trans_assignments = new_Assoc();
  result -> define_assignments = new_Assoc();

  result -> constants = new_Assoc();
  gen_constants(node, result);
  for(p = result -> processes; p; p = cdr(p))
    add_constant(car(p), result);

  if(verbose >= 2)
    fprintf(stderr,
      "-- [verbose]   found %u constants\n",
      count_Assoc(result -> constants));

  result -> parameters = new_Assoc();
  result -> variables = new_Assoc();

  return main_atom;
}

/*------------------------------------------------------------------------*/

static void release_Result(Result * result)
{
  unsigned num_modules, num_used_modules;

  delete_Assoc(result -> define_assignments);
  delete_Assoc(result -> trans_assignments);
  delete_Assoc(result -> init_assignments);
  delete_Assoc(result -> invar_assignments);
  delete_Assoc(result -> variables);
  delete_Assoc(result -> constants);

  delete(result -> self);
  delete(result -> running);
  delete(result -> processes);

  forall_src_in_Assoc(result -> parameters, (void(*)(void*)) delete);
  forall_dst_in_Assoc(result -> parameters, (void(*)(void*)) delete);
  delete_Assoc(result -> parameters);

  release_Module(&result -> module);

  if(verbose >= 2)
    {
      num_modules = count_Assoc(result -> modules);
      num_used_modules = count_Assoc(result -> used_modules);

      assert(num_modules >= num_used_modules);

      fputs("-- [verbose]   ", stderr);

      if(num_modules > num_used_modules)
        {
	  fprintf(
	    stderr, 
	    "used %u modules (%u unused)\n",
	    num_used_modules,
	    num_modules - num_used_modules);
	}
      else fprintf(stderr, "used all %u modules\n", num_modules);
    }

  delete_Assoc(result -> modules);
  delete_Assoc(result -> used_modules);
}

/*------------------------------------------------------------------------*/

static void init_Context(Context * context, Result * result, Node * module)
{
  context -> result = result;
  context -> access = 0;
  context -> variable = 0;
  context -> module = module;
  context -> process = atom("main");
}

/*------------------------------------------------------------------------*/

static void push_Variable(Context * outer, Context * inner, Node * var)
{
  assert(!outer -> variable);
  assert(var -> tag == ATOM || var -> tag == ACCESS || var -> tag == NUMBER);

  inner -> result = outer -> result;
  inner -> access = copy(outer -> access);
  inner -> variable = append_tagged(ACCESS, outer -> access, var);
  inner -> process = copy(outer -> process);
}

/*------------------------------------------------------------------------*/

static void push_Access(Context * outer, Context * inner, Node * access)
{
  assert(outer -> variable);

  inner -> result = outer -> result;
  inner -> access = copy(outer -> access);
  inner -> variable = append_tagged(ACCESS, outer -> variable, access);
  inner -> process = copy(outer -> process);
}

/*------------------------------------------------------------------------*/

static void push_Context(
  unsigned is_process, Context * outer, Context * inner, Node * module)
{
  assert(outer -> variable);

  inner -> result = outer -> result;
  inner -> access = copy(outer -> variable);
  inner -> variable = 0;
  inner -> module = module;

  if(is_process) inner -> process = copy(outer -> variable);
  else inner -> process = copy(outer -> process);
}

/*------------------------------------------------------------------------*/

static void release_Context(Context * context)
{
  delete(context -> access);
  delete(context -> variable);
  delete(context -> process);

  context -> access = 0;
  context -> variable = 0;
  context -> process = 0;
}

/*------------------------------------------------------------------------*/

static Node * get_suffix(Node * node, int k)
{
  Node * res, * p;
  int l, i;

  if(k)
    {
      l = length(node);
      assert(k <= l);

      for(i = 0, p = node; i < l - k && p; i++, p = cdr(p))
        ;
      
      assert(p);

      if(p -> tag == ACCESS && !cdr(p)) res = copy(car(p));
      else res = copy(p);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * get_prefix_recursive(Node * node, int k)
{
  Node * res, * tmp;

  if(node)
    {
      if(node -> tag == ACCESS)
	{
	  if(k)
	    {
	      tmp = get_prefix_recursive(cdr(node), k - 1);
	      assert(!tmp || tmp -> tag == ACCESS);
	      res = new(ACCESS, copy(car(node)), tmp);
	    }
	  else res = 0;
	}
      else
	{
	  assert(k == 1);
	  assert(node -> tag == NUMBER || node -> tag == ATOM);

	  res = copy(node);
	}
    }
  else
    {
      assert(!k);
      res = 0;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static Node * get_prefix(Node * node, int k)
{
  Node * res, * tmp;

  tmp = get_prefix_recursive(node, k);
  if(tmp -> tag == ACCESS && !cdr(tmp)) res = copy(car(tmp));
  else res = copy(tmp);

  delete(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

static int find_prefix_aux(Assoc * container, Node * node, Node ** match)
{
  int i, l, res;
  Node * tmp;

  l = length(node);

  for(i = l, res = 0; !res && i; i--)
    {
      tmp = get_prefix(node, i);
      if(is_associated(container, tmp))
        {
	  assert(tmp -> ref > 1);
	  *match = tmp;
	  res = 1;
	}
      delete(tmp);
    }

  return res;
}

/*------------------------------------------------------------------------*/

static int find_prefix(
  Result * result, Node * node, Node ** match, Assoc ** container)
{
  int res;

  res = 1;

  if(find_prefix_aux(result -> variables, node, match))
    {
      *container = result -> variables;
    }
  else
  if(find_prefix_aux(result -> define_assignments, node, match))
    {
      *container = result -> define_assignments;
    }
  else
  if(is_associated(result -> parameters, node))
    {
      *match = node;
      *container = result -> parameters;
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static void check_prefix(Result * result, Node * node)
{
  Node * match, * tmp;
  Assoc * container;

  tmp = get_suffix(node, 1);
  assert(tmp);

  if(is_associated(result -> constants, tmp) ||
     find_prefix(result, node, &match, &container))
    {
      fputs("*** smvflatten: `", stderr);
      print(stderr, node);
      fputs("' is ambiguous\n", stderr);
      exit(1);
    }

  delete(tmp);
}

/*------------------------------------------------------------------------*/

static void add_variable(Context * context, Node * type)
{
  Node * var, * decl;
  Result * result;

  result = context -> result;

  assert(context -> variable);
  check_prefix(result, context -> variable);

  var = copy(context -> variable);
  decl = new(DECL, var, copy(type));
  result -> module.var = cons(decl, result -> module.var);
  
  associate(result -> variables, var, (void*) 1);

  if(verbose >= 3)
    {
      fputs("-- [verbose]     declaring `", stderr);
      print(stderr, var);
      fputs("'\n", stderr);
    }
}

/*------------------------------------------------------------------------*/

static Node * ft(Context * context, Node * node, unsigned);
static void ft_sections(Context * context, Node * node);

/*------------------------------------------------------------------------*/

static void add2trans(Context * context, Node * node)
{
  Result * result;

# if 0
  /* Old CMU-SMV and also early versions of NuSMV allow a combination of
   * TRANS sections with the process keyword.  As I understood the
   * semantics, the TRANS section is just added to the global transition
   * relation as an additional restriction.
   *
   * TODO: check if this assumption is correct.
   */
  if(cdr(context -> processes))
    {
      fputs(
	"*** smvflatten: combination of `TRANS' and `process'\n",
	stderr);
      exit(1);
    }
# endif
  
  result = context -> result;

  if(result -> module.trans)
    {
      result -> module.trans = new(AND, result -> module.trans, node);
    }
  else result -> module.trans = node;
}

/*------------------------------------------------------------------------*/

static void add_definition(Context * context, Node * lhs, Node * rhs)
{
  Node * definition;
  Result * result;

  result = context -> result;

  check_prefix(result, lhs);

  associate(result -> define_assignments, lhs, rhs);

  definition = new(DEFINEASSIGNMENT, lhs, rhs);
  result -> module.define = cons(definition, result -> module.define);

  if(verbose >= 3)
    {
      fputs("-- [verbose]     defining `", stderr);
      print(stderr, lhs);
      fputs("'\n", stderr);
    }
}

/*------------------------------------------------------------------------*/

static void add_parameter(Result * result, Node * lhs, Node * rhs)
{
  check_prefix(result, lhs);
  associate(result -> parameters, lhs, rhs);
}

/*------------------------------------------------------------------------*/

static void add_invar_assignment(Context * context, Node * lhs, Node * rhs)
{
  Node * assignment, * match;
  Result * result;

  result = context -> result;

  if(find_prefix_aux(result -> invar_assignments, lhs, &match) ||
     find_prefix_aux(result -> init_assignments, lhs, &match) ||
     find_prefix_aux(result -> trans_assignments, lhs, &match) ||
     find_prefix_aux(result -> define_assignments, lhs, &match))
    {
      fputs("*** smvflatten: invalid invar assignment of `", stderr);
      print(stderr, lhs);
      fputs("'\n", stderr);
      exit(1);
    }

  associate(result -> invar_assignments, lhs, rhs);

  assignment = new(INVARASSIGNMENT, lhs, rhs);
  result -> module.assign = new(LIST, assignment, result -> module.assign);
}

/*------------------------------------------------------------------------*/

static void add_init_assignment(Result * result, Node * lhs, Node * rhs)
{
  Node * assignment, * match;

  if(find_prefix_aux(result -> invar_assignments, lhs, &match) ||
     find_prefix_aux(result -> init_assignments, lhs, &match) ||
     find_prefix_aux(result -> define_assignments, lhs, &match))
    {
      fputs("*** smvflatten: invalid init assignment of `", stderr);
      print(stderr, lhs);
      fputs("'\n", stderr);
      exit(1);
    }

  assignment = new(INITASSIGNMENT, lhs, rhs);
  associate(result -> init_assignments, lhs, rhs);
  result -> module.assign = new(LIST, assignment, result -> module.assign);
}

/*------------------------------------------------------------------------*/

static int more_than_one_process(Context * context)
{
  int res;

  assert(context -> result -> processes);
  res = (cdr(context -> result -> processes) != 0);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * synchronize(Context * context)
{
  Node * res, * l, * r;

  assert(more_than_one_process(context));

  l = copy(context -> result -> running);
  r = copy(context -> process);
  res = new(EQUAL, l, r);

  return res;
}

/*------------------------------------------------------------------------*/

static void add_trans_assignment(Context * context, Node * lhs, Node * rhs)
{
  Node * assignment, * match, * new_rhs, * old_rhs;
  Result * result;

  result = context -> result;

  if(find_prefix_aux(result -> invar_assignments, lhs, &match) ||
     (!more_than_one_process(context) &&
       find_prefix_aux(result -> trans_assignments, lhs, &match)) ||
     find_prefix_aux(result -> define_assignments, lhs, &match))
    {
      fputs("*** smvflatten: invalid trans assignment of `", stderr);
      print(stderr, lhs);
      fputs("'\n", stderr);
      exit(1);
    }

  if(more_than_one_process(context))
    {
      if(find_prefix_aux(result -> trans_assignments, lhs, &match))
	{
	  if(match != lhs)
	    {
	      fputs("*** smvflatten: can not assign `next(", stderr);
	      print(stderr, lhs);
	      fputs(")' and `next(", stderr);
	      print(stderr, match);
	      fputs(")'\n", stderr);
	      exit(1);
	    }
	  
	  old_rhs = (Node*) get_association(result -> trans_assignments, lhs);
	  new_rhs = ite(synchronize(context), rhs, copy(old_rhs));
        }
      else new_rhs = ite(synchronize(context), rhs, copy(lhs));
    }
  else new_rhs = rhs;

  associate(result -> trans_assignments, lhs, new_rhs);

  assignment = new(TRANSASSIGNMENT, lhs, new_rhs);
  result -> module.assign = new(LIST, assignment, result -> module.assign);
}

/*------------------------------------------------------------------------*/

static void ft_ISA(Context * context, Node * node)
{
  Node * name, * module;
  Result * result;

  assert(node && node -> tag == ISA);

  result = context -> result;
  name = car(node);
  module = get_association(result -> modules, name);

  assert(module);

  assert(!cdr(car(node)));		/* parser disallows args */

  if(cdr(car(module)))
    {
      fputs("*** smvflatten: module `", stderr);
      print(stderr, name);
      fputs("' has parameters and is used with `ISA'\n", stderr); 
      exit(1);
    }

  if(verbose >= 3)
    {
      fputs("-- [verbose]     merging `", stderr);
      print(stderr, name);
      fputc('\'', stderr);
      if(context -> access)
        {
	  fputs(" into `", stderr);
	  print(stderr, context -> access);
	  fputc('\'', stderr);
	}
      fputc('\n', stderr);
    }
  
  ft_sections(context, cdr(module));
  associate(result -> used_modules, name, name);
}

/*------------------------------------------------------------------------*/

static void ft_sections(Context * context, Node * node)
{
  Node * p, * section, * q, * tmp;
  Result * result;
  Node ** ptr;

  assert(!node || node -> tag == LIST);

  result = context -> result;

  for(p = node; p; p = cdr(p))
    {
      section = car(p);

      switch(section -> tag)
        {
	  case ASSIGN:
	  case VAR:
	  case DEFINE:
	    for(q = car(section); q; q = cdr(q)) (void) ft(context, car(q), 0);
	    break;

	  case INVAR:
	  case INIT:
	    tmp = ft(context, car(section), 0);
	    ptr = section_Module(&result -> module, section);
	    *ptr = *ptr ? new(AND, *ptr, tmp) : tmp;
	    break;

	  case TRANS:
	    tmp = ft(context, car(section), 0);
	    add2trans(context, tmp);
	    break;

	  case COMPUTE:
	  case FAIRNESS:
	  case SPEC:
	  case LTLSPEC:
	    tmp = ft(context, car(section), 0);
	    ptr = section_Module(&result -> module, section);
	    *ptr = cons(tmp, *ptr);
	    break;

	  case ISA:
	    ft_ISA(context, section);
	    break;
	  
	  default:
	    assert(0);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/
#if 0

static int is_array_of_modules(Node * type)
{
  Node * p;
  int res;

  for(p = type; p && p -> tag == ARRAY; p = cdr(p))
    ;
  
  assert(p);

  res = (p -> tag == INSTANCE || p -> tag == PROCESS);

  return res;
}

#endif
/*------------------------------------------------------------------------*/

static void ft_instance(Context * outer, unsigned is_process, Node * node)
{
  Node * p, * q, * lhs, * rhs, * arg, * para, * args, * paras;
  Node * name, * module;
  Result * result;
  Context inner;

  assert(node && node -> tag == INSTANCE);

  result = outer -> result;

  name = car(car(node));
  module = get_association(result -> modules, name);
  push_Context(is_process, outer, &inner, module);

  assert(module);

  args = cdr(car(node));
  paras = cdr(car(module));

  if(length(args) != length(paras))
    {
      fputs( 
	"*** smvflatten: wrong number of arguments for `", stderr);
      print(stderr, name);
      fputs("' in declaration of `", stderr);
      print(stderr, outer -> variable);
      fputs("'\n", stderr);
      exit(1);
    }
  else
  if(verbose >= 3)
    {
      fputs("-- [verbose]     flattening `", stderr);
      if(is_process) fputs("process ", stderr);
      print(stderr, inner.access);
      fputs("'\n", stderr);
    }
  
  for(p = args, q = paras; p && q; p = cdr(p), q = cdr(q))
    {
      arg = car(p);
      para = car(q);

      lhs = append_tagged(ACCESS, inner.access, para);
      rhs = ft(outer, arg, 0);

      add_parameter(outer -> result, lhs, rhs);
    }
  
  assert(!p == !q);

  ft_sections(&inner, cdr(module));
  release_Context(&inner);
  associate(result -> used_modules, name, name);
}

/*------------------------------------------------------------------------*/

static Node * ft(Context * context, Node * node, unsigned add_next)
{
  Node * res, * a, * b, * tmp, * lhs, * rhs, * type;
  int tag, l, r, i;
  Result * result;
  Context inner;
  unsigned n;

  if(node)
    {
      result = context -> result;

      switch((tag = node -> tag))
        {
	  case NUMBER:
	    res = copy(node);
	    break;

	  case ACCESS:
	  case ATOM:
	    if(more_than_one_process(context) && node == result -> running)
	      {
		res = synchronize(context);
	      }
	    else
	    if(node == result -> self)
	      {
	        res = copy(context -> access);
	      }
	    else
	    if(is_associated(result -> constants, node))
	      {
	        res = copy(node);
	      }
	    else
	      {
		tmp = append_tagged(ACCESS, context -> access, node);
		if(find_prefix_aux(result -> parameters, tmp, &lhs))
		  {
		    rhs = get_association(result -> parameters, lhs);

		    if(lhs == tmp) res = copy(rhs);
		    else
		      {
			l = length(tmp);
			r = length(lhs);

			assert(l > r);

			a = get_suffix(tmp, l - r);

			res = append_tagged(ACCESS, rhs, a);
			delete(a);
		      }
		    delete(tmp);
		  }
		else res = tmp;
	      }
	    
	    for(n = 0; n < add_next; n++) res = new(NEXT, res, 0);
	    break;
	  
	  case NEXT:
	    res = ft(context, car(node), add_next + 1);
	    break;

	  case BOOLEAN:
	    add_variable(context, node);
	    res = 0;
	    break;

	  case TWODOTS:
	    if(context -> variable)
	      {
		if(is_boolean_type(node)) type = new(BOOLEAN, 0, 0);
		else type = copy(node);
		add_variable(context, type);
		delete(type);
		res = 0;
	      }
	    else res = copy(node);
	    break;
	  
	  case DECL:
	    push_Variable(context, &inner, car(node));
	    a = ft(&inner, cdr(node), 0);
	    assert(!a);
	    release_Context(&inner);
	    res = 0;
	    break;

	  case DEFINEASSIGNMENT:
	    a = ft(context, car(node), 0);
	    b = ft(context, cdr(node), 0);
	    add_definition(context, a, b);
	    res = 0;
	    break;

	  case INVARASSIGNMENT:
	    a = ft(context, car(node), 0);
	    b = ft(context, cdr(node), 0);
	    add_invar_assignment(context, a, b);
	    res = 0;
	    break;
	  
	  case TRANSASSIGNMENT:
	    a = ft(context, car(node), 0);
	    b = ft(context, cdr(node), 0);
	    add_trans_assignment(context, a, b);
	    res = 0;
	    break;

	  case INITASSIGNMENT:
	    a = ft(context, car(node), 0);
	    b = ft(context, cdr(node), 0);
	    add_init_assignment(result, a, b);
	    res = 0;
	    break;

	  case ARRAY:

	    assert(car(node) -> tag == TWODOTS);
	    assert(car(car(node)) -> tag == NUMBER);
	    assert(cdr(car(node)) -> tag == NUMBER);

	    l = (long)car(car(car(node)));
	    r = (long)car(cdr(car(node)));

	    assert(l < r);

	    for(i = l; i <= r; i++)
	      {
		tmp = number(i);
		push_Access(context, &inner, tmp);
		a = ft(&inner, cdr(node), 0);
		assert(!a);
		release_Context(&inner);
		delete(tmp);
	      }

	    res = 0;
	    break;

	  case ENUM:

	    if(context -> variable)
	      {
	        /* Type.
		 */
		type = normalize_type(node);
		add_variable(context, type);
		delete(type);
		res = 0;
	      }
	    else
	      {
	        /* Term.
		 */
		res = copy(node);
	      }
	    break;

	  case PROCESS:
	    ft_instance(context, 1, car(node));
	    res = 0;
	    break;
	  
	  case INSTANCE:
	    ft_instance(context, 0, node);
	    res = 0;
	    break;
	  
	  case NOTEQUAL:
	    a = ft(context, car(node), add_next);
	    b = ft(context, cdr(node), add_next);
	    tmp = new(EQUAL, a, b);
	    res = new(NOT, tmp, 0);
	    break;
	  
	  case GT:
	    a = ft(context, car(node), add_next);
	    b = ft(context, cdr(node), add_next);
	    res = new(LT, b, a);
	    break;

	  case GE:
	    a = ft(context, car(node), add_next);
	    b = ft(context, cdr(node), add_next);
	    res = new(LE, b, a);
	    break;

	  default:
	    a = ft(context, car(node), add_next);
	    b = ft(context, cdr(node), add_next);
	    res = new(node -> tag, a, b);
	    break;
	}
    }
  else res = 0;
  
  return res;
}

/*------------------------------------------------------------------------*/

static void check_defined(Result * result, Node * node)
{
  Assoc * container;
  Node * match;
  int tag;

  if(node)
    {
      switch((tag = node -> tag))
	{
	  case BOOLEAN:
	  case NUMBER:
	    break;

	  case ACCESS:
	  case ATOM:
	    if((cdr(result -> processes) && node == result -> running) 
	       ||
	       is_associated(result -> constants, node))
	      {
	        /* everything is fine */
	      }
	    else
	    if(!find_prefix(result, node, &match, &container))
	      {
	        fputs("*** smvflatten: `", stderr);
		print(stderr, node);
	        fputs("' is undefined\n", stderr);
		exit(1);
	      }
	    break;

	  case DEFINEASSIGNMENT:
	  case INVARASSIGNMENT:
	  case INITASSIGNMENT:
	  case TRANSASSIGNMENT:
	    check_defined(result, cdr(node));
	    break;

	  default:
	    check_defined(result, car(node));
	    check_defined(result, cdr(node));
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void check_all_defined(Result * result)
{
  check_defined(result, result -> module.define);
  check_defined(result, result -> module.assign);

  check_defined(result, result -> module.invar);
  check_defined(result, result -> module.init);
  check_defined(result, result -> module.trans);

  check_defined(result, result -> module.fairness);
  check_defined(result, result -> module.spec);
  check_defined(result, result -> module.ltlspec);
  check_defined(result, result -> module.compute);
}

/*------------------------------------------------------------------------*/

Node * flatten(Node * node)
{
  Node * main_atom, * main_module, * res;
  Context context;
  Result result;
 
  if(verbose)
    fprintf(stderr, "-- [verbose] phase 1: flattening hirarchy ...\n");

  main_atom = init_Result(&result, node);
  main_module = get_association(result.modules, main_atom);
  delete(main_atom);
  init_Context(&context, &result, main_module);

  ft_sections(&context, cdr(main_module));
  check_all_defined(&result);

  res = merge_Module(&result.module);

  release_Context(&context);
  release_Result(&result);

  if(verbose) fprintf(stderr, "-- [verbose] end of phase 1: flattened.\n");

  return res;
}

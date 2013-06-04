/*------------------------------------------------------------------------*/
/* Copyright 1999-2013 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "cache.h"
#include "encode.h"
#include "module.h"
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

typedef struct EncContext EncContext;

/*------------------------------------------------------------------------*/

struct EncContext
{
  Assoc * node2type;
  Node * variable;
  Cache * cache;
  Node * invar;
  Module module;
  Node * type_checks;
};

/*------------------------------------------------------------------------*/

static void extract(Node * arg, Node ** node, Node ** type, int * bit)
{
  Node * p;

  if(arg)
    {
      p = arg;
      *node = car(p);
      p = cdr(p);
      *type = car(p);
      p = cdr(p);
      *bit = (long)car(car(p));
    }
  else
    {
      *node = 0;
      *type = 0;
      *bit = 0;
    }
}

/*------------------------------------------------------------------------*/

static Node * combine(Node * node, Node * type, int bit)
{
  Node * res;

  if(node)
    {
      res = cons(number(bit), 0);
      res = cons(copy(type), res);
      res = cons(copy(node), res);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * add_at(EncContext * context, Node * node, unsigned bit)
{
  Node * res, * tmp, * type;
  unsigned w;

  type = get_association(context -> node2type, node);
  assert(type);
  w = num_bits(type);
  if(bit >= w) res = get_first_type(type);
  else
    {
      tmp = new(AT, number((int) bit), 0);
      res = append_tagged(ACCESS, node, tmp);
      delete(tmp);
    }

  return res;
}

/*------------------------------------------------------------------------*/

static int is_power_of_two(int n)
{
  int l, p, res;

  assert(n >= 0);

  l = ldceil((int) n);
  p = (1 << l);

  assert(n <= p);

  res = (n == p);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc(EncContext * context, Node * arg);

/*------------------------------------------------------------------------*/

static Node * enc_le_aux(
  EncContext * context, Node * type, Node * lhs, Node * rhs, int bit)
{
  Node * arg, * enc_lhs, * enc_rhs, * res, * tmp, * cond, * other;

  assert(bit >= 0);

  arg = combine(lhs, type, bit);
  enc_lhs = enc(context, arg);
  delete(arg);

  arg = combine(rhs, type, bit);
  enc_rhs = enc(context, arg);
  delete(arg);

  if(bit)
    {
      tmp = enc_le_aux(context, type, lhs, rhs, bit - 1);
      cond = new_simplify(IFF, copy(enc_lhs), copy(enc_rhs));
      other = new_simplify(IMPLIES, enc_lhs, enc_rhs);
      res = ite_simplify(cond, tmp, other);
    }
  else res = new_simplify(IMPLIES, enc_lhs, enc_rhs);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_le_ge(EncContext * context, Node * le)
{
  Node * lhs, * rhs, * res, * lhs_type, * rhs_type, * super_type;
  int n;

  switch(le -> tag)
    {
      case LE:
	lhs = car(le);
	rhs = cdr(le);
	break;

      case GE:
	lhs = cdr(le);
	rhs = car(le);
	break;

      default: 
        assert(0);
	lhs = rhs = 0;
	break;
    }

  lhs_type = get_association(context -> node2type, lhs);
  rhs_type = get_association(context -> node2type, rhs);

  assert(lhs_type);
  assert(rhs_type);

  if(!is_number_type(lhs_type) || !is_number_type(rhs_type))
    {
      fputs(
        "*** smvflatten: expected number type for arguments of `<='\n",
	stderr);
      exit(1);
    }

  super_type = merge_type(lhs_type, rhs_type);
  n = num_bits(super_type);
  res = enc_le_aux(context, super_type, lhs, rhs, n - 1);
  delete(super_type);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_lt_aux(
  EncContext * context, Node * type, Node * lhs, Node * rhs, int bit)
{
  Node * arg, * enc_lhs, * enc_rhs, * res, * tmp, * cond, * other;

  assert(bit >= 0);

  arg = combine(lhs, type, bit);
  enc_lhs = enc(context, arg);
  delete(arg);

  arg = combine(rhs, type, bit);
  enc_rhs = enc(context, arg);
  delete(arg);

  if(bit)
    {
      tmp = enc_lt_aux(context, type, lhs, rhs, bit - 1);
      cond = new_simplify(IFF, copy(enc_lhs), copy(enc_rhs));
      other = new_simplify(AND, new_simplify(NOT, enc_lhs, 0), enc_rhs);
      res = ite_simplify(cond, tmp, other);
    }
  else res = new_simplify(AND, new_simplify(NOT, enc_lhs, 0), enc_rhs);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_lt_gt(EncContext * context, Node * lt)
{
  Node * lhs, * rhs, * res, * lhs_type, * rhs_type, * super_type;
  int n;

  switch(lt -> tag)
    {
      case LT:
	lhs = car(lt);
	rhs = cdr(lt);
	break;

      case GT:
	lhs = cdr(lt);
	rhs = car(lt);
	break;

      default: 
        assert(0);
	lhs = rhs = 0;
	break;
    }

  lhs_type = get_association(context -> node2type, lhs);
  rhs_type = get_association(context -> node2type, rhs);

  assert(lhs_type);
  assert(rhs_type);

  if(!is_number_type(lhs_type) || !is_number_type(rhs_type))
    {
      fputs(
        "*** smvflatten: expected number type for arguments of `<'\n",
	stderr);
      exit(1);
    }

  super_type = merge_type(lhs_type, rhs_type);
  n = num_bits(super_type);
  res = enc_lt_aux(context, super_type, lhs, rhs, n - 1);
  delete(super_type);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_var(EncContext * context, Node * var_section)
{
  Node * p, * res, * decl, * type, * new_decl, * v, * tmp, * new_v;
  unsigned i, w;
  Node * b, * r;
  unsigned size;

  assert(var_section -> tag == VAR || var_section -> tag == IVAR);

  for(p = car(var_section), res = 0; p; p = cdr(p))
    {
      decl = car(p);
      v = car(decl);
      type = cdr(decl);

      assert(get_association(context -> node2type, v) == type);

      if(is_boolean_type(type))
        {
	  res = cons(copy(decl), res);
	}
      else
        {
	  w = num_bits(type);

	  for(i = w; i; i--)
	    {
	      new_v = add_at(context, v, i - 1);
	      new_decl = new(DECL, new_v, new(BOOLEAN, 0, 0));
	      res = cons(new_decl, res);
	    }

	  size = size_type(type);

	  assert(size);
	  assert(((int) size) >= (int)0);

	  if(!is_power_of_two((unsigned) size))
	    {
	      b = get_last_type(type);
	      r = enc_le_aux(context, type, v, b, w - 1);
	      delete(b);

	      context -> invar = new_simplify(AND, context -> invar, r);

	      if(verbose >= 3)
	        {
		  fputs("-- [verbose]     restricting range of `", stderr);
		  print(stderr, v);
		  fputs("'\n", stderr);
		}
	    }
	}
    }
  
  tmp = reverse(res);
  delete(res);
  res = new(VAR, tmp, 0);	// TODO special case for IVAR?

  return res;
}

/*------------------------------------------------------------------------*/

static Node * reencode_subtype(
  EncContext * context, Node * node, Node * type)
{
  Node * res, * sub_type, * one_case, * cond, * p, * num, * c, * tmp;
  int i, l, r;

  sub_type = get_association(context -> node2type, node);
  assert(sub_type);

  switch(sub_type -> tag)
    {
      case BOOLEAN:
      case TWODOTS:
        range_bounds(sub_type, &l, &r);
	for(i = r, res = 0; i >= l; i--)
	  {
	    num = number(i);
	    if(!type_contains(type, num))
	      {
	        delete(num);
		num = get_first_type(type);
	      }

	    if(i == r) cond = number(1);
	    else cond = new(EQUAL, copy(node), copy(num));

	    one_case = new(COLON, cond, num);
	    res = cons(one_case, res);
	  }
        break;
      
      case ENUM:
        for(p = car(sub_type), res = 0; p; p = cdr(p))
	  {
	    c = copy(car(p));
	    if(!type_contains(type, c))
	      {
	        delete(c);
		c = get_first_type(type);
	      }

	    if(cdr(p)) cond = new(EQUAL, copy(node), copy(c));
	    else cond = number(1);

	    one_case = new(COLON, cond, c);
	    res = cons(one_case, res);
	  }
	tmp = res;
	res = reverse(tmp);
	delete(tmp);
        break;
      
      default:
        assert(0);
	res = 0;
	break;
    }

  res = new(CASE, res, 0);
  
  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_assignments(EncContext * context, Node * section)
{
  Node * res, * type, * p, * assignments, * assignment, * lhs, * rhs;
  Node * enc_assignment, * enc_lhs, * enc_rhs, * arg, * tmp;
  Node * lhs_type, * rhs_type;
  int i, n, tag, section_tag;

  section_tag = section -> tag;

  assert(section_tag == DEFINE || section_tag == ASSIGN);
  assignments = car(section);

  for(p = assignments, res = 0; p; p = cdr(p))
    {
      assignment = car(p);

      switch((tag = assignment -> tag))
	{
	  case DEFINEASSIGNMENT:
	  case INVARASSIGNMENT:
	  case INITASSIGNMENT:
	  case TRANSASSIGNMENT:

	    lhs = car(assignment);
	    rhs = cdr(assignment);
	    lhs_type = get_association(context -> node2type, lhs);
	    assert(lhs_type);
	    rhs_type = get_association(context -> node2type, rhs);
	    assert(rhs_type);
	    type = copy(lhs_type);
	    if(is_boolean_type(type))
	      {
		enc_lhs = copy(lhs);
		arg = combine(rhs, type, 0);
		enc_rhs = enc(context, arg);
		delete(arg);
		enc_assignment = new(tag, enc_lhs, enc_rhs);
		res = cons(enc_assignment, res);
	      }
	    else
	      {
	        n = num_bits(type);
		for(i = n; i; i--)
		  {
		    enc_lhs = add_at(context, lhs, i - 1);
		    arg = combine(rhs, type, i - 1);
		    enc_rhs = enc(context, arg);
		    delete(arg);
		    enc_assignment = new(tag, enc_lhs, enc_rhs);
		    res = cons(enc_assignment, res);
		  }
	      }
	    delete(type);
	    break;
	  
	  default:
	    assert(0);
	    break;
	}
    }
  
  tmp = reverse(res);
  delete(res);
  res = new(section_tag, tmp, 0);
  
  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_equal(EncContext * context, Node * e)
{
  Node * lhs, * rhs, * res, * enc_lhs, * enc_rhs, * enc_equality;
  Node * lhs_type, * rhs_type, * super_type, * arg;
  int i, n;

  assert(e -> tag == EQUAL || e -> tag == NOTEQUAL);

  lhs = car(e);
  rhs = cdr(e);

  lhs_type = get_association(context -> node2type, lhs);
  rhs_type = get_association(context -> node2type, rhs);

  assert(lhs_type);
  assert(rhs_type);

  super_type = merge_type(lhs_type, rhs_type);
  n = num_bits(super_type);

  for(i = 0, res = number(1); i < n; i++)
    {
      arg = combine(lhs, super_type, i);
      enc_lhs = enc(context, arg);
      delete(arg);

      arg = combine(rhs, super_type, i);
      enc_rhs = enc(context, arg);
      delete(arg);

      enc_equality = new_simplify(IFF, enc_lhs, enc_rhs);
      res = new_simplify(AND, res, enc_equality);
    }
  
  delete(super_type);

  if(e -> tag == NOTEQUAL) res = new_simplify(NOT, res, 0);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_case(EncContext * context, Node * arg)
{
  Node * res, * p, * cond, * val, * enc_cond, * enc_val, * type, * node;
  Node * boolean_type, * new_arg, * tmp;
  int bit;

  extract(arg, &node, &type, &bit);

  assert(node -> tag == CASE);

  if(bit < (int)num_bits(type))
    {
      boolean_type = new(BOOLEAN, 0, 0);

      for(p = car(node), res = 0; p; p = cdr(p))
	{
	  cond = car(car(p));
	  val = cdr(car(p));

	  new_arg = combine(cond, boolean_type, 0);
	  enc_cond = enc(context, new_arg);
	  delete(new_arg);

	  arg = combine(val, type, bit);
	  enc_val = enc(context, arg);
	  delete(arg);

	  tmp = new(COLON, enc_cond, enc_val);
	  res = cons(tmp, res);
	}

      delete(boolean_type);

      tmp = reverse(res);
      delete(res);
      res = new_simplify(CASE, tmp, 0);
    }
  else res = number(0);

  return res;
}

/*------------------------------------------------------------------------*/
/* Computes the carry of the two arguments at the bit position 'bit'.  The
 * addition is performed implictely subtracting the start of the two types
 * given for the arguments, which not necessarily have to be the real types
 * of the arguments.  This procedure may also be used to perform the
 * calculation of the carry for substraction.  Then the last argument should
 * be non zero.
 */
static Node * enc_carry(
  EncContext * context,
  Node * x,
  Node * y,
  Node * x_type,
  Node * y_type,
  int bit,
  int subtract)
{
  Node * arg, * enc_x, * enc_y, * res, * carry, * a, * b, * c, * tmp;

  if(bit >= 0)
    {
      arg = combine(x, x_type, bit);
      enc_x = enc(context, arg);
      delete(arg);

      arg = combine(y, y_type, bit);
      enc_y = enc(context, arg);
      if(subtract) enc_y = new_simplify(NOT, enc_y, 0);
      delete(arg);

      carry = enc_carry(context, x, y, x_type, y_type, bit - 1, subtract);
      a = new_simplify(AND, carry, enc_x);
      b = new_simplify(AND, copy(carry), enc_y);
      c = new_simplify(AND, copy(enc_x), copy(enc_y));
      tmp = new_simplify(OR, a, b);
      res = new_simplify(OR, tmp, c);
    }
  else res = number(subtract ? 1 : 0);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_add_aux(
  EncContext * context,
  Node * x,
  Node * y,
  Node * x_type, 
  Node * y_type,
  int bit,
  int subtract)
{
  Node * arg, * enc_x, * enc_y, * res, * carry, * type;
#ifndef NDEBUG
  int l, r;
#endif

  assert(bit >= 0);

  type = merge_type (x_type, y_type);
  if (is_range_type(type))
    range_bounds (type, &l, &r);
  else
    l = r = -1;

  if (l) 
    {
      fputs(
	"*** smvflatten: can only add/subtract range types starting at 0..\n",
	stderr);
      exit(1);
    }

  arg = combine(x, type, bit);
  enc_x = enc(context, arg);
  delete(arg);

  arg = combine(y, type, bit);
  enc_y = enc(context, arg);
  delete(arg);

  carry = enc_carry(context, x, y, type, type, bit - 1, subtract);
  res = new_simplify(IFF, carry, new_simplify(IFF, enc_x, enc_y));
  delete (type);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc_add(
  EncContext * context, Node * x, Node * y, int bit, int subtract)
{
  Node * res, * x_type, * y_type;

  x_type = get_association(context -> node2type, x);
  y_type = get_association(context -> node2type, y);
  assert(x_type);
  assert(y_type);
  assert(is_range_type(x_type));
  assert(is_range_type(y_type));
  res = enc_add_aux(context, x, y, x_type, y_type, bit, subtract);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * promote_boolean(Node * node, Node * type)
{
  Node * tmp, * res;

  (void) node;

  tmp = new(BOOLEAN, 0, 0);
  if(is_subtype(tmp, type))
    {
      fputs(
      "*** smvflatten: can not promote boolean type yet\n",
      stderr);
    }
  else
    {
      fputs(
	"*** smvflatten: expected boolean type\n",
	stderr);
    }
  res = 0;
  exit(1);

  delete(res);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * enc(EncContext * context, Node * arg)
{
  Node * res, * a, * b, * node, * type, * arg0, * arg1, * var_type;
  Node * case_expr, * tmp, * common;
  int tag, bit;
  unsigned pos;

  if(arg)
    {
      if(is_cached(context -> cache, arg))
        {
	  res = copy(lookup_Cache(context -> cache, arg));
	}
      else
        {
	  extract(arg, &node, &type, &bit);

	  switch((tag = node -> tag))
	    {
	      case IVAR:
	      case VAR:
		res = enc_var(context, node);
	        break;
	      
	      case CASE:
	        res = enc_case(context, arg);
	        break;

	      case NUMBER:
	        assert(type_contains(type, node));
		if(((unsigned)bit) < num_bits(type))
		  {
		    pos = get_type_position(type, node);
		    assert(pos < (1u << num_bits(type)));
		    res = number((pos & (1u << bit)) ? 1 : 0);
		  }
		else res = number(0);			/* zero extension */
	        break;
	      
	      case ACCESS:
	      case ATOM:
		if(type_contains(type, node))
		  {
		    /* constant
		     */
		    pos = get_type_position(type, node);
		    assert(pos < (1u << num_bits(type)));
		    res = number((pos & (1u << bit)) ? 1 : 0);
		  }
		else
		  {
		    var_type = get_association(context -> node2type, node);
		    assert(var_type);
		    if(var_type == type)
		      {
			if(is_boolean_type(type)) res = copy(node);
			else res = add_at(context, node, bit);
		      }
		    else
		      {
			common = intersect_type(var_type, type);
			if(common)
			  {
			    case_expr = 
			      reencode_subtype(context, node, common);
			    add_type(context -> node2type, case_expr);
			    arg0 = combine(case_expr, type, bit);
			    res = enc(context, arg0);
			    delete(arg0);
			    delete(case_expr);
			    delete(common);
			  }
			else
			  {
			    /* The variable does not have any value common
			     * with 'type'.  Therefore silently return the
			     * first value of 'type'.  The type checks
			     * introduced in phase1 should check for this
			     * behaviour.
			     */
			    res = copy(get_first_type(type));
			  }
		      }
		  }
	        break;
	      
	      case EQUAL:
	      case NOTEQUAL:
		tmp = enc_equal(context, node);
	        if(is_boolean_type(type)) res = copy(tmp);
		else res = promote_boolean(tmp, type);
		delete(tmp);
	        break;

	      case GT:
	      case LT:
		tmp = enc_lt_gt(context, node);
	        if(is_boolean_type(type)) res = copy(tmp);
		else res = promote_boolean(tmp, type);
		delete(tmp);
		break;
	      
	      case GE:
	      case LE:
		tmp = enc_le_ge(context, node);
	        if(is_boolean_type(type)) res = copy(tmp);
		else res = promote_boolean(tmp, type);
		delete(tmp);
		break;
	      
	      case PLUS:
		res = enc_add(context, car(node), cdr(node), bit, 0);
		break;
	      
	      case MINUS:
		res = enc_add(context, car(node), cdr(node), bit, 1);
		break;
	      
	      case DEFINE:
	      case ASSIGN:
	        res = enc_assignments(context, node);
	        break;
	      
	      case INVAR:
	      case INIT:
	      case TRANS:
	      case FAIRNESS:
	      case SPEC:
	      case LTLSPEC:
	        type = new(BOOLEAN, 0, 0);
		arg0 = combine(car(node), type, 0);
		a = enc(context, arg0);
		delete(arg0);
		delete(type);
		res = new(tag, a, 0);
	        break;
	      
	      case COMPUTE:
		type = new(BOOLEAN, 0, 0);
		arg0 = combine(car(car(node)), type, 0);
		arg1 = combine(cdr(car(node)), type, 0);
		a = enc(context, arg0);
		b = enc(context, arg1);
		delete(arg0);
		delete(arg1);
		delete(type);
		res = new(COMPUTE, new(car(node) -> tag, a, b), 0);
		break;
	      
	      case MODULE:
	        arg1 = combine(cdr(node), 0, 0);
		b = enc(context, arg1);
		delete(arg1);
		res = new(MODULE, copy(car(node)), b);
	        break;

	      default:
	        arg0 = combine(car(node), type, bit);
	        arg1 = combine(cdr(node), type, bit);
		a = enc(context, arg0);
		b = enc(context, arg1);
		delete(arg1);
		delete(arg0);
		res = new_simplify(tag, a, b);
		break;
	    }

	  insert_Cache(context -> cache, copy(arg), copy(res));
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static void setup_EncContext(EncContext * context, Assoc * node2type)
{
  context -> invar = number(1);
  context -> node2type = node2type;
  context -> cache = new_Cache("encoder cache");
  context -> variable = 0;
  context -> type_checks = 0;
}

/*------------------------------------------------------------------------*/

static void release_EncContext(EncContext * context)
{
  forall_src_in_Assoc(context -> cache -> assoc, (void(*)(void*)) &delete);
  forall_dst_in_Assoc(context -> cache -> assoc, (void(*)(void*)) &delete);
  delete_Cache(context -> cache);

  delete(context -> invar);
}

/*------------------------------------------------------------------------*/

static void p1(EncContext * context, Node * node)
{
}

/*------------------------------------------------------------------------*/

static void enc_backannotate(
  Assoc * node2type, Node * node, Assoc * var2type)
{
  Node * stripped_var, * var, * type;

  if(node)
    {
      switch(node -> tag)
        {
	  case MODULE:
	    enc_backannotate(node2type, cdr(node), var2type);
	    break;

	  case IVAR:
	  case VAR:
	    enc_backannotate(node2type, car(node), var2type);
	    break;

	  case LIST:
	    enc_backannotate(node2type, car(node), var2type);
	    enc_backannotate(node2type, cdr(node), var2type);
	    break;

	  case DECL:

	    var = car(node);
	    stripped_var = strip_at(var);

	    if(var == stripped_var)
	      {
		type = get_association(node2type, var);
	        assert(is_boolean_type(type));
	      }
	    else
	      {
	        type = get_association(node2type, stripped_var);
		assert(type);
		assert(!is_boolean_type(type));
	      }

	    assert(!is_associated(var2type, var));
	    associate(var2type, copy(var), copy(type));
	    delete(stripped_var);
	    break;

	  default:
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void p3_and_section(Node ** section_ptr, Node * node)
{
  if(*section_ptr)
    {
      *section_ptr = new_simplify(AND, *section_ptr, node);
    }
  else *section_ptr = node;
}

/*------------------------------------------------------------------------*/

static void p3(EncContext * context, Node * node)
{
  Node * decl, * lhs, * rhs, * eq, * contents;
  Module * m;

  m = &context -> module;

  if(node)
    {
      switch(node -> tag)
        {
	  case VAR:
	  case IVAR:
	  case ASSIGN:
	  case DEFINE:
	    p3(context, car(node));
	    break;
	  
	  case MODULE:
	    p3(context, cdr(node));
	    break;
	  
	  case LIST:
	    p3(context, car(node));
	    p3(context, cdr(node));
	    break;
	  
	  case DEFINEASSIGNMENT:
	    rhs = cdr(node);
	    if(rhs -> contains_next)
	      {
		/* Unfortunately this implies that we have to declare this
		 * defined variable.
		 */
		lhs = car(node);
		decl = new(DECL, copy(lhs), new(BOOLEAN, 0, 0));
		m -> var = cons(decl, m -> var);

		if(verbose >= 3)
		  {
		    fputs("-- [verbose]     ", stderr);
		    print(stderr, lhs);
		    fputs(" := ... next ... (definition)\n", stderr);
		  }

		eq = new_simplify(IFF, copy(lhs), copy(rhs));
		p3_and_section(&m -> trans, eq);
	      }
	    else m -> define = cons(copy(node), m -> define);
	    break;
	  
	  case DECL:
	    m -> var = cons(copy(node), m -> var);
	    break;
	  
	  case INITASSIGNMENT:
	    assert(!cdr(node) -> contains_next);
	    m -> assign = cons(copy(node), m -> assign);
	    break;

	  case INVARASSIGNMENT:
	    rhs = cdr(node);
	    if(rhs -> contains_next)
	      {
		lhs = car(node);
		eq = new_simplify(IFF, copy(lhs), copy(rhs));
		p3_and_section(&m -> trans, eq);

		if(verbose >= 3)
		  {
		    /* This is untested, since the parser disallows next
		     * assignments occuring on the RHS.
		     */
		    assert(0);

		    fputs("-- [verbose]     ", stderr);
		    print(stderr, lhs);
		    fputs(" := ... next ... (invar assignment)\n", stderr);
		  }
	      }
	    else m -> assign = cons(copy(node), m -> assign);
	    break;

	  case TRANSASSIGNMENT:
	    rhs = cdr(node);
	    if(rhs -> contains_next)
	      {
		lhs = car(node);
		eq = new_simplify(IFF, new(NEXT, copy(lhs), 0), copy(rhs));
		p3_and_section(&m -> trans, eq);

		if(verbose >= 3)
		  {
		    fputs("-- [verbose]     next(", stderr);
		    print(stderr, lhs);
		    fputs(") := ... next ...\n", stderr);
		  }
	      }
	    else m -> assign = cons(copy(node), m -> assign);
	    break;
	  
	  case INIT:
	    contents = car(node);
	    if(!is_true(contents)) p3_and_section(&m -> init, copy(contents));
	    break;

	  case INVAR:
	    contents = car(node);
	    if(!is_true(contents)) p3_and_section(&m -> invar, copy(contents));
	    break;

	  case TRANS:
	    contents = car(node);
	    if(!is_true(contents)) p3_and_section(&m -> trans, copy(contents));
	    break;

	  case FAIRNESS:
	    contents = car(node);
	    if(!is_true(contents))
	      m -> fairness = cons(copy(contents), m -> fairness);
	    break;

	  case SPEC:
	    contents = car(node);
	    if(!is_true(contents)) m -> spec = cons(copy(contents), m -> spec);
	    break;
	  
	  case LTLSPEC:
	    contents = car(node);
	    if(!is_true(contents)) m -> ltlspec = 
	      cons(copy(contents), m -> ltlspec);
	    break;
	  
	  case COMPUTE:
	    m -> compute = cons(copy(car(node)), m -> compute);
	    break;

	  default:
	    assert(0);
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/
/* First introduce type checking specifications for all RHS which have a
 * type that is not subset of the type of the LHS.
 */
static void phase1(EncContext * context, Node * node)
{
  if(verbose >= 2) 
    fputs(
      "-- [verbose]   introduce type checks ... \n",
      stderr);
  
  p1(context, node);

  if(verbose >= 2) 
    fprintf(
      stderr,
      "-- [verbose]   introduced %u type checks ... \n",
      length(context -> type_checks));
}

/*------------------------------------------------------------------------*/
/* Second use the type information and do a binary encoding of everything.
 */
static Node * phase2(EncContext * context, Node * node)
{
  Node * res, * arg;

  if(verbose >= 2) fputs("-- [verbose]   binary encoding ... \n", stderr);

  arg = combine(node, 0, 0);
  res = enc(context, arg);
  delete(arg);

  if(verbose >= 2) fputs("-- [verbose]   binary encoded.\n", stderr);

  return res;
}

/*------------------------------------------------------------------------*/
/* Third Move assignments and definitions that have a `next' operator on
 * the RHS to the TRANS section.  Also incorporate the `invar' section in
 * the context.
 */
static Node * phase3(EncContext * context, Node * node)
{
  Node * res;

  if(verbose >= 2) 
    fputs(
      "-- [verbose]   removing `next' in RHS of assignments ...\n",
      stderr);
  
  init_Module(&context -> module);
  if(!is_true(context -> invar))
    context -> module.invar = copy(context -> invar);	/* add `invar' */
  p3(context, node);
  res = merge_Module(&context -> module);
  release_Module(&context -> module);
  
  if(verbose >= 2) 
    fputs(
      "-- [verbose]   removed `next' in RHS of assignments.\n",
      stderr);
    
  return res;
}

/*------------------------------------------------------------------------*/
/* Fourth provide back annotation for sliced non boolean variables.
 */
static void phase4(EncContext * context, Node * res)
{
  Assoc * var2type, * node2type;

  if(verbose >= 2) fputs("-- [verbose]   back annotating ...\n", stderr);

  node2type = context -> node2type;
  var2type = new_Assoc();
  enc_backannotate(node2type, res, var2type);
  forall_src_in_Assoc(node2type, (void(*)(void*)) &delete);
  forall_dst_in_Assoc(node2type, (void(*)(void*)) &delete);
  reset_Assoc(node2type);
  map_Assoc(var2type, node2type, (void(*)(void*,void*,void*))&associate);
  delete_Assoc(var2type);

  if(verbose >= 2) fputs("-- [verbose]   back annotated.\n", stderr);
}

/*------------------------------------------------------------------------*/

Node * encode(Assoc * node2type, Node * node)
{
  Node * res, * tmp;
  EncContext context;

  if(verbose) fputs("-- [verbose] phase 4: boolean encoding ...\n", stderr);
  setup_EncContext(&context, node2type);
  phase1(&context, node);
  res = phase2(&context, node);
  tmp = res; res = phase3(&context, tmp); delete(tmp);
  phase4(&context, res);
  release_EncContext(&context);
  if(verbose) fputs("-- [verbose] end of phase 4: encoded.\n", stderr);
  return res;
}

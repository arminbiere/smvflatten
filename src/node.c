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
#include "prime.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <strings.h>

/*------------------------------------------------------------------------*/

extern char * strdup(const char*);

/*------------------------------------------------------------------------*/

extern int verbose, simplification_level, enable_nnf;

/*------------------------------------------------------------------------*/

static Node ** nodes = 0;
static unsigned num_nodes, size_nodes, max_nodes, gensym_counter;
static double searched, visited, simplify_calls;
static unsigned nodes_generated = 0;

/*------------------------------------------------------------------------*/

static Assoc * oracles = 0, * negation_cache = 0;

/*------------------------------------------------------------------------*/

void init_Node(void)
{
  nodes = (Node**) calloc(size_nodes = next_prime(0), sizeof(Node*));
  searched = visited = simplify_calls = 0.0;
  max_nodes = num_nodes = 0;
  gensym_counter = 0;
  oracles = new_Assoc();
  if(enable_nnf) negation_cache = new_Assoc();
}

/*------------------------------------------------------------------------*/

void exit_Node(void)
{
#ifndef CHECK_NODE_LEAKAGE

  Node * p, * tmp;
  unsigned i;

#endif

  forall_src_in_Assoc(oracles, (void(*)(void*)) &delete);
  delete_Assoc(oracles);

  if(enable_nnf) delete_Assoc(negation_cache);

#ifndef CHECK_NODE_LEAKAGE

  for(i = 0; i < size_nodes; i++)
    for(p = nodes[i]; p; p = tmp)
      {
        tmp = p -> next;
	free(p);
      }

#endif
  
  free(nodes);

  if(verbose)
    {
      fprintf(
        stderr,
	"-- [verbose] Node: %u num, %u max, %u size, %.1f%% filled\n",
        num_nodes,
	max_nodes,
	size_nodes, 100.0 * (((double)num_nodes) / ((double)size_nodes)));

      fprintf(
        stderr,
	"-- [verbose] Node: %.0f searched, %.0f visited, %.2f average\n",
	searched,
	visited,
	searched > 0 ? visited / searched : 0.0);
      
      fprintf(
        stderr,
	"-- [verbose] Node: %.0f simplification steps\n",
	simplify_calls);
    }
}

/*------------------------------------------------------------------------*/

unsigned count_Node(void)
{
  return num_nodes;
}

/*------------------------------------------------------------------------*/

static unsigned hash_string(const char * str)
{
  unsigned tmp1, tmp2, res;
  const char * p;

  for(p = str, res = 0; *p; p++)
    {
      tmp1 = (res << 4) + *p;
      tmp2 = tmp1 & 0xf0000000;
      res = tmp2 ? (tmp1 ^ (tmp2 >> 28)) : tmp1;
    }

  return res;
}

/*------------------------------------------------------------------------*/
static unsigned hash(Node * a)
{
  unsigned res, tmp;

  res = ((unsigned)ATOM) * 999983;

  if(a -> tag == ATOM) tmp = hash_string((char*) car(a));
  else tmp = (unsigned) car(a);

  res += tmp * 3999971;
  res += ((unsigned)cdr(a)) * 9973;

  return res;
}

/*------------------------------------------------------------------------*/

static void resize(unsigned new_size)
{
  Node ** old_nodes, * p, * tmp;
  unsigned old_size, i, h;

  old_nodes = nodes;
  old_size = size_nodes;

  size_nodes = next_prime(new_size);
  nodes = (Node**) calloc(size_nodes, sizeof(Node*));

  for(i = 0; i < old_size; i++)
    for(p = old_nodes[i]; p; p = tmp)
      {
        tmp = p -> next;
	h = hash(p) % size_nodes;
	p -> next = nodes[h];
	nodes[h] = p;
      }
  
  free(old_nodes);
}

/*------------------------------------------------------------------------*/

static int eq(Node * a, Node * b)
{
  int res;

  if(a -> tag == b -> tag)
    {
      if(a -> tag == ATOM) res = (strcmp((char*)car(a), (char*)car(b)) == 0);
      else res = (car(a) == car(b) && cdr(a) == cdr(b));
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node ** find(Node * node)
{
  unsigned h;
  Node ** p;

  searched++;

  h = hash(node) % size_nodes;
  for(p = &nodes[h]; *p && !eq(*p, node); p = &(*p) -> next)
    visited++;
  
  return p;
}

/*------------------------------------------------------------------------*/

static void set_Node(Node * node, int tag, Node * head, Node * tail)
{
  unsigned cn, ct;

  node -> tag = tag;
  node -> head = head;
  node -> tail = tail;

  switch(tag)
    {
      case ATOM:
      case NUMBER:
      case ACCESS:
      case AT:
      case BOOLEAN:
        cn = 0;
	ct = 0;
	break;
      
      case NEXT:
        cn = 1;
	ct = 1;
	break;
      
      default:

	cn =
	  (head && head -> contains_next) ||
	  (tail && tail -> contains_next);

        switch(tag)
	  {
	    case AG:
	    case AF:
	    case AX:
	    case AU:
	    case EG:
	    case EF:
	    case EX:
	    case EU:
	    case MIN:
	    case MAX:
	      ct = 1;
	      break;
	    
	    default:
	      ct = 
		(head && head -> contains_temporal_operator) ||
		(tail && tail -> contains_temporal_operator);
	      break;
	  }
    }

  node -> contains_next = cn;
  node -> contains_temporal_operator = ct;
}

/*------------------------------------------------------------------------*/
/* We eat references of head and tail ...
 */
Node * new(int tag, Node * head, Node * tail)
{
  Node * res, ** p, tmp, * new_head, * new_tail;

  switch(tag)
    {
      case INVAR:
      case INIT:
      case TRANS:
	if(head -> tag == NEXT && !is_atom(car(head)))
	  {
	    new_head = add_next_in_front_of_atoms(car(head));
	    delete(head);
	  }
	else new_head = head;
	new_tail = 0;
        break;

      case INITASSIGNMENT:
      case TRANSASSIGNMENT:
      case INVARASSIGNMENT:
      case DEFINEASSIGNMENT:
	if(tail -> tag == NEXT && !is_atom(car(tail)))
	  {
	    new_tail = add_next_in_front_of_atoms(car(tail));
	    delete(tail);
	  }
	else new_tail = tail;
	new_head = head;
        break;

      default:
	new_head = head;
	new_tail = tail;
	break;
    }

  if(num_nodes >= 2 * size_nodes) resize(2 * num_nodes);

  set_Node(&tmp, tag, new_head, new_tail);
  p = find(&tmp);

  if(*p) 
    {
      switch(tag)
        {
	  case NUMBER:
	  case ATOM:
	    break;
	  
	  default:
	    delete(new_head);
	    break;
	}
      
      delete(new_tail);

      res = *p;
      res -> ref++;
    }
  else
    {
      res = (Node*) malloc(sizeof(Node));
      set_Node(res, tag, new_head, new_tail);
      if(tag == ATOM) res -> head = (Node*) strdup((char*) new_head);
      res -> ref = 1;
      res -> age = nodes_generated++;
      assert(nodes_generated);
      res -> next = 0;
      num_nodes++;
      if(num_nodes > max_nodes) max_nodes = num_nodes;
      *p = res;
    }

  return res;
}

/*------------------------------------------------------------------------*/

static Node * simp_cases_merge_RHS(Node * cases)
{
  Node * one_case, * next_case, * merged_cond, * res, * tmp, * next;
  Node * cond, * next_cond, * val, * next_val, * new_case, * p;

  if(cases)
    {
      p = cases;

      one_case = car(p);
      cond = car(one_case);
      val = cdr(one_case);

      merged_cond = copy(cond);

      /* Merge sequence of cases with same RHS.
       */
      while((next = cdr(p)) && 
	    (next_case = car(next)) &&		/* should always be true */
	    (next_val = cdr(next_case)) &&	/* should always be true */
	    (next_val == val))
        {
	  next_cond = car(next_case);
	  merged_cond = new_simplify(OR, merged_cond, copy(next_cond));
	  p = next;
	}
      
      tmp = simp_cases_merge_RHS(next);
      new_case = new(COLON, merged_cond, copy(val));
      res = cons(new_case, tmp);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static int contains_tagged(int tag, Node * node, Node * b)
{
  int res;

  assert(b);
  assert(b -> tag != tag);

  if(node)
    {
      if(node -> tag == tag)
        {
	  res = contains_tagged(tag, car(node), b);
	  if(!res) res = contains_tagged(tag, cdr(node), b);
	}
      else res = (node == b);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * divide_common(int tag, Node * a, Node * b)
{
  Node * res, * l, * r;

  if(a)
    {
      if(a -> tag == tag)
        {
	  l = divide_common(tag, car(a), b);
	  r = divide_common(tag, cdr(a), b);

	  if(l && r) res = new_simplify(tag, l, r);
	  else res = l ? l : r;
	}
      else
        {
	  if(contains_tagged(tag, b, a)) res = 0;
	  else res = copy(a);
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * factor_common(int tag, Node * a, Node * b)
{
  Node * res, * l, * r;

  assert(tag == OR || tag == AND);

  if(a)
    {
      if(a -> tag == tag)
        {
	  l = factor_common(tag, car(a), b);
	  r = factor_common(tag, cdr(a), b);

	  if(l && r) res = new_simplify(tag, l, r);
	  else res = l ? l : r;
	}
      else
        {
	  if(contains_tagged(tag, b, a)) res = copy(a);
	  else res = 0;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * simp_cases_divide_cond(Node * cases, Node * divisor)
{
  Node * simp_cond, * cond, * val, * tmp, * res, * one_case;
  Node * new_case, * factor;

  if(cases)
    {
      one_case = car(cases);
      cond = car(one_case);
      val = cdr(one_case);

      /* First divide condition by divisor ...
       */
      factor = factor_common(AND, cond, divisor);
      if(factor)
        {
	  simp_cond = divide_common(AND, cond, factor);
	  if(!simp_cond) simp_cond = number(1);
	}
      else simp_cond = copy(cond);
      delete(factor);
      
      if(is_false(simp_cond))
        {
	  delete(simp_cond);
	  res = simp_cases_divide_cond(cdr(cases), divisor);
	}
      else
      if(is_true(simp_cond))
        {
	  new_case = new(COLON, simp_cond, copy(val));
	  res = new(LIST, new_case, 0);
	}
      else
        {
	  tmp = simp_cases_divide_cond(cdr(cases), divisor);
	  new_case = new(COLON, simp_cond, copy(val));
	  res = new(LIST, new_case, tmp);
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * simp_cases_remove_subsumed_cond(Node * cases)
{
  Node * res, * one_case, * cond, * new_case, * new_other_cases, * neg_cond;
  Node * val, * tmp;

  if(cases)
    {
      one_case = car(cases);
      cond = car(one_case);
      val = cdr(one_case);

      if(is_false(cond)) res = simp_cases_remove_subsumed_cond(cdr(cases));
      else 
      if(is_true(cond)) 
        {
	  new_case = new(COLON, copy(cond), copy(val));
	  res = new(LIST, new_case, 0);
	}
      else
        {
	  /* Quadratic algorithm in the number of cases ...
	   */
	  neg_cond = new_simplify(NOT, copy(cond), 0);
	  tmp = simp_cases_divide_cond(cdr(cases), neg_cond);
	  delete(neg_cond);
	  new_other_cases = simp_cases_remove_subsumed_cond(tmp);
	  delete(tmp);
	  res = new(LIST, copy(one_case), new_other_cases);
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * encode_cases(Node * cases)
{
  Node * cond, * other_cond, * one_case, * p, * res, * tmp, * implication;
  Node * not_cond;

  for(res = 0, p = cases, other_cond = number(1); p; p = cdr(p))
    {
      one_case = car(p);
      cond = new_simplify(AND, copy(other_cond), copy(car(one_case)));
      implication = new_simplify(IMPLIES, cond, copy(cdr(one_case)));

      if(res) res = new_simplify(AND, res, implication);
      else res = implication;

      tmp = other_cond;
      not_cond = new_simplify(NOT, copy(car(one_case)), 0);
      other_cond = new_simplify(AND, copy(other_cond), not_cond);
      delete(tmp);
    }
  
  delete(other_cond);
  
  return res;
}

/*------------------------------------------------------------------------*/

static void get_factors(int tag, Assoc * assoc, Node * node)
{
  if(node -> tag == tag)
    {
      get_factors(tag, assoc, car(node));
      get_factors(tag, assoc, cdr(node));
    }
  else associate(assoc, node, (void*) 1);
}

/*------------------------------------------------------------------------*/

static Node * ns(int tag, Node * head, Node * tail);

/*------------------------------------------------------------------------*/

static Node * rs(Assoc * assoc, int tag, int outer_tag, Node * node)
{
  Node * res, * a, * b, * tmp;
  int inner_tag;

  if(node -> tag == tag)
    {
      a = rs(assoc, tag, tag, car(node));
      b = rs(assoc, tag, tag, cdr(node));
      res = ns(tag, a, b);
    }
  else
    {
      inner_tag = (tag == AND) ? OR : AND;
      if(node -> tag == inner_tag)
        {
	  a = rs(assoc, tag, inner_tag, car(node));
	  b = rs(assoc, tag, inner_tag, cdr(node));
	  res = ns(inner_tag, a, b);
	}
      else
        {
	  if(outer_tag == inner_tag)
	    {
	      tmp = ns(NOT, copy(node), 0);
	      if(is_associated(assoc, tmp))
		{
		  /*  !a | (a & b)  <->  !a | (1 & b)
		   */
		  res = number((inner_tag == AND) ? 1 : 0);
		}
	      else
	      if(is_associated(assoc, node))
	        {
		  /*  a | (a & b)  <->  a | (0 & b)
		   */
		  res = number((inner_tag == AND) ? 0 : 1);
		}
	      else res = copy(node);
	      delete(tmp);
	    }
	  else res = copy(node);
	}
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static Node * remove_subsumed(Node * node)
{
  Assoc * assoc;
  Node * res;

  if(node && (node -> tag == AND || node -> tag == OR))
    {
      assoc = new_Assoc();
      get_factors(node -> tag, assoc, node);
      res = rs(assoc, node -> tag, node -> tag, node);
      delete_Assoc(assoc);
    }
  else res = copy(node);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * neg_cases(Node * cases)
{
  Node * res, * c, * lhs, * rhs, * new_lhs, * new_rhs, * new_case, * tmp;

  if(cases)
    {
      c = car(cases);
      assert(c -> tag == COLON);
      lhs = car(c);
      rhs = cdr(c);
      new_lhs = copy(lhs);
      new_rhs = new_simplify(NOT, copy(rhs), 0);
      new_case = new(COLON, new_lhs, new_rhs);
      tmp = neg_cases(cdr(cases));
      res = cons(new_case, tmp);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static double simplify_limit = 10000000;

/*------------------------------------------------------------------------*/

static void inc_simplify_calls(void)
{
  if(simplify_calls >= simplify_limit) 
    {
      fprintf(
        stderr,
	"*** smvflatten: simplify limit of %.0f reached\n",
	simplify_limit);

      if(simplification_level)
	{
	  fprintf(
	    stderr,
	    "*** (decrement simplification level with `-simp<n>')\n");
	}
      else 
	{
	  fprintf(
	    stderr,
	    "*** (recompile with larger `simplify_limit' in `node.c')\n");
	}

      exit(1);
    }

  simplify_calls++;
}

/*------------------------------------------------------------------------*/

static Node * ns(int tag, Node * head, Node * tail)
{
  Node * res, * new_cases, * a, * b, * tmp, * l, * r, * f;
  Node * first_case, * cond, * value, * neg_value;
  unsigned len;

  inc_simplify_calls();

  /* Sort the arguments for commutative operators.
   */
  if((tag == AND || tag == OR || tag == IFF) && cmp_Node(head, tail) > 0)
    {
      tmp = head;
      head = tail;
      tail = tmp;
    }

  /* If a simplification is possible `res' will become non zero.
   * Only the list case has to be handled differently.
   */
  res = 0;

  switch(tag)
    {
      case NOT:

        if(head -> tag == NOT) res = copy(car(head));
	else if(is_true(head)) res = number(0);
	else if(is_false(head)) res = number(1);
	else if(is_atom(head) || head -> tag == NEXT)
	  {
	    res = new(NOT, copy(head), 0);
	  }
	else
	if(enable_nnf)
	  {
	    /* Force NNF of all simplified terms.
	     */
	    res = get_association(negation_cache, head);

	    if(res) res = copy(res);
	    else
	      {
		switch(head -> tag)
		  {
		    case AND:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      r = new_simplify(NOT, copy(cdr(head)), 0);
		      res = new_simplify(OR, l, r);
		      break;

		    case OR:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      r = new_simplify(NOT, copy(cdr(head)), 0);
		      res = new_simplify(AND, l, r);
		      break;
		    
		    case IFF:
		      l = copy(car(head));
		      r = new_simplify(NOT, copy(cdr(head)), 0);
		      res = new_simplify(IFF, l, r);
		      break;
		    
		    case CASE:
		      new_cases = neg_cases(car(head));
		      res = new_simplify(CASE, new_cases, 0);
		      break;

		    case AF:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(EG, l, 0);
		      break;
		    
		    case AG:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(EF, l, 0);
		      break;
		    
		    case AX:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(EX, l, 0);
		      break;
		    
		    case AU:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(EU, l, 0);
		      break;
		    
		    case EF:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(AG, l, 0);
		      break;
		    
		    case EG:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(AF, l, 0);
		      break;
		    
		    case EX:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(AX, l, 0);
		      break;
		    
		    case EU:
		      l = new_simplify(NOT, copy(car(head)), 0);
		      res = new_simplify(AU, l, 0);
		      break;
		    
		    default:
		      assert(0);
		      res = new(NOT, copy(head), 0);
		      break;
		  }
		
		assert(!is_associated(negation_cache, head));

		tmp = get_association(negation_cache, res);

		if(tmp)
		  {
		    assert(get_association(negation_cache,  tmp) == res);

		    deassociate(negation_cache, tmp);
		    deassociate(negation_cache, res);
		  }

		associate(negation_cache, head, res);
		associate(negation_cache, res, head);
	      }
	  }
	else
	if((head -> tag == OR || head -> tag == AND || head -> tag == IFF) &&
	   (car(head) -> tag == NOT || cdr(head) -> tag == NOT))
	  {
	    /* Use DeMorgan's Law to reduce number of Not's
	     */
	    switch(head -> tag)
	      {
	        case OR:
		  a = new_simplify(NOT, copy(car(head)), 0);
		  b = new_simplify(NOT, copy(cdr(head)), 0);
		  res = new_simplify(AND, a, b);
		  break;

		case AND:
		  a = new_simplify(NOT, copy(car(head)), 0);
		  b = new_simplify(NOT, copy(cdr(head)), 0);
		  res = new_simplify(OR, a, b);
		  break;

		case IFF:
		  if(car(head) -> tag == NOT)
		    {
		      a = new_simplify(NOT, copy(car(head)), 0);
		      b = copy(cdr(head));
		    }
		  else
		    {
		      a = copy(car(head));
		      b = new_simplify(NOT, copy(cdr(head)), 0);
		    }
		  res = new_simplify(IFF, a, b);
		  break;

		default:
		  res = 0;
		  break;
	      }
	  }
        break;
      
      case AND:
        if(is_false(head) || is_false(tail)) res = number(0);
	else if(is_true(head)) res = copy(tail);
	else if(is_true(tail)) res = copy(head);
	else if(head == tail) res = copy(tail);
	else if(is_negation(head, tail)) res = number(0);
	else
	if(head -> tag == OR && tail -> tag == OR &&
	   (
	     (
	       is_negation(car(head), car(tail)) &&
	       is_negation(cdr(head), cdr(tail))
	     )
	     ||
	     (
	       is_negation(car(head), cdr(tail)) &&
	       is_negation(cdr(head), car(tail))
	     )
	    )
	  )
	  {
	    res = new_simplify(IFF, copy(car(head)), copy(cdr(head)));
	    res = new_simplify(NOT, res, 0);
	  }
	else
	if(simplification_level >= 2)
	  {
	    f = factor_common(OR, head, tail);
	    if(f)
	      {
	        l = divide_common(OR, head, f);
	        r = divide_common(OR, tail, f);

		if(!l) l = number(0);
		if(!r) r = number(0);

	        res = new_simplify(OR, f, new_simplify(AND, l, r));
	      }
	  }
        break;
      
      case OR:
        if(is_true(head) || is_true(tail)) res = number(1);
	else if(is_false(head)) res = copy(tail);
	else if(is_false(tail)) res = copy(head);
	else if(head == tail) res = copy(tail);
	else if(is_negation(head, tail)) res = number(1);
	else
	if(head -> tag == AND && tail -> tag == AND &&
	   (
	     (
	       is_negation(car(head), car(tail)) &&
	       is_negation(cdr(head), cdr(tail))
	     )
	     ||
	     (
	       is_negation(car(head), cdr(tail)) &&
	       is_negation(cdr(head), car(tail))
	     )
	    )
	  )
	  {
	    res = new_simplify(IFF, copy(car(head)), copy(cdr(head)));
	  }
	else
	if(simplification_level >= 2)
	  {
	    f = factor_common(AND, head, tail);
	    if(f)
	      {
	        l = divide_common(AND, head, f);
	        r = divide_common(AND, tail, f);

		if(!l) l = number(1);
		if(!r) r = number(1);

	        res = new_simplify(AND, f, new_simplify(OR, l, r));
	      }
	  }
        break;

      case IFF:
        if(is_true(head)) res = copy(tail);
	else if(is_true(tail)) res = copy(head);
	else if(is_false(head)) res = new_simplify(NOT, copy(tail), 0);
	else if(is_false(tail)) res = new_simplify(NOT, copy(head), 0);
	else if(head == tail) res = number(1);
	else if(is_negation(head, tail)) res = number(0);
	else if(head -> tag == NOT && tail -> tag == NOT)
	  {
	    res = new_simplify(IFF, copy(car(head)), copy(car(tail)));
	  }
        break;
      
      case CASE:

	assert(head);

	first_case = car(head);
	cond = car(first_case);
	value = cdr(first_case);
	neg_value = new_simplify(NOT, copy(value), 0);

	if(is_constant(value) || (value == cond) || (neg_value == cond))
	  {
	    /* We can strip the first case if the RHS of the first case is a
	     * constant or the RHS is the LHS or its negation.
	     */
	    if(is_false(value) || (neg_value == cond))
	      {
	         /* case a : 0; ... esac == !a & case ... esac
		  */
		l = new_simplify(NOT, copy(cond), 0);
		if(cdr(head)) r = new_simplify(CASE, copy(cdr(head)), 0);
		else r = number(1);
		res = new_simplify(AND, l, r);
	      }
	    else
	      {
	        assert(is_true(value) || (value == cond));

	         /* case a : 1; ... esac == a | case ... esac
		  */
		l = copy(cond);
		if(cdr(head)) r = new_simplify(CASE, copy(cdr(head)), 0);
		else r = number(0);
		res = new_simplify(OR, l, r);
	      }
	  }
	else
	  {
	    if(simplification_level >= 3)
	      {
		new_cases = simp_cases_remove_subsumed_cond(head);
		delete(head);
		head = new_cases;
	      }

	    if(simplification_level >= 3)
	      {
		new_cases = simp_cases_merge_RHS(head);
		delete(head);
		head = new_cases;
	      }

	    if(is_true(car(car(head)))) res = copy(cdr(car(head)));
	    else if((len = length(head)) <= 3) res = encode_cases(head);
	  }

	delete(neg_value);
        break;
      
      /* Remove implications for simplification of `new_simplify' ;-)
       */
      case IMPLIES:
	res = new_simplify(OR, new_simplify(NOT, copy(head), 0), copy(tail));
	break;

      default:
	break;
    }

  if(res)
    {
      switch(tag)
        {
	  case NUMBER:
	    break;

	  default:
	    delete(head);
	    delete(tail);
	    break;
	  
	  case ATOM:
	  case ACCESS:
	    assert(0);
	    break;
	}
    }
  else res = new(tag, head, tail);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * rd(int tag, Assoc * assoc, Node * node)
{
  Node * res, * a, * b, * tmp; 

  assert(tag == AND || tag == OR);

  if(node -> tag == tag)
    {
      a = rd(tag, assoc, car(node));
      b = rd(tag, assoc, cdr(node));
      res = ns(tag, a, b);
    }
  else
  if(is_associated(assoc, node))
    {
      /* a | b | a  == a | b | 0  == a | b
       */
      res = number((tag == OR) ? 0 : 1);
    }
  else
    {
      tmp = ns(NOT, copy(node), 0);

      if(is_associated(assoc, tmp))
	{
	  /* a | b | !a  == a | b | 1  == 1
	   */
	  res = number((tag == OR) ? 1 : 0);
	}
      else 
        {
	  associate(assoc, node, node);
	  res = copy(node);
	}

      delete(tmp);
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static Node * remove_duplicates(Node * node)
{
  Assoc * assoc;
  Node * res;

  if(node && (node -> tag == OR || node -> tag == AND))
    {
      assoc = new_Assoc();
      res = rd(node -> tag, assoc, node);
      delete_Assoc(assoc);
    }
  else res = copy(node);

  return res;
}

/*------------------------------------------------------------------------*/

Node * add_next_in_front_of_atoms(Node * node)
{
  Node * res, * a, * b;
  int tag;

  if(node)
    {
      switch((tag = node -> tag))
	{
	  case AT:
	  case ACCESS:
	  case NUMBER:
	  case ATOM:
	    res = new(NEXT, copy(node), 0);
	    break;
	  
	  default:
	    a = add_next_in_front_of_atoms(car(node));
	    b = add_next_in_front_of_atoms(cdr(node));
	    res = new(tag, a, b);	/* Do not use new_simplify here !!  */
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

Node * new_simplify(int tag, Node * head, Node * tail)
{
  Node * res, * tmp, * new_head, * new_tail;

  if(!simplification_level) res = new(tag, head, tail);
  else
  if(tag == LIST &&
     head &&
     is_true(car(head)) &&
     (head -> tag == INVAR || 
      head -> tag == SPEC ||
      head -> tag == TRANS ||
      head -> tag == INIT))
    {
      inc_simplify_calls();
      delete(head);
      res = tail;
    }
  else
  if(tag == NOT && head -> tag == NEXT)
    {
      /* Pull out `NEXT'
       */
      tmp = new_simplify(NOT, copy(car(head)), 0);
      delete(head);
      res = new(NEXT, tmp, 0);
    }
  else
  if(head && head -> tag == NEXT && 
     tail && tail -> tag == NEXT)
    {
      /* Pull out `NEXT'
       */
      tmp = new_simplify(tag, copy(car(head)), copy(car(tail)));
      delete(head);
      delete(tail);
      res = new(NEXT, tmp, 0);
    }
  else
    {
      if(head && head -> tag == NEXT && !is_atom(car(head)))
        {
	  /* Push in `NEXT'
	   */
	  new_head = add_next_in_front_of_atoms(car(head));
	  delete(head);
	}
      else new_head = head;

      if(tail && tail -> tag == NEXT && !is_atom(car(tail)))
        {
	  /* Push in `NEXT'
	   */
	  new_tail = add_next_in_front_of_atoms(car(tail));
	  delete(tail);
	}
      else new_tail = tail;

      res = ns(tag, new_head, new_tail);

      if(simplification_level >= 5)
        {
	  /* Unfortunately it turns out to be too expensive to perform
	   * subsumtption removal for every node during simplification for
	   * large examples because to do it in the construction of every
	   * node induces a quadractic time overhead.
	   *
	   * TODO: Make subsumption removal a seperate phase before
	   * extraction of macros.
	   */
	  tmp = res;
	  res = remove_subsumed(tmp);

#         if 0
	  if(tmp != res)
	    {
	      fputs("REMOVE_SUBSUMED\n", stderr);
	      print(stderr, tmp);
	      fputc('\n', stderr);
	      fputs("--->\n", stderr);
	      print(stderr, res);
	      fputc('\n', stderr);
	      fflush(stderr);
	    }
#         endif

	  delete(tmp);
	}
      
      if(simplification_level >= 4)
        {
	  /* The same comment as above.
	   *
	   * TODO: Make duplicate removal a seperate phase.
	   */
	  tmp = res;
	  res = remove_duplicates(tmp);

#         if 0
	  if(tmp != res)
	    {
	      fputs("REMOVE_DUPLICATES\n", stderr);
	      print(stderr, tmp);
	      fputc('\n', stderr);
	      fputs("--->\n", stderr);
	      print(stderr, res);
	      fputc('\n', stderr);
	      fflush(stderr);
	    }
#         endif

	  delete(tmp);
	}
    }

  return res;
}

/*------------------------------------------------------------------------*/

static void delete_aux(Node * node)
{
  Node ** p, * head, * tail;
  unsigned h;
  int tag;

  assert(node);
  assert(num_nodes);
  assert(!enable_nnf || !is_associated(negation_cache, node));

  /* First dequeue it from the unique table.
   */
  h = hash(node) % size_nodes;
  for(p = &nodes[h]; *p && *p != node; p = &(*p) -> next)
    ;
  assert(*p);
  *p = node -> next;

  /* Release the memory of this node and save references to subnodes
   * or data and the tag.
   */
  tag = node -> tag;
  head = car(node);
  tail = cdr(node);
  free(node);
  num_nodes--;

  /* Now dereference sub nodes.
   */
  switch(tag)
    {
      case ATOM:
	free((char*) head);
	break;
      
      case NUMBER:
      case BOOLEAN:
	break;

      default:
        delete(head);
        delete(tail);
	break;
    }
}

/*------------------------------------------------------------------------*/

void delete(Node * node)
{
  Node * neg_node;

  if(node)
    {
      if(node -> ref == 1)
        {
	  if(enable_nnf && (neg_node = get_association(negation_cache, node)))
	    {
	      assert(node == get_association(negation_cache, neg_node));

	      deassociate(negation_cache, node);
	      deassociate(negation_cache, neg_node);
	    }

	  delete_aux(node);
	}
      else node -> ref--;
  }
}

/*------------------------------------------------------------------------*/

Node * copy(Node * node)
{
  if(node)
    {
      assert(node -> ref);

      node -> ref++;

      assert(node -> ref);
    }

  return node;
}

/*------------------------------------------------------------------------*/

Node * car(Node * node)
{ 
  assert(node);

  return node -> head;
}

/*------------------------------------------------------------------------*/

Node * cdr(Node * node)
{ 
  assert(node);

  return node -> tail;
}

/*------------------------------------------------------------------------*/

Node * cons(Node * head, Node * tail)
{ 
  return new(LIST, head, tail);
}

/*------------------------------------------------------------------------*/

Node * atom(const char * str)
{
  Node * res;

  res = new(ATOM, (Node*) str, 0);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * gensym(const char * prefix)
{
  Node * res, ** p, tmp;
  char * buffer;

  buffer = (char*) malloc(strlen(prefix) + 21);
  res = 0;

  do {
    sprintf(buffer, "%s%0u", prefix, gensym_counter++);
    set_Node(&tmp, ATOM, (Node*) buffer, 0);
    p = find(&tmp);
    if(!*p) res = atom(buffer);
  } while(!res);

  assert(!is_associated(oracles, res));
  associate(oracles, copy(res), (void*)1);

  free(buffer);

  return res;
}

/*------------------------------------------------------------------------*/

Node * new_oracle(void)
{
  Node * res;

  res = gensym("ORACLE");

  return res;
}

/*------------------------------------------------------------------------*/

Node * new_running(void)
{
  Node * res;

  res = gensym("RUNNING");

  return res;
}

/*------------------------------------------------------------------------*/

Node * new_macro(void)
{
  Node * res;

  res = gensym("MACRO");

  return res;
}

/*------------------------------------------------------------------------*/

Node * number(int n)
{
  return new(NUMBER, (Node*) n, 0);
}

/*------------------------------------------------------------------------*/

unsigned length(Node * node)
{
  Node * p;
  int res;

  if(node)
    {
      if(node -> tag == ACCESS || 
         node -> tag == AT || 
         node -> tag == LIST)
        {
	  for(res = 1, p = cdr(node); p; p = cdr(p))
	    res++;
	}
      else res = 1;
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

Node * append(Node * h, Node * r)
{
  Node * res, * tmp;
  
  if(h)
    {
      assert(h -> tag == LIST || h -> tag == ACCESS || h -> tag == AT);

      if(r)
        {
	  switch(r -> tag)
	    {
	      case LIST:
	      case ACCESS:
	      case AT:
		tmp = append(cdr(h), r);
		res = new(h -> tag, copy(car(h)), tmp);
		break;
	      
	      default:
	        tmp = new(h -> tag, copy(r), 0);
		res = append(h, tmp);
		delete(tmp);
	        break;
	    }
	}
      else res = copy(h);
    }
  else res = copy(r);

  return res;
}

/*------------------------------------------------------------------------*/

Node * append_tagged(int tag, Node * head, Node * rest)
{
  Node * res, * tmp;

  assert(tag == LIST || tag == ACCESS);

  if(head)
    {
      if(head -> tag == tag) res = append(head, rest);
      else
        {
	  tmp = new(tag, copy(head), 0);
	  res = append(tmp, rest);
	  delete(tmp);
	}
    }
  else res = copy(rest);

  return res;
}

/*------------------------------------------------------------------------*/

Node * reverse(Node * node)
{
  Node * res, * p;

  for(res = 0, p = node; p; p = cdr(p))
    {
      assert(p -> tag == LIST || p -> tag == ACCESS);
      res = cons(copy(car(p)), res);
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

Node * get_last(Node * node)
{
  Node * res, * p;

  assert(node);
  assert(node -> tag == LIST);

  for(p = node, res = 0; p; p = cdr(p))
    res = car(p);

  return res;
}

/*------------------------------------------------------------------------*/

int is_oracle(Node * node)
{
  return is_associated(oracles, node);
}

/*------------------------------------------------------------------------*/

static Node * subst(Node * node, Assoc * cache)
{
  Node * res, * a, * b;

  if(node)
    {
      res = (Node*) get_association(cache, node);
      if(res) res = copy(res);
      else
	{
	  switch(node -> tag)
	    {
	      case NUMBER:
	      case BOOLEAN:
	      case ATOM:
		res = copy(node);
		break;
	      
	      default:
		a = subst(car(node), cache);
		b = subst(cdr(node), cache);
		res = new(node -> tag, a, b);
		associate(cache, node, copy(res));
		break;
	    }
	}
    }
  else res = 0;
  
  return res;
}

/*------------------------------------------------------------------------*/

Node * substitute(Node * node, Assoc * s)
{
  Assoc * cache;
  Node * res;

  cache = new_Assoc();
  map_Assoc(s, cache, (void(*)(void*,void*,void*)) &associate);
  forall_dst_in_Assoc(cache, (void(*)(void*))copy);
  res = subst(node, cache);
  forall_dst_in_Assoc(cache, (void(*)(void*))delete);
  delete_Assoc(cache);

  return res;
}

/*------------------------------------------------------------------------*/

Node * ite(Node * c, Node * t, Node * e)
{
  Node * res, * first_case, * second_case, * rest, * one, * cases;

  first_case = new(COLON, c, t);

  if(e -> tag == CASE) 
    {
      rest = copy(car(e));
      delete(e);
    }
  else 
    {
      one = new(NUMBER, (Node*) 1, 0);
      second_case = new(COLON, one, e);
      rest = new(LIST, second_case, 0);
    }

  cases = new(LIST, first_case, rest);
  res = new(CASE, cases, 0);

  return res;
}

/*------------------------------------------------------------------------*/

Node * ite_simplify(Node * c, Node * t, Node * e)
{
  Node * res, * first_case, * second_case, * rest, * one, * cases;

  if(!simplification_level)
    {
      res = ite(c, t, e);
    }
  else
  if(is_true(c)) 
    {
      res = t;
      delete(c);
      delete(e);
    }
  else
  if(is_false(c))
    {
      res = e;
      delete(c);
      delete(t);
    }
  else
  if(t == e)
    {
      res = t;
      delete(c);
      delete(e);
    }
  else
  if(is_negation(t, e))
    {
      res = new_simplify(IFF, c, t);
      delete(e);
    }
  else
    {
      first_case = new(COLON, c, t);

      if(e -> tag == CASE) 
	{
	  rest = copy(car(e));
	  delete(e);
	}
      else 
	{
	  one = new(NUMBER, (Node*) 1, 0);
	  second_case = new(COLON, one, e);
	  rest = new(LIST, second_case, 0);
	}

      cases = new(LIST, first_case, rest);
      res = new_simplify(CASE, cases, 0);
    }

  return res;
}

/*------------------------------------------------------------------------*/

int is_member(Node * l, Node * m)
{
  Node * p;
  int res;

  for(p = l, res = 0; !res && p; p = cdr(p))
    res = (car(p) == m);

  return res;
}

/*------------------------------------------------------------------------*/

unsigned get_position(Node * l, Node * m)
{
  unsigned res;
  Node * p;

  for(p = l, res = 0; p && car(p) != m; p = cdr(p), res++)
    ;
  
  return res;
}

/*------------------------------------------------------------------------*/

int is_true(Node * n)
{
  int res;

  res = (n && n -> tag == NUMBER && 1 == (int) car(n));

  return res;
}

/*------------------------------------------------------------------------*/

int is_false(Node * n)
{
  int res;

  res = (n && n -> tag == NUMBER && 0 == (int) car(n));

  return res;
}

/*------------------------------------------------------------------------*/

int is_constant(Node * n)
{
  return is_false(n) || is_true(n);
}

/*------------------------------------------------------------------------*/

int is_atom(Node * n)
{
  int res;

  if(n)
    {
      switch(n -> tag)
        {
	  case ATOM:
	  case ACCESS:
	  case AT:
	    res = 1;
	    break;

	  default:
	    res = 0;
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

int is_literal(Node * n)
{
  int res;

  if(n)
    {
      if(n -> tag == NOT) res = is_atom(car(n));
      else res = is_atom(n);
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

int is_clause(Node * n)
{
  int res;

  if(n)
    {
      switch(n -> tag)
        {
	  case AND:
	  case OR:
	  case IMPLIES:
	  case IFF:
	    res = (is_literal(car(n)) && is_literal(cdr(n)));
	    break;
	  
	  default:
	    res = is_literal(n);
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static Node * strip_at_aux(Node * n)
{
  Node * res, * tmp;

  if(n)
    {
      switch(n -> tag)
        {
	  case ATOM:
	    res = copy(n);
	    break;
	  
	  case AT:
	    res = 0;
	    break;
	  
	  case ACCESS:
	    tmp = strip_at_aux(cdr(n));
	    res = new(ACCESS, copy(car(n)), tmp);
	    break;

	  default:
	    res = 0;
	    assert(0);
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

Node * strip_at(Node * n)
{
  Node * res, * tmp;

  tmp = strip_at_aux(n);
  if(tmp)
    {
      if(tmp -> tag == ACCESS && !cdr(tmp)) 
        {
	  res = copy(car(tmp));
	  delete(tmp);
	}
      else res = tmp;
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static int is_negation_aux(Node * a, Node * b)
{
  int res;

  if(a -> tag == NOT) res = (car(a) == b);
  else if(b -> tag == NOT) res = (car(b) == a);
  else if(enable_nnf) res = (get_association(negation_cache, a) == b);
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

int is_negation(Node * a, Node * b)
{
  int res;

  if(!a || !b || a == b) res = 0;
  else
  if(is_negation_aux(a, b)) res = 1;
  else 
  if((a -> tag == OR && b -> tag == AND) ||	/* De'Morgan */
     (a -> tag == AND && b -> tag == OR))
    {
      res = 
        (is_negation_aux(car(a), car(b)) && is_negation_aux(cdr(a), cdr(b)))
	||
        (is_negation_aux(car(a), cdr(b)) && is_negation_aux(cdr(a), car(b)))
	;
    }
  else
  if(a -> tag == IFF && b -> tag == IFF)
    {
      if(car(a) == car(b)) res = is_negation_aux(cdr(a), cdr(b));
      else if(car(a) == cdr(b)) res = is_negation_aux(cdr(a), car(b));
      else if(cdr(a) == car(b)) res = is_negation_aux(car(a), cdr(b));
      else if(cdr(a) == cdr(b)) res = is_negation_aux(car(a), car(b));
      else res = 0;
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

int cmp_Node(Node * a, Node * b)
{
  int l, r, res;
  
  if(a == b) res = 0;
  else
  if(!a) res = -1;
  else
  if(!b) res = 1;
  else
  if(a -> tag == NOT)	/* ... strip 'NOT' in comparison */
    {
      res = cmp_Node(car(a), b);
    }
  else
  if(b -> tag == NOT)	/* ... strip 'NOT' in comparison */
    {
      res = cmp_Node(a, car(b));
    }
  else
  if(a -> tag == NEXT && b -> tag == NEXT)
    {
      res = cmp_Node(car(a), car(b));	/* strip 'NEXT' for comparison */
    }
  else
    {
      if(a -> tag == NUMBER)		/* Numbers are the smallest terms */
	{
	  if(b -> tag == NUMBER)
	    {
	      l = (int) car(a);
	      r = (int) car(b);

	      res = (l < r) ? -1 : 1;
	    }
	  else res = -1;
	}
      else
      if(b -> tag == NUMBER)
	{
	  res = 1;
	}
      else
      if(a -> tag == ATOM)	/* ... followed by constants and atoms */
	{
	  /* Be sure not to use the `age' of a node for constants.
	   */
	  if(b -> tag == ATOM) res = strcmp((char*) car(a), (char*) car(b));
	  else res = -1;
	}
      else
      if(a -> tag == AT && b -> tag == AT)
	{
	  l = (int) car(car(a));
	  r = (int) car(car(b));

	  assert(l != r);

	  /* Prefer MSB to be the smaller term.
	   */
	  res = (l < r) ? 1 : -1;
	}
      else
      if(a -> tag == ACCESS && b -> tag == ACCESS)
	{
	  if(car(a) == car(b)) res = cmp_Node(cdr(a), cdr(b));
	  else res = cmp_Node(car(a), car(b));
	}
      else
	{
	  /* Finally use the age of two nodes, which is the number of nodes
	   * already generated before this node is generated.
	   */
	  assert(a -> age != b -> age);

	  res = (a -> age < b -> age) ? -1 : 1;
	}

      /* Exactly syntactical equivalent terms are the same.
       */
      assert(res);
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

unsigned term_size(Node * node)
{
  unsigned res, a, b;

  if(node)
    {
      switch(node -> tag)
        {
	  case ATOM:
	  case BOOLEAN:
	  case NUMBER:
	    res = 1;
	    break;
	  
	  default:
	    a = term_size(car(node));
	    b = term_size(cdr(node));
	    res = a + b;
	    break;
        }
    }
  else res = 0;

  return res;
}

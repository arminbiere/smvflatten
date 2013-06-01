/*------------------------------------------------------------------------*/
/* Copyright 1999-2011 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "node.h"
#include "pp.h"
#include "type.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

/*------------------------------------------------------------------------*/

extern int verbose;

/*------------------------------------------------------------------------*/

typedef struct TfContext TfContext;

/*------------------------------------------------------------------------*/

struct TfContext
{
  Assoc * node2type, * defs, * decls;
};

/*------------------------------------------------------------------------*/

static int min(int a, int b) { return (((a) < (b)) ? (a) : (b)); }
static int max(int a, int b) { return (((a) > (b)) ? (a) : (b)); }

/*------------------------------------------------------------------------*/

unsigned ldceil(unsigned n)
{
  unsigned res;

       if(n <= 0x00000001) res = 0;
  else if(n <= 0x00000002) res = 1;
  else if(n <= 0x00000004) res = 2;
  else if(n <= 0x00000008) res = 3;
  else if(n <= 0x00000010) res = 4;
  else if(n <= 0x00000020) res = 5;
  else if(n <= 0x00000040) res = 6;
  else if(n <= 0x00000080) res = 7;
  else if(n <= 0x00000100) res = 8;
  else if(n <= 0x00000200) res = 9;
  else if(n <= 0x00000400) res = 10;
  else if(n <= 0x00000800) res = 11;
  else if(n <= 0x00001000) res = 12;
  else if(n <= 0x00002000) res = 13;
  else if(n <= 0x00004000) res = 14;
  else if(n <= 0x00008000) res = 15;
  else if(n <= 0x00010000) res = 16;
  else if(n <= 0x00020000) res = 17;
  else if(n <= 0x00040000) res = 18;
  else if(n <= 0x00080000) res = 19;
  else if(n <= 0x00100000) res = 20;
  else if(n <= 0x00200000) res = 21;
  else if(n <= 0x00400000) res = 22;
  else if(n <= 0x00800000) res = 23;
  else if(n <= 0x01000000) res = 24;
  else if(n <= 0x02000000) res = 25;
  else if(n <= 0x04000000) res = 26;
  else if(n <= 0x08000000) res = 27;
  else if(n <= 0x10000000) res = 28;
  else if(n <= 0x20000000) res = 29;
  else if(n <= 0x40000000) res = 30;
  else if(n <= 0x80000000) res = 31;
  else                     res = 32;

  return res;
}

/*------------------------------------------------------------------------*/

unsigned num_bits(Node * node)
{
  unsigned res, w;
  int l, r;

  switch(node -> tag)
    {
      case ENUM:
        w = length(car(node));
        res = ldceil(w);
        break;
      
      case BOOLEAN:
        res = 1;
        break;
      
      case TWODOTS:
        l = (long) car(car(node));
        r = (long) car(cdr(node));
	assert(l <= r);
	w = (long)(r - l + 1);
        res = ldceil(w);
        break;
      
      default:
        assert(0);
	res = 0;
	break;
    }

  return res;
}

/*------------------------------------------------------------------------*/

unsigned size_type(Node * type)
{
  unsigned res;
  int l, r;

  switch(type -> tag)
    {
      case TWODOTS:
      case BOOLEAN:
	range_bounds(type, &l, &r);
	res = (long)(r - l + 1);
	break;
      
      case ENUM:
        res = length(car(type));
	break;
      
      default:
        assert(0);
	res = 0;
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

Node * get_first_type(Node * type)
{
  Node * res;

  switch(type -> tag)
    {
      case BOOLEAN:
        res = number(0);
	break;
      
      case TWODOTS:
        res = copy(car(type));
	break;
      
      case ENUM:
        res = copy(car(car(type)));
        break;
      
      default:
	assert(0);
        res = 0;
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

Node * get_last_type(Node * type)
{
  Node * res;

  switch(type -> tag)
    {
      case BOOLEAN:
        res = number(1);
	break;
      
      case TWODOTS:
        res = copy(cdr(type));
	break;
      
      case ENUM:
        res = copy(get_last(car(type)));
        break;
      
      default:
	assert(0);
        res = 0;
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static int is_number_enumeration(Node * node)
{
  Node * p;
  int res;

  assert(node -> tag == ENUM);

  for(res = 1, p = car(node); res && p; p = cdr(p))
    res = (car(p) -> tag == NUMBER);
  
  return res;
}

/*------------------------------------------------------------------------*/

static int min_number_enumeration(Node * node)
{
  Node * p, * n;
  int res, tmp;

  assert(node -> tag == ENUM);
  assert(car(node));

  p = car(node);
  n = car(p);
  assert(n -> tag == NUMBER);
  res = (long) car(n);

  for(p = cdr(p); p; p = cdr(p))
    {
      n = car(p);
      assert(n -> tag == NUMBER);
      tmp = (long) car(n);
      if(tmp < res) res = tmp;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static int max_number_enumeration(Node * node)
{
  Node * p, * n;
  int res, tmp;

  assert(node -> tag == ENUM);
  assert(car(node));

  p = car(node);
  n = car(p);
  assert(n -> tag == NUMBER);
  res = (long) car(n);

  for(p = cdr(p); p; p = cdr(p))
    {
      n = car(p);
      assert(n -> tag == NUMBER);
      tmp = (long) car(n);
      if(tmp > res) res = tmp;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

int is_number_type(Node * node)
{
  Node * p;
  int res;

  if(node)
    {
      switch(node -> tag)
        {
	  case BOOLEAN:
	  case TWODOTS:
	    res = 1;
	    break;
	  
	  case  ENUM:
	    for(p = car(node), res = 1; res && p; p = cdr(node))
	      res = (car(p) -> tag == NUMBER);
	    break;
	  
	  default:
	    assert(0);
	    res = 0;
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

int is_range_type(Node * node)
{
  int res;

  if(node)
    {
      switch(node -> tag)
        {
	  case BOOLEAN:
	  case TWODOTS:
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

int min_number_range(Node * node)
{
  int res;

  assert(node);
  assert(is_range_type(node));

  switch(node -> tag)
    {
      case BOOLEAN:
        res = 0;
        break;

      case TWODOTS:
        res = (long) car(car(node));
	break;
      
      default:
        res = 0;
	assert(0);
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static int max_number_range(Node * node)
{
  int res;

  assert(node);
  assert(is_range_type(node));

  switch(node -> tag)
    {
      case BOOLEAN:
        res = 1;
        break;

      case TWODOTS:
        res = (long) car(cdr(node));
	break;
      
      default:
        res = 0;
	assert(0);
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

int is_boolean_type(Node * node)
{
  int res, l, r;

  if(node)
    {
      switch(node -> tag)
	{
	  case TWODOTS:
	    l = (long) car(car(node));
	    r = (long) car(cdr(node));
	    res = (l == 0 && r == 1);
	    return res;
	  
	  case BOOLEAN:
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

static int cmp_Node_for_qsort(const void * a_ptr, const void * b_ptr)
{
  Node * a, * b;
  int res;

  a = * (Node**) a_ptr;
  b = * (Node**) b_ptr;
  res = cmp_Node(a, b);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * sort_enum(Node * node)
{
  Node * res, * p, ** nodes;
  unsigned l, i;

  assert(node -> tag == ENUM);

  l = length(car(node));
  nodes = (Node**) calloc(l, sizeof(Node*));

  for(i = 0, p = car(node); p; p = cdr(p), i++)
    nodes[i] = car(p);
  
  assert(i == l);

  qsort(nodes, l, sizeof(Node*), cmp_Node_for_qsort);
  
  for(i = l, res = 0; i; i--) res = cons(copy(nodes[i - 1]), res);

  free(nodes);

  res = new(ENUM, res, 0);

  return res;
}

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

static int is_sorted_enum(Node * node)
{
  Node * p, * last;
  int res;

  assert(node -> tag == ENUM);

  for(res = 1, p = car(node), last = 0; res && p; p = cdr(p))
    {
      if(last) res = (cmp_Node(last, car(p)) < 0);
      last = car(p);
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static int is_normalized_type(Node * node)
{
  int res;

  if(node)
    {
      switch(node -> tag)
        {
	  case BOOLEAN:
	    res = 1;
	    break;

	  case TWODOTS:
	    res = !is_boolean_type(node);
	    break;
	  
	  case ENUM:
	    res = is_sorted_enum(node);
	    break;

	  default:
	    assert(0);
	    res = 0;
	    break;
	}
    }
  else res = 1;

  return res;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static Node * normalize_enum(Node * node)
{
  unsigned len;
  Node * res;
  int l, r;

  assert(node -> tag == ENUM);
      
  if(is_number_enumeration(node))
    {
      l = min_number_enumeration(node);
      r = max_number_enumeration(node);
      len = length(car(node));
      if(len == (unsigned)(r - l + 1))
	{
	  if(l == 0 && r == 1) res = new(BOOLEAN, 0, 0);
	  else res = new(TWODOTS, number(l), number(r));
	}
      else res = sort_enum(node);
    }
  else res = sort_enum(node);

  assert(is_normalized_type(res));
  
  return res;
}

/*------------------------------------------------------------------------*/

void range_bounds(Node * node, int * l_ptr, int * r_ptr)
{
  switch(node -> tag)
    {
      case BOOLEAN:
        *l_ptr = 0;
	*r_ptr = 1;
        break;
      
      case TWODOTS:
        *l_ptr = (long) car(car(node));
        *r_ptr = (long) car(cdr(node));
	assert(*l_ptr <= *r_ptr);
	break;

      default:
        assert(0);
	break;
    }
}

/*------------------------------------------------------------------------*/

static Node * normalize_range(Node * node)
{
  Node * res;
  int l, r;

  assert(node -> tag == TWODOTS);

  range_bounds(node, &l, &r);
  if(l == 0 && r == 1) res = new(BOOLEAN, 0, 0);
  else res = copy(node);

  return res;
}

/*------------------------------------------------------------------------*/

Node * normalize_type(Node * node)
{
  Node * res;

  switch(node -> tag)
    {
      case ENUM:
        res = normalize_enum(node);
	break;
      
      case BOOLEAN:
        res = copy(node);
	break;
      
      case TWODOTS:
        res = normalize_range(node);
        break;
      
      default:
        res = 0;
	assert(0);
	break;
    }

  return res;
}

/*------------------------------------------------------------------------*/

static Node * type_as_enum(Node * t)
{
  int i, l, r;
  Node * res;

  switch(t -> tag)
    {
      case BOOLEAN:
        res = new(ENUM, cons(number(0), cons(number(1), 0)), 0);
	break;
      
      case ENUM:
        res = copy(t);
	break;
      
      case TWODOTS:
        l = (long) car(car(t));
        r = (long) car(cdr(t));
	for(i = r, res = 0; i >= l; i--) res = cons(number(i), res);
	res = new(ENUM, res, 0);
        break;
      
      default:
        assert(0);
	res = 0;
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/
#if 0

static Node * type_as_range(Node * t)
{
  Node * res;

  switch(t -> tag)
    {
      case BOOLEAN:
        res = new(TWODOTS, number(0), number(1));
        break;
      
      case TWODOTS:
        res = copy(t);
	break;
      
      default:
        assert(0);
	res = 0;
	break;
    }
  
  return res;
}

#endif
/*------------------------------------------------------------------------*/

static Node * merge_type_as_enums(Node * a, Node * b)
{
  Node * res, * p, * last, * a_as_enum, * b_as_enum, ** nodes;
  unsigned l, i;

  a_as_enum = type_as_enum(a);
  b_as_enum = type_as_enum(b);

  assert(car(a_as_enum) || car(b_as_enum));

  l = length(car(a_as_enum)) + length(car(b_as_enum));
  nodes = (Node**) calloc(l, sizeof(Node*));

  for(i = 0, p = car(a_as_enum); p; i++, p = cdr(p)) nodes[i] = car(p);
  for(p = car(b_as_enum); p; i++, p = cdr(p)) nodes[i] = car(p);

  qsort(nodes, l, sizeof(Node*), cmp_Node_for_qsort);

  assert(i == l);

  for(i = l, last = 0, res = 0; i; i--)
    {
      if(nodes[i - 1] != last)
        {
	  last = nodes[i - 1];
	  res = cons(copy(last), res);
	}
    }
  
  free(nodes);
  delete(b_as_enum);
  delete(a_as_enum);

  res = new(ENUM, res, 0);

  assert(is_normalized_type(res));
  
  return res;
}

/*------------------------------------------------------------------------*/

Node * merge_type(Node * a, Node * b)
{
  int al, bl, ar, br, l, r;
  Node * res;

  if(!a) res = copy(b);
  else
  if(!b) res = copy(a);
  else
  if(is_range_type(a) && is_range_type(b))
    {
      range_bounds(a, &al, &ar);
      range_bounds(b, &bl, &br);

      if(ar + 1 < bl || br + 1 < al)
        {
	  /* The intervals can not be combined to a new interval.  If this
	   * turns out to be a bottle neck, then we have to use a union of
	   * intervalls and adapt all the type code above to work with
	   * unions of enums as well.
	   */
	  res = merge_type_as_enums(a, b);
	}
      else
        {
	  l = min(al, bl);
	  r = max(ar, br);

	  if(l == 0 && r == 1) res = new(BOOLEAN, 0, 0);
	  else res = new(TWODOTS, number(l), number(r));
	}
    }
  else res = merge_type_as_enums(a, b);

  assert(is_normalized_type(res));
  
  return res;
}

/*------------------------------------------------------------------------*/

int type_contains(Node * t, Node * c)
{
  int res, i, l, r;

  if(t)
    {
      switch(t -> tag)
	{
	  case BOOLEAN:
	  case TWODOTS:

	    if(c -> tag == NUMBER)
	      {
		i = (long) car(c);
	        range_bounds(t, &l, &r);
		res = (l <= i && i <= r);
	      }
	    else res = 0;
	    break;
	  
	  case ENUM:
	    res = is_member(car(t), c);
	    break;

	  default:
	    assert(0);
	    res = 0;
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

unsigned get_type_position(Node * t, Node * c)
{
  int res, i, l, r;

  if(t)
    {
      switch(t -> tag)
        {
	  case BOOLEAN:
	  case TWODOTS:

	    if(c -> tag == NUMBER)
	      {
	        i = (long) car(c);
		range_bounds(t, &l, &r);
	        if(l <= i && i <= r) res = i - l;
		else res = 1 << num_bits(t);
	      }
	    else res = 1 << num_bits(t);
	    break;
	  
	  case ENUM:
	    res = get_position(car(t), c);
	    break;
	  
	  default:
	    assert(0);
	    res = 0;
	    break;
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

int is_subtype(Node * a, Node * b)
{
  int res, al, ar, bl, br, i, l, r;
  Node * p, * c;

  if(!a) res = 1;
  else
  if(!b) res = 0;
  else
  if(is_range_type(a) && is_range_type(b))
    {
      range_bounds(a, &al, &ar);
      range_bounds(b, &bl, &br);

      res = (bl <= al && ar <= br);
    }
  else
    {
      switch(a -> tag)
        {
	  case BOOLEAN:
	  case TWODOTS:
	    range_bounds(a, &l, &r);
	    for(i = l, res = 1; res && i <= r; i++) 
	      {
		c = number(i);
		res = type_contains(b, c);
		delete(c);
	      }
	    break;
	  
	  case ENUM:
	    for(p = car(a), res = 1; res && p; p = cdr(p))
	      res = type_contains(b, car(p));
	    break;

	  default:
	    assert(0);
	    res = 0;
	    break;
	}
    }

  return res;
}

/*------------------------------------------------------------------------*/

Node * intersect_type(Node * a, Node * b)
{
  Node * res, * tmp, * p, * c;
  int al, ar, bl, br, l, r;

  if(!a || !b) res = 0;
  else
  if(is_range_type(a) && is_range_type(b))
    {
      range_bounds(a, &al, &ar);
      range_bounds(b, &bl, &br);

      l = max(al, bl);
      r = min(ar, br);

      if(l > r) res = 0;
      else if(l == 0 && r == 1) res = new(BOOLEAN, 0, 0);
      else res = new(TWODOTS, number(l), number(r));
    }
  else
    {
      assert(a -> tag == ENUM || b -> tag == ENUM);

      if(a -> tag != ENUM)
        {
	  tmp = a;
	  a = b;
	  b = tmp;
	}
      
      assert(a -> tag == ENUM);

      for(p = car(a), tmp = 0; p; p = cdr(p))
        {
	  c = car(p);
	  if(type_contains(b, c)) tmp = cons(copy(c), tmp);
	}
      
      if(tmp)
        {
	  tmp = new(ENUM, tmp, 0);
	  res = normalize_enum(tmp);
	  delete(tmp);
	}
      else res = 0;
    }
  
  assert(is_normalized_type(res));

  return res;
}

/*------------------------------------------------------------------------*/

static void insert_TfContext(TfContext * context, Node * node)
{
  if(node)
    {
      switch(node -> tag)
        {
	  case MODULE:
	    insert_TfContext(context, cdr(node));
	    break;

	  case DEFINE:
	  case VAR:
	  case IVAR:
	    insert_TfContext(context, car(node));
	    break;
	  
	  case DECL:
	    associate(context -> decls, car(node), cdr(node));
	    break;

	  case DEFINEASSIGNMENT:
	    associate(context -> defs, car(node), cdr(node));
	    break;

	  case LIST:
	    insert_TfContext(context, car(node));
	    insert_TfContext(context, cdr(node));
	    break;

	  default:
	    break;
	}
    }
}

/*------------------------------------------------------------------------*/

static void setup_TfContext(TfContext * context, Node * node)
{
  context -> node2type = new_Assoc();
  context -> defs = new_Assoc();
  context -> decls = new_Assoc();
  insert_TfContext(context, node);
}

/*------------------------------------------------------------------------*/

static void release_TfContext(TfContext * context)
{
  delete_Assoc(context -> defs);
  delete_Assoc(context -> decls);
}

/*------------------------------------------------------------------------*/

static Node * tf(TfContext * context, Node * node)
{
  Node * def, * res, * a, * b, * tmp, * p;
  int l, r;

  if(node)
    {
      if(is_associated(context -> node2type, node))
	{
	  res = get_association(context -> node2type, node);
	}
      else
	{
	  switch(node -> tag)
	    {
	      case DECL:
		a = tf(context, car(node));
		b = tf(context, cdr(node));
		res = 0;
	        break;
	      
	      case ENUM:

		/* Do not forget to insert all constants.
		 */
	        for(p = car(node); p; p = cdr(p))
		  {
		    a = tf(context, car(p));
		  }
		res = 0;
	        break;
	      
	      case BOOLEAN:
	      case TWODOTS:
		res = 0;
	        break;

	      case LIST:
		a = tf(context, car(node));
		b = tf(context, cdr(node));

		if(car(node) -> tag == COLON)
		  {
		    res = merge_type(a, b);
		    associate(context -> node2type, copy(node), res);
		  }
		else res = 0;
		break;
	      
	      case CASE:
		res = tf(context, car(node));
		associate(context -> node2type, copy(node), copy(res));
		break;
	      
	      case COLON:
	        a = tf(context, car(node));
	        tmp = new(BOOLEAN, 0, 0);
		if(!is_subtype(a, tmp))
		  {
		    fputs(
		      "*** smvflatten: expected boolean condition\n",
		      stderr);
		    exit(1);
		  }
		delete(tmp);
	        b = tf(context, cdr(node));	
		res = copy(b);
		associate(context -> node2type, copy(node), res);
	        break;
	      
	      case PLUS:
	        a = tf(context, car(node));
		b = tf(context, cdr(node));
		if(!is_range_type(a) || !is_range_type(b))
		  {
		    fputs(
		      "*** smvflatten: expected range type for '+'\n",
		      stderr);
		    exit(1);
		  }
		l = min_number_range(a) + min_number_range(b);
		r = max_number_range(a) + max_number_range(b);
		tmp = new(TWODOTS, number(l), number(r));
		res = normalize_range(tmp);
		delete(tmp);
		associate(context -> node2type, copy(node), res);
	        break;
	      
	      case MINUS:
	        a = tf(context, car(node));
		b = tf(context, cdr(node));
		if(!is_range_type(a) || !is_range_type(b))
		  {
		    fputs(
		      "*** smvflatten: expected range type for '-'\n",
		      stderr);
		    exit(1);
		  }
		l = min_number_range(a) - max_number_range(b);
		r = max_number_range(a) - min_number_range(b);
		tmp = new(TWODOTS, number(l), number(r));
		res = normalize_range(tmp);
		delete(tmp);
		associate(context -> node2type, copy(node), res);
	        break;

	      case UMINUS:
	        a = tf (context, car(node));
		abort ();
	        break;
	      
	      case ATOM:
	      case ACCESS:

		assert(context -> decls);
		assert(context -> defs);

		res = get_association(context -> decls, node);
		def = get_association(context -> defs, node);

		assert(!res || !def);

		if(def || res)
		  {
		    if(def)
		      {
			tf(context, def);
			res = get_association(context -> node2type, def);
			assert(res);
		      }

		    res = copy(res);

		    if(verbose >= 3)
		      {
			fputs("-- [verbose]   type of `", stderr);
			print(stderr, node);

			if(verbose >= 4)
			  {
			    fputs("' is `", stderr);
			    print(stderr, res);
			    fprintf(stderr, "' (%u bits)\n", num_bits(res));
			  }
			else fprintf(stderr, "' has %u bits\n", num_bits(res));
		      }
		  }
		else
		  {
		    /* Found a constant.
		     */
		    res = new(ENUM, cons(copy(node), 0), 0);
		  }

		associate(context -> node2type, copy(node), res);
		break;
	      
	      case NUMBER:
		res = new(TWODOTS, copy(node), copy(node));
		associate(context -> node2type, copy(node), res);
		break;

	      case MODULE:
		tf(context, cdr(node));
		res = 0;
		break;

	      case AND:
	      case AU:
	      case EU:
	      case UNTIL:
	      case IFF:
	      case IMPLIES:
	      case OR:
		a = tf(context, car(node));
		b = tf(context, cdr(node));
		res = new(BOOLEAN, 0, 0);
		if(!is_subtype(a, res) || !is_subtype(b, res))
		  {
		    fputs(
		      "*** smvflatten: expected boolean operands\n", stderr);
		    exit(1);
		  }
		associate(context -> node2type, copy(node), res);
		break;

	      case MIN:
	      case MAX:
		a = tf(context, car(node));
		b = tf(context, cdr(node));
		tmp = new(BOOLEAN, 0, 0);
		if(!is_subtype(a, tmp) || !is_subtype(b, tmp))
		  {
		    fputs(
		      "*** smvflatten: no boolean expression for MIN/MAX\n",
		      stderr);
		    exit(1);
		  }
		delete(tmp);
		res = 0;
		break;
	      
	      case AX:
	      case AG:
	      case AF:
	      case EX:
	      case EG:
	      case EF:
	      case F:
	      case X:
	      case G:
	      case NOT:
		a = tf(context, car(node));
		res = new(BOOLEAN, 0, 0);
		if(!is_subtype(a, res))
		  {
		    fputs(
		      "*** smvflatten: expected boolean operand\n", stderr);
		    exit(1);
		  }
		associate(context -> node2type, copy(node), res);
		break;

	      case NEXT:
	        a = tf(context, car(node));
		res = copy(a);
		associate(context -> node2type, copy(node), res);
	        break;
	      
	      case LT:
	      case LE:
	      case GE:
	      case GT:
	      case NOTEQUAL:
	      case EQUAL:

		a = tf(context, car(node));
		b = tf(context, cdr(node));
	        res = new(BOOLEAN, 0, 0);
		associate(context -> node2type, copy(node), res);
		break;
	      
	      case TRANSASSIGNMENT:
	      case DEFINEASSIGNMENT:
	      case INVARASSIGNMENT:
	      case INITASSIGNMENT:
	        a = tf(context, car(node));
	        b = tf(context, cdr(node));
		if(!is_subtype(b, a))
		  {
		    tmp = intersect_type(a, b);
		    if(!tmp)
		      {
		        fputs(
			  "*** smvflatten: types of LHS and RHS of '",
			  stderr);
			print_lhs_of_assignment(stderr, node);
			fputs(" := ...' have empty intersection\n", stderr);
			exit(1);
		      }

		    if(tmp != b)
		      {
		        if(verbose >= 3)
			  {
			    fputs("-- [verbose]     RHS of '", stderr);
			    print_lhs_of_assignment(stderr, node);
			    fputs(" := ...' requires type check\n", stderr);
			  }
		      }
		      
		    delete(tmp);
		  }
		res = 0;
		break;
	      
	      case INVAR:
	      case INIT:
	      case TRANS:
	      case FAIRNESS:
	      case SPEC:
	      case LTLSPEC:
		a = tf(context, car(node));
	        tmp = new(BOOLEAN, 0, 0);
		if(!is_subtype(a, tmp))
		  {
		    fputs(
		      "*** smvflatten: type of section body is not boolean\n",
		      stderr);
		    exit(1);
		  }
		delete(tmp);
		res = 0;
		break;
	      
	      case VAR:
	      case IVAR:
	      case DEFINE:
	      case ASSIGN:
	      case COMPUTE:
		tf(context, car(node));
		res = 0;
		break;

	      default:
		assert(0);
		res = 0;
		break;
	    }
	}
    }
  else res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

static void insert_type(Assoc * types, Node * type)
{
  if(!is_associated(types, type)) associate(types, type, type);
}

/*------------------------------------------------------------------------*/

Assoc * typify(Node * node)
{
  Assoc * res, * types;
  TfContext context;

  if(verbose) fputs("-- [verbose] checking types ...\n", stderr);

  setup_TfContext(&context, node);
  tf(&context, node);
  release_TfContext(&context);
  res = context.node2type;

  if(verbose >=2) 
    {
      types = new_Assoc();
      map_dst_in_Assoc(res, types, (void(*)(void*,void*)) insert_type);
      fprintf(stderr, "-- [verbose]   found %u types\n", count_Assoc(types));
      delete_Assoc(types);
    }

  if(verbose) fputs("-- [verbose] checked types.\n", stderr);

  return res;
}

/*------------------------------------------------------------------------*/

void add_type(Assoc * node2type, Node * node)
{
  TfContext context;

  context.node2type = node2type;
  context.decls = context.defs = 0;
  tf(&context, node);
}

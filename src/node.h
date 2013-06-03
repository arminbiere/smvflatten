/*------------------------------------------------------------------------*/
/* Copyright 1999-2013 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/
#ifndef _node_h_INCLUDED
#define _node_h_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdio.h>

/*------------------------------------------------------------------------*/

struct Assoc;

/*------------------------------------------------------------------------*/

typedef struct Node Node;

/*------------------------------------------------------------------------*/

struct Node
{
  int tag;
  unsigned ref, age;
  Node * head, * tail, * next;
  unsigned contains_next;
  unsigned contains_temporal_operator;
};

/*------------------------------------------------------------------------*/

extern void init_Node(void);
extern void exit_Node(void);

/*------------------------------------------------------------------------*/

extern Node * new(int, Node *, Node *);
extern Node * new_simplify(int, Node *, Node *);
extern void delete(Node *);
extern Node * copy(Node*);
extern Node * cons(Node * head, Node * tail);
extern Node * append(Node * head, Node * node);
extern Node * append_tagged(int tag, Node * head, Node * rest);
extern Node * car(Node *);
extern Node * cdr(Node *);
extern Node * reverse(Node*);
extern unsigned length(Node*);
extern Node * get_last(Node *);
extern int is_member(Node * list, Node * member);
extern unsigned get_position(Node * list, Node * member);
extern Node * atom(const char *);
extern Node * number(int);
extern unsigned count_Node(void);
extern Node * new_oracle(void);
extern Node * new_running(void);
extern Node * new_macro(void);
extern int is_oracle(Node *);
extern int is_true(Node *);
extern int is_constant(Node *);
extern int is_atom(Node *);
extern int is_literal(Node *);
extern int is_clause(Node *);
extern int is_negation(Node *, Node *);
extern int is_false(Node *);
extern Node * substitute(Node *, struct Assoc *);
extern Node * ite(Node * c, Node * t, Node * e);
extern Node * ite_simplify(Node * c, Node * t, Node * e);
extern Node * strip_at(Node * n);
extern int cmp_Node(Node*,Node*);
extern unsigned term_size(Node *);
extern Node * add_next_in_front_of_atoms(Node * node);

/*------------------------------------------------------------------------*/

#endif

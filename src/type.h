#ifndef _type_h_INCLUDED
#define _type_h_INCLUDED

/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "node.h"
#include "assoc.h"

/*------------------------------------------------------------------------*/

extern unsigned num_bits(Node * t);
extern unsigned size_type(Node * t);
extern Node * get_first_type(Node * t);
extern Node * get_last_type(Node * t);
extern Node * normalize_type(Node *);
extern int is_boolean_type(Node *);
extern int is_range_type(Node *);
extern int is_number_type(Node *);
extern int type_contains(Node * t, Node * c);
extern int is_subtype(Node * a, Node * b);
extern unsigned get_type_position(Node * t, Node * c);
extern void add_type(Assoc * assoc, Node * node);
extern void range_bounds(Node * range, int * l_ptr, int * r_ptr);
extern Node * merge_type(Node * a, Node * b);
extern unsigned ldceil(unsigned);

/*------------------------------------------------------------------------*/
/* Associate with each term in the list of modules a canonical term.  The
 * caller is responsible for deleting the references of the types that are
 * stored in the association (the destination).
 */
extern Assoc * typify(Node * modules);

/*------------------------------------------------------------------------*/

#endif

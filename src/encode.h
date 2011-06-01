#ifndef _encode_h_INCLUDED
#define _encode_h_INCLUDED

/*------------------------------------------------------------------------*/
/* Copyright 1999-2011 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"
#include "node.h"

/*------------------------------------------------------------------------*/
/* The first argument has to be generated by a call to `typify' with modules
 * as argument.  The encoding process deletes the contents of `node2type'
 * but inserts for backannotation purposes an association for each generated
 * boolean variable with its original type.  This information can be used by
 * `print_typped'.  The caller has to delete the references of the types
 * inserted in `node2type'.
 */
extern Node * encode(Assoc * node2type, Node * modules);

/*------------------------------------------------------------------------*/

#endif

#ifndef _check_h_INCLUDED
#define _check_h_INCLUDED

/*------------------------------------------------------------------------*/
/* Copyright Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"
#include "node.h"

/*------------------------------------------------------------------------*/
/* Returns the mapping of all terms and formulae in the flat module `node'
 * to their types.   It also checks for noncircular definitions.
 */
extern Assoc * check(Node * node);

/*------------------------------------------------------------------------*/

#endif

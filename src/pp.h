#ifndef _pp_h_INCLUDED
#define _pp_h_INCLUDED

extern void print(FILE*, Node *);
extern void print_typped(FILE*, struct Assoc *, Node *);
extern void print_lhs_of_assignment(FILE * file, Node * node);

#endif

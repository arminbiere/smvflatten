/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/
#ifndef _assoc_h_INCLUDED
#define _assoc_h_INCLUDED

/*------------------------------------------------------------------------*/

typedef struct Assoc Assoc;

/*------------------------------------------------------------------------*/

extern Assoc * new_Assoc(void);
extern void delete_Assoc(Assoc *);
extern void reset_Assoc(Assoc *);
extern void associate(Assoc *, void * src, void * dst);
extern void deassociate(Assoc *, void * src);
extern int is_associated(Assoc *, void * src);
extern void * get_association(Assoc *, void * src);
extern void forall_Assoc(Assoc *, void(*)(void*,void*));
extern void forall_src_in_Assoc(Assoc *, void(*)(void*));
extern void forall_dst_in_Assoc(Assoc *, void(*)(void*));
extern void map_Assoc(Assoc *,  void*, void(*)(void*,void*,void*));
extern void map_src_in_Assoc(Assoc *, void *, void(*)(void*,void*));
extern void map_dst_in_Assoc(Assoc *, void *, void(*)(void*,void*));
extern unsigned count_Assoc(Assoc*);

/*------------------------------------------------------------------------*/

#endif

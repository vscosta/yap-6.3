/************************************************************************
**                                                                     **
**                   The YapTab/YapOr/OPTYap systems                   **
**                                                                     **
** YapTab extends the Yap Prolog engine to support sequential tabling  **
** YapOr extends the Yap Prolog engine to support or-parallelism       **
** OPTYap extends the Yap Prolog engine to support or-parallel tabling **
**                                                                     **
**                                                                     **
**      Yap Prolog was developed at University of Porto, Portugal      **
**                                                                     **
************************************************************************/

#ifdef MULTI_ASSIGNMENT_VARIABLES
/* 
   Set of routines to allow restoring updatable variables when we go *up*
   in the tree. Required by copying, SBA, and tabling. Not required by ACOW.
*/

#ifndef OPT_MAVAR_STATIC
#define OPT_MAVAR_STATIC inline static
#endif /* !OPT_MAVAR_STATIC */

OPT_MAVAR_STATIC unsigned int Yap_MAVAR_HASH(CELL *addr USES_REGS);
OPT_MAVAR_STATIC struct ma_h_entry * Yap_ALLOC_NEW_MASPACE(USES_REGS1);
OPT_MAVAR_STATIC int Yap_lookup_ma_var(CELL *addr USES_REGS);
OPT_MAVAR_STATIC UInt Yap_NEW_MAHASH(ma_h_inner_struct *top USES_REGS);

OPT_MAVAR_STATIC unsigned int
Yap_MAVAR_HASH(CELL *addr USES_REGS) {
#if SIZEOF_INT_P==8
  return((((unsigned int)((CELL)(addr)))>>3)%MAVARS_HASH_SIZE);
#else
  return((((unsigned int)((CELL)(addr)))>>2)%MAVARS_HASH_SIZE); 
#endif
}

OPT_MAVAR_STATIC struct ma_h_entry *
Yap_ALLOC_NEW_MASPACE(USES_REGS1)
{
  ma_h_inner_struct *newS = REMOTE_ma_h_top(worker_id);
  REMOTE_ma_h_top(worker_id)++;
  return newS;
}

OPT_MAVAR_STATIC int
Yap_lookup_ma_var(CELL *addr USES_REGS) {
  unsigned int i = Yap_MAVAR_HASH(addr PASS_REGS);
  struct ma_h_entry *nptr, *optr;

  if (REMOTE_ma_hash_table(worker_id)[i].timestmp != REMOTE_ma_timestamp(worker_id)) {
    REMOTE_ma_hash_table(worker_id)[i].timestmp = REMOTE_ma_timestamp(worker_id);
    REMOTE_ma_hash_table(worker_id)[i].val.addr = addr;
    REMOTE_ma_hash_table(worker_id)[i].val.next = NULL;
    return FALSE;
  }
  if (REMOTE_ma_hash_table(worker_id)[i].val.addr == addr) 
    return TRUE;
  optr = &(REMOTE_ma_hash_table(worker_id)[i].val);
  nptr = REMOTE_ma_hash_table(worker_id)[i].val.next;
  while (nptr != NULL) {
    if (nptr->addr == addr) {
      return TRUE;
    }
    optr = nptr;
    nptr = nptr->next;
  }
  nptr = Yap_ALLOC_NEW_MASPACE(PASS_REGS1);
  nptr->addr = addr;
  nptr->next = optr;
  return FALSE;
}

OPT_MAVAR_STATIC UInt
Yap_NEW_MAHASH(ma_h_inner_struct *top USES_REGS) {
  UInt time = ++REMOTE_ma_timestamp(worker_id);
  if (time == 0) {
    unsigned int i;
    /* damn, we overflowed */
    for (i = 0; i < MAVARS_HASH_SIZE; i++)
      REMOTE_ma_hash_table(worker_id)[i].timestmp = 0;
    time = ++REMOTE_ma_timestamp(worker_id);
  }
  REMOTE_ma_h_top(worker_id) = top;
  return time;
}
#else
#define Yap_MAVAR_HASH(addr)
#define Yap_ALLOC_NEW_MASPACE()
#define Yap_lookup_ma_var(addr)
#define Yap_NEW_MAHASH(top)
#endif /* MULTI_ASSIGNMENT_VARIABLES */

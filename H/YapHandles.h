/*************************************************************************
*									 *
*	 YAP Prolog 	%W% %G% 					 *
*	Yap Prolog was developed at NCCUP - Universidade do Porto	 *
*									 *
* Copyright L.Damas, V.S.Costa and Universidade do Porto 1985-1997	 *
*									 *
**************************************************************************
*									 *
* File:		YapHandles.h   						 *
* mods:									 *
* comments:	term handles for YAP: basic ops				 *
* version:      $Id: Yap.h,v 1.38 2008-06-18 10:02:27 vsc Exp $	 *
*************************************************************************/

#ifndef YAP_HANDLES_H
#define YAP_HANDLES_H 1

#include "inline-only.h"
#include "Yatom.h"

#define LOCAL_CurHandle LOCAL_CurSlot
#define REMOTE_CurHandle REMOTE_CurSlot
#define LOCAL_NHandles LOCAL_NSlots
#define REMOTE_NHandles REMOTE_NSlots
#define LOCAL_HandleBase LOCAL_SlotBase
#define REMOTE_HandleBase REMOTE_SlotBase

/**
@groupdef  term_t_slots 

@{
Also known as term handles, slots are offsets to entries in the local stack. YAP
never compresses the local stack, so slots are respected by the garbage
collector,
hence providing a way to access terms without being exposed to stack shifts or
garbage-collection.

 Space is released when the function terminates. Thus, slots will be
automatically released at the end
of a function. Hence, slots should always be used as local variables.

Handles are organized as follows:
---- Offset of next pointer in chain (tagged as an handle_t)
---- Number of entries (tagged as handle_t), in the example TAG(INT,4)
Entry
Entry
Entry
Entry
---- Number of entries (tagged as handle_t), in the example TAG(INT,4)

Handles are not known to the yaam. Instead, A new set of slots is created when
the
emulator calls user C-code.
(see YAP_Execute* functions). They are also created:

   - by SWI's PL_foreign_frame() function,

   - by the YAP_RunGoal() routines and friends, when they exit successfully.
Notice that all handles created by c-goals  within
     a `Goal` execution should not be used afterwards.

     This section lists the main internal functions for slot management. These
functions are then exported through corresponding FLI C-functions

*************************************************************************************************/

#include <stdio.h>

/// @brief reboot the slot system.
/// Used when we start from scratch (Reset).
#define Yap_RebootHandles(wid) Yap_RebootHandles__(wid PASS_REGS)
#define Yap_RebootSlots(wid) Yap_RebootHandles__(wid PASS_REGS)

INLINE_ONLY void Yap_RebootHandles__(int wid USES_REGS) {
  // fprintf(stderr,  " StartHandles = %ld", REMOTE_CurHandle(worker_id));
  REMOTE_CurHandle(wid) = 1;
}

/// @brief declares a new set of slots.
/// Used to tell how many slots we have so d=dara when we entered a segment of
/// code.
//#define Yap_StartHandles() (
// printf("[<<<%s,%s,%d-%ld\n",__FILE__,__FUNCTION__,__LINE__,REMOTE_CurHandle(worker_id))?Yap_StartHandles__(PASS_REGS1):
//-1)
#define Yap_StartHandles() Yap_StartHandles__(PASS_REGS1)
#define Yap_StartSlots() Yap_StartHandles__(PASS_REGS1)

INLINE_ONLY yhandle_t Yap_StartHandles__(USES_REGS1);
INLINE_ONLY yhandle_t Yap_StartHandles__(USES_REGS1) {
  //  // fprintf(stderr,  " StartHandles = %ld", REMOTE_CurHandle(worker_id));
  // fprintf(stderr,"SS %s:%d\n", __FILE__, __LINE__);;
  if (REMOTE_CurHandle(worker_id) < 0) {
    Yap_Error(SYSTEM_ERROR_INTERNAL, 0L, " StartHandles = %ld",
              REMOTE_CurHandle(worker_id));
  }
  return REMOTE_CurHandle(worker_id);
}

/// @brief reset the nmber of slots _slot_ to the number existing before the
/// call that produce _slot_
///(eg, Yap_StartHandles(), YAP_NewHandles(), or YAP_PushHandle)
//#define Yap_CloseHandles(slot) ( printf("- %s,%s,%d
//%ld>>>]\n",__FILE__,__FUNCTION__,__LINE__, slot)?Yap_CloseHandles__(slot
// PASS_REGS):-1)
#define Yap_CloseHandles(slot) Yap_CloseHandles__(slot PASS_REGS)
#define Yap_CloseSlots(slot) Yap_CloseHandles__(slot PASS_REGS)

INLINE_ONLY void Yap_CloseHandles__(yhandle_t slot USES_REGS);
INLINE_ONLY void Yap_CloseHandles__(yhandle_t slot USES_REGS) {
  // fprintf(stderr,"CS %s:%d\n", __FILE__, __LINE__);
  REMOTE_CurHandle(worker_id) = slot;
}

#define Yap_CurrentHandle() Yap_CurrentHandle__(PASS_REGS1)
#define Yap_CurrentSlot() Yap_CurrentHandle__(PASS_REGS1)

/// @brief report the current position of the slots, assuming that they occupy
/// the top of the stack.
INLINE_ONLY yhandle_t Yap_CurrentHandle__(USES_REGS1);
INLINE_ONLY yhandle_t Yap_CurrentHandle__(USES_REGS1) {
  return REMOTE_CurHandle(worker_id);
}

#define Yap_GetFromHandle(slot) Yap_GetFromHandle__(slot PASS_REGS)
#define Yap_GetFromSlot(slot) Yap_GetFromHandle__(slot PASS_REGS)

/// @brief read from a slot.
INLINE_ONLY Term Yap_GetFromHandle__(yhandle_t slot USES_REGS);
INLINE_ONLY Term Yap_GetFromHandle__(yhandle_t slot USES_REGS) {
  //  fprintf(stderr, "GS %s:%d\n", __FILE__, __LINE__);
  return Deref(REMOTE_HandleBase(worker_id)[slot]);
}

#define Yap_GetDerefedFromHandle(slot)                                         \
  Yap_GetDerefedFromHandle__(slot PASS_REGS)
#define Yap_GetDerefedFromSlot(slot) Yap_GetDerefedFromHandle__(slot PASS_REGS)

/// @brief read from a slot. but does not try to dereference the slot.
INLINE_ONLY Term
Yap_GetDerefedFromHandle__(yhandle_t slot USES_REGS);
INLINE_ONLY Term
Yap_GetDerefedFromHandle__(yhandle_t slot USES_REGS) {
  // fprintf(stderr,"GDS %s:%d\n", __FILE__, __LINE__);
  return REMOTE_HandleBase(worker_id)[slot];
}

#define Yap_GetPtrFromHandle(slot) Yap_GetPtrFromHandle__(slot PASS_REGS)
#define Yap_GetPtrFromSlot(slot) Yap_GetPtrFromHandle__(slot PASS_REGS)

/// @brief read the object in a slot. but do not try to dereference the slot.
INLINE_ONLY Term *
Yap_GetPtrFromHandle__(yhandle_t slot USES_REGS);
INLINE_ONLY Term *
Yap_GetPtrFromHandle__(yhandle_t slot USES_REGS) {
  // fprintf(stderr,"GPS %s:%d\n", __FILE__, __LINE__);
  return (Term *)REMOTE_HandleBase(worker_id)[slot];
}

#define Yap_AddressFromHandle(slot) Yap_AddressFromHandle__(slot PASS_REGS)
#define Yap_AddressFromSlot(slot) Yap_AddressFromHandle__(slot PASS_REGS)

INLINE_ONLY CELL *
Yap_AddressFromHandle__(yhandle_t slot USES_REGS);
INLINE_ONLY CELL *
Yap_AddressFromHandle__(yhandle_t slot USES_REGS) {
  /// @brief get the memory address of a slot

  return REMOTE_HandleBase(worker_id) + slot;
}

#define Yap_PutInSlot(slot, t) Yap_PutInHandle__(slot, t PASS_REGS)
#define Yap_PutInHandle(slot, t) Yap_PutInHandle__(slot, t PASS_REGS)
/// @brief store  term in a slot
INLINE_ONLY void Yap_PutInHandle__(yhandle_t slot,
                                                 Term t USES_REGS);
INLINE_ONLY void Yap_PutInHandle__(yhandle_t slot,
                                                 Term t USES_REGS) {
// fprintf(stderr,"PS %s:%d\n", __FILE__, __LINE__);
  REMOTE_HandleBase(worker_id)[slot] = t;
}

#ifndef Yap_Max
#define Yap_Max(X, Y) (X > Y ? X : Y)
#endif

#define ensure_handles ensure_slots
INLINE_ONLY void ensure_slots(int N USES_REGS) {
  if (REMOTE_CurHandle(worker_id) + N >= REMOTE_NHandles(worker_id)) {
    size_t inc = Yap_Max(16 * 1024, REMOTE_NHandles(worker_id) / 2); // measured in cells
    inc = Yap_Max(inc, (size_t)N + 16);                  // measured in cells
    REMOTE_HandleBase(worker_id) = (CELL *)realloc(REMOTE_HandleBase(worker_id),
                                       (inc + REMOTE_NHandles(worker_id)) * sizeof(CELL));
    REMOTE_NHandles(worker_id) += inc;
    if (!REMOTE_HandleBase(worker_id)) {
      size_t kneeds = ((inc + REMOTE_NHandles(worker_id)) * sizeof(CELL)) / 1024;
      Yap_Error(
          SYSTEM_ERROR_INTERNAL, 0 /* TermNil */,
          "Out of memory for the term handles (term_t) aka slots, l needed",
          kneeds);
    }
  }
}

/// @brief create a new slot with term t
// #define Yap_InitHandle(t)
//  (printf("+%d %ld %s,%s,%d>>>]\n", 1, REMOTE_CurHandle(worker_id),__FILE__, __FUNCTION__,
//  __LINE__)
//    ? Yap_InitHandle__(t PASS_REGS)
//    : -1)
#define Yap_InitHandle(t) Yap_InitHandle__(t PASS_REGS)
#define Yap_PushHandle(t) Yap_InitHandle__(t PASS_REGS)
#define Yap_InitSlot(t) Yap_InitHandle__(t PASS_REGS)

INLINE_ONLY yhandle_t Yap_InitHandle__(Term t USES_REGS);
INLINE_ONLY yhandle_t Yap_InitHandle__(Term t USES_REGS) {
  yhandle_t old_slots = REMOTE_CurHandle(worker_id);

  ensure_slots(1 PASS_REGS);
  if (t==0) {
    t = MkVarTerm();
  } /* else if (IsVarTerm(t) && VarOfTerm(t) > HR ) {
    Term tg = MkVarTerm();
    Bind_Local(VarOfTerm(t), tg);
    }*/
  REMOTE_HandleBase(worker_id)[old_slots] = t;
  REMOTE_CurHandle(worker_id)++;
  return old_slots;
}

//#define Yap_NewHandles(n) ( printf("+%d %ld
//%s,%s,%d>>>]\n",n,REMOTE_CurHandle(worker_id),__FILE__,__FUNCTION__,__LINE__)
//?Yap_NewHandles__(n PASS_REGS):-1)
#define Yap_NewHandles(n) Yap_NewHandles__(n PASS_REGS)
#define Yap_NewSlots(n) Yap_NewHandles__(n PASS_REGS)

INLINE_ONLY yhandle_t Yap_NewHandles__(int n USES_REGS);
INLINE_ONLY yhandle_t Yap_NewHandles__(int n USES_REGS) {
  yhandle_t old_slots = REMOTE_CurHandle(worker_id);
  int i;
  // fprintf(stderr, "NS %s:%d\n", __FILE__, __LINE__);

  ensure_slots(n PASS_REGS);
  for (i = 0; i < n; i++) {
    REMOTE_HandleBase(worker_id)[old_slots + i] = MkVarTerm();
  }
  REMOTE_CurHandle(worker_id) += n;
  return old_slots;
}

//#define Yap_InitHandles(n, ts)
//  (printf("+%d %d %s,%s,%d>>>]\n", n, REMOTE_CurHandle(worker_id), __FILE__, __FUNCTION__,
//  __LINE__)
//   ? Yap_InitHandles__(n, ts PASS_REGS)
//   : -1)
#define Yap_InitHandles(n, ts) Yap_InitHandles__(n, ts PASS_REGS)
#define Yap_InitSlots(n, ts) Yap_InitHandles__(n, ts PASS_REGS)

/// @brief create n new slots with terms ts[]
INLINE_ONLY yhandle_t Yap_InitHandles__(int n,
                                                      Term *ts USES_REGS);
INLINE_ONLY yhandle_t Yap_InitHandles__(int n,
                                                      Term *ts USES_REGS) {
  yhandle_t old_slots = REMOTE_CurHandle(worker_id);
  int i;
  ensure_slots(n PASS_REGS);
  for (i = 0; i < n; i++)
    REMOTE_HandleBase(worker_id)[old_slots + i] = ts[i];
  REMOTE_CurHandle(worker_id) += n;
  return old_slots;
}

#define Yap_RecoverHandles(n, ts) Yap_RecoverHandles__(n, ts PASS_REGS)
#define Yap_RecoverSlots(n, ts) Yap_RecoverHandles__(n, ts PASS_REGS)

/// @brief Succeeds if it is to recover the space allocated for $n$ contiguos
/// slots starting at topHandle.
static inline bool Yap_RecoverHandles__(int n, yhandle_t topHandle USES_REGS);
static inline bool Yap_RecoverHandles__(int n, yhandle_t topHandle USES_REGS) {
  if (topHandle + n < REMOTE_CurHandle(worker_id))
    return false;
#ifdef DEBUG
  if (n > REMOTE_CurHandle(worker_id)) {
    Yap_Error(SYSTEM_ERROR_INTERNAL, 0,
              "Inconsistent slot state in Yap_RecoverHandles.", 0);
    return false;
  }
#endif
  REMOTE_CurHandle(worker_id) = topHandle;
  //fprintf(stderr,"RS %ld %s:%d\n", REMOTE_CurHandle(worker_id), __FILE__, __LINE__);
  return true;
}

#define Yap_PopSlot(ts) Yap_PopHandle__(ts PASS_REGS)
#define Yap_PopHandle(ts) Yap_PopHandle__(ts PASS_REGS)

/// @brief recovers the element at position $n$ dropping any other elements p
static inline Term Yap_PopHandle__(yhandle_t topHandle USES_REGS);
static inline Term Yap_PopHandle__(yhandle_t topHandle USES_REGS) {
  if (REMOTE_CurHandle(worker_id) < topHandle)
    return TermNil;
  else {
    REMOTE_CurHandle(worker_id) = topHandle;
    // fprintf(stderr,"RS %ld %s:%d\n", REMOTE_CurHandle(worker_id), __FILE__, __LINE__);
    return REMOTE_HandleBase(worker_id)[topHandle];
  }
}
#endif

/// @}


/*************************************************************************
 *									 *
 *	 YAP Prolog 							 *
 *									 *
 *	Yap Prolog was developed at NCCUP - Universidade do Porto	 *
 *									 *
 * Copyright L.Damas, V. Santos Costa and Universidade do Porto 1985--	 *
 *									 *
 **************************************************************************
 *									 *
 * File:		qlyw.c *
 * comments:	quick saver/loader					 *
 *									 *
 * Last rev:     $Date: 2011-08-29$,$Author: vsc $			 *
 * $Log: not supported by cvs2svn $					 *
 *									 *
 *************************************************************************/

/**
 *
 * @file qlyr.c
 *
 * @addtogroup SaveRestoreSupport
 * @{
 *
 */

#include "Foreign.h"
#include "absmi.h"
#include "alloc.h"
#include "attvar.h"
#include "iopreds.h"
#include "yapio.h"
#if HAVE_STRING_H
#include <string.h>
#endif

#include "qly.h"

static void RestoreEntries(PropEntry *, int USES_REGS);
static void CleanCode(PredEntry *USES_REGS);

static void GrowAtomTable(void) {
  CACHE_REGS
  UInt size = REMOTE_ExportAtomHashTableSize(worker_id);
  export_atom_hash_entry_t *p, *newt, *oldt = REMOTE_ExportAtomHashChain(worker_id);
  UInt new_size = size + (size > 1024 ? size : 1024);
  UInt i;

  newt = (export_atom_hash_entry_t *)calloc(new_size,
                                            sizeof(export_atom_hash_entry_t));
  if (!newt) {
    return;
  }
  p = oldt;
  for (i = 0; i < size; p++, i++) {
    Atom a = p->val;
    export_atom_hash_entry_t *newp;
    CELL hash;
    const unsigned char *apt;

    if (!a)
      continue;
    apt = RepAtom(a)->UStrOfAE;
    hash = HashFunction(apt) / (2 * sizeof(CELL)) % new_size;
    newp = newt + hash;
    while (newp->val) {
      newp++;
      if (newp == newt + new_size)
        newp = newt;
    }
    newp->val = a;
  }
  REMOTE_ExportAtomHashChain(worker_id) = newt;
  REMOTE_ExportAtomHashTableSize(worker_id) = new_size;
  free(oldt);
}

static void LookupAtom(Atom at) {
  CACHE_REGS
  const unsigned char *p = RepAtom(at)->UStrOfAE;
  CELL hash = HashFunction(p) % REMOTE_ExportAtomHashTableSize(worker_id);
  export_atom_hash_entry_t *a;

  a = REMOTE_ExportAtomHashChain(worker_id) + hash;
  while (a->val) {
    if (a->val == at) {
      return;
    }
    a++;
    if (a == REMOTE_ExportAtomHashChain(worker_id) + REMOTE_ExportAtomHashTableSize(worker_id))
      a = REMOTE_ExportAtomHashChain(worker_id);
  }
  a->val = at;
  REMOTE_ExportAtomHashTableNum(worker_id)++;
  if (REMOTE_ExportAtomHashTableNum(worker_id) > REMOTE_ExportAtomHashTableSize(worker_id) / 2) {
    GrowAtomTable();
    if (!REMOTE_ExportAtomHashChain(worker_id)) {
      return;
    }
  }
}

static void GrowFunctorTable(void) {
  CACHE_REGS
  UInt size = REMOTE_ExportFunctorHashTableSize(worker_id);
  export_functor_hash_entry_t *p, *newt, *oldt = REMOTE_ExportFunctorHashChain(worker_id);
  UInt new_size = size + (size > 1024 ? size : 1024);
  UInt i;

  newt = (export_functor_hash_entry_t *)calloc(
      new_size, sizeof(export_functor_hash_entry_t));
  if (!newt) {
    return;
  }
  p = oldt;
  for (i = 0; i < size; p++, i++) {
    Functor f = p->val;
    export_functor_hash_entry_t *newp;
    CELL hash;

    if (!f)
      continue;
    hash = ((CELL)(f)) / (2 * sizeof(CELL)) % new_size;
    newp = newt + hash;
    while (newp->val) {
      newp++;
      if (newp == newt + new_size)
        newp = newt;
    }
    newp->val = p->val;
    newp->arity = p->arity;
    newp->name = p->name;
  }
  REMOTE_ExportFunctorHashChain(worker_id) = newt;
  REMOTE_ExportFunctorHashTableSize(worker_id) = new_size;
  free(oldt);
}

static void LookupFunctor(Functor fun) {
  CACHE_REGS
  CELL hash =
      ((CELL)(fun)) / (2 * sizeof(CELL)) % REMOTE_ExportFunctorHashTableSize(worker_id);
  export_functor_hash_entry_t *f;
  Atom name = NameOfFunctor(fun);
  UInt arity = ArityOfFunctor(fun);

  f = REMOTE_ExportFunctorHashChain(worker_id) + hash;
  while (f->val) {
    if (f->val == fun) {
      return;
    }
    f++;
    if (f == REMOTE_ExportFunctorHashChain(worker_id) + REMOTE_ExportFunctorHashTableSize(worker_id))
      f = REMOTE_ExportFunctorHashChain(worker_id);
  }
  LookupAtom(name);
  f->val = fun;
  f->name = name;
  f->arity = arity;
  REMOTE_ExportFunctorHashTableNum(worker_id)++;
  if (REMOTE_ExportFunctorHashTableNum(worker_id) > REMOTE_ExportFunctorHashTableSize(worker_id) / 2) {
    GrowFunctorTable();
    if (!REMOTE_ExportFunctorHashChain(worker_id)) {
      return;
    }
  }
}

static void GrowPredTable(void) {
  CACHE_REGS
  UInt size = REMOTE_ExportPredEntryHashTableSize(worker_id);
  export_pred_entry_hash_entry_t *p, *newt,
      *oldt = REMOTE_ExportPredEntryHashChain(worker_id);
  UInt new_size = size + (size > 1024 ? size : 1024);
  UInt i;

  newt = (export_pred_entry_hash_entry_t *)calloc(
      new_size, sizeof(export_pred_entry_hash_entry_t));
  if (!newt) {
    return;
  }
  p = oldt;
  for (i = 0; i < size; p++, i++) {
    PredEntry *pe = p->val;
    export_pred_entry_hash_entry_t *newp;
    CELL hash;

    if (!pe)
      continue;
    hash = ((CELL)(pe)) / (2 * sizeof(CELL)) % new_size;
    newp = newt + hash;
    while (newp->val) {
      newp++;
      if (newp == newt + new_size)
        newp = newt;
    }
    newp->val = p->val;
    newp->arity = p->arity;
    newp->u_af.f = p->u_af.f;
    newp->module = p->module;
  }
  REMOTE_ExportPredEntryHashChain(worker_id) = newt;
  REMOTE_ExportPredEntryHashTableSize(worker_id) = new_size;
  free(oldt);
}

static void LookupPredEntry(PredEntry *pe) {
  CACHE_REGS
  CELL hash =
      (((CELL)(pe)) / (2 * sizeof(CELL))) % REMOTE_ExportPredEntryHashTableSize(worker_id);
  export_pred_entry_hash_entry_t *p;
  UInt arity = pe->ArityOfPE;

  p = REMOTE_ExportPredEntryHashChain(worker_id) + hash;
  while (p->val) {
    if (p->val == pe) {
      return;
    }
    p++;
    if (p ==
        REMOTE_ExportPredEntryHashChain(worker_id) + REMOTE_ExportPredEntryHashTableSize(worker_id))
      p = REMOTE_ExportPredEntryHashChain(worker_id);
  }
  p->arity = arity;
  p->val = pe;
  if (pe->ModuleOfPred != IDB_MODULE) {
    if (arity) {
      p->u_af.f = pe->FunctorOfPred;
      LookupFunctor(pe->FunctorOfPred);
    } else {
      p->u_af.a = (Atom)(pe->FunctorOfPred);
      LookupAtom((Atom)(pe->FunctorOfPred));
    }
  } else {
    if (pe->PredFlags & AtomDBPredFlag) {
      p->u_af.a = (Atom)(pe->FunctorOfPred);
      p->arity = (CELL)(-2);
      LookupAtom((Atom)(pe->FunctorOfPred));
    } else if (!(pe->PredFlags & NumberDBPredFlag)) {
      p->u_af.f = pe->FunctorOfPred;
      p->arity = (CELL)(-1);
      LookupFunctor(pe->FunctorOfPred);
    } else {
      p->u_af.f = pe->FunctorOfPred;
    }
  }
  if (pe->ModuleOfPred) {
    p->module = AtomOfTerm(pe->ModuleOfPred);
  } else {
    p->module = AtomProlog;
  }
  LookupAtom(p->module);
  REMOTE_ExportPredEntryHashTableNum(worker_id)++;
  if (REMOTE_ExportPredEntryHashTableNum(worker_id) >
      REMOTE_ExportPredEntryHashTableSize(worker_id) / 2) {
    GrowPredTable();
    if (!REMOTE_ExportPredEntryHashChain(worker_id)) {
      return;
    }
  }
}

static void GrowDBRefTable(void) {
  CACHE_REGS
  UInt size = REMOTE_ExportDBRefHashTableSize(worker_id);
  export_dbref_hash_entry_t *p, *newt, *oldt = REMOTE_ExportDBRefHashChain(worker_id);
  UInt new_size = size + (size > 1024 ? size : 1024);
  UInt i;

  newt = (export_dbref_hash_entry_t *)calloc(new_size,
                                             sizeof(export_dbref_hash_entry_t));
  if (!newt) {
    return;
  }
  p = oldt;
  for (i = 0; i < size; p++, i++) {
    DBRef dbr = p->val;
    export_dbref_hash_entry_t *newp;
    CELL hash;

    if (!dbr)
      continue;
    hash = ((CELL)(dbr)) / (2 * sizeof(CELL)) % new_size;
    newp = newt + hash;
    while (newp->val) {
      newp++;
      if (newp == newt + new_size)
        newp = newt;
    }
    newp->val = p->val;
    newp->sz = p->sz;
    newp->refs = p->refs;
  }
  REMOTE_ExportDBRefHashChain(worker_id) = newt;
  REMOTE_ExportDBRefHashTableSize(worker_id) = new_size;
  free(oldt);
}

static void LookupDBRef(DBRef ref) {
  CACHE_REGS
  CELL hash =
      ((CELL)(ref)) / (2 * sizeof(CELL)) % REMOTE_ExportDBRefHashTableSize(worker_id);
  export_dbref_hash_entry_t *a;

  a = REMOTE_ExportDBRefHashChain(worker_id) + hash;
  while (a->val) {
    if (a->val == ref) {
      a->refs++;
      return;
    }
    a++;
    if (a == REMOTE_ExportDBRefHashChain(worker_id) + REMOTE_ExportDBRefHashTableSize(worker_id))
      a = REMOTE_ExportDBRefHashChain(worker_id);
  }
  a->val = ref;
  a->sz = ((LogUpdClause *)ref)->ClSize;
  a->refs = 1;
  REMOTE_ExportDBRefHashTableNum(worker_id)++;
  if (REMOTE_ExportDBRefHashTableNum(worker_id) > REMOTE_ExportDBRefHashTableSize(worker_id) / 2) {
    GrowDBRefTable();
    if (!REMOTE_ExportDBRefHashChain(worker_id)) {
      return;
    }
  }
}

static void InitHash(void) {
  CACHE_REGS
  REMOTE_ExportFunctorHashTableNum(worker_id) = 0;
  REMOTE_ExportFunctorHashTableSize(worker_id) = EXPORT_FUNCTOR_TABLE_SIZE;
  REMOTE_ExportFunctorHashChain(worker_id) = (export_functor_hash_entry_t *)calloc(
      REMOTE_ExportFunctorHashTableSize(worker_id), sizeof(export_functor_hash_entry_t));
  REMOTE_ExportAtomHashTableNum(worker_id) = 0;
  REMOTE_ExportAtomHashTableSize(worker_id) = EXPORT_ATOM_TABLE_SIZE;
  REMOTE_ExportAtomHashChain(worker_id) = (export_atom_hash_entry_t *)calloc(
      REMOTE_ExportAtomHashTableSize(worker_id), sizeof(export_atom_hash_entry_t));
  REMOTE_ExportPredEntryHashTableNum(worker_id) = 0;
  REMOTE_ExportPredEntryHashTableSize(worker_id) = EXPORT_PRED_ENTRY_TABLE_SIZE;
  REMOTE_ExportPredEntryHashChain(worker_id) = (export_pred_entry_hash_entry_t *)calloc(
      REMOTE_ExportPredEntryHashTableSize(worker_id),
      sizeof(export_pred_entry_hash_entry_t));
  REMOTE_ExportDBRefHashTableNum(worker_id) = 0;
  REMOTE_ExportDBRefHashTableSize(worker_id) = EXPORT_DBREF_TABLE_SIZE;
  REMOTE_ExportDBRefHashChain(worker_id) = (export_dbref_hash_entry_t *)calloc(
      EXPORT_DBREF_TABLE_SIZE, sizeof(export_dbref_hash_entry_t));
}

static void CloseHash(void) {
  CACHE_REGS
  REMOTE_ExportFunctorHashTableNum(worker_id) = 0;
  REMOTE_ExportFunctorHashTableSize(worker_id) = 0L;
  free(REMOTE_ExportFunctorHashChain(worker_id));
  REMOTE_ExportAtomHashTableNum(worker_id) = 0;
  REMOTE_ExportAtomHashTableSize(worker_id) = 0L;
  free(REMOTE_ExportAtomHashChain(worker_id));
  REMOTE_ExportPredEntryHashTableNum(worker_id) = 0;
  REMOTE_ExportPredEntryHashTableSize(worker_id) = 0L;
  free(REMOTE_ExportPredEntryHashChain(worker_id));
  REMOTE_ExportDBRefHashTableNum(worker_id) = 0;
  REMOTE_ExportDBRefHashTableSize(worker_id) = 0L;
  free(REMOTE_ExportDBRefHashChain(worker_id));
}

static inline Atom AtomAdjust(Atom a) {
  LookupAtom(a);
  return a;
}

static inline Functor FuncAdjust(Functor f) {
  LookupFunctor(f);
  return f;
}

static inline Term AtomTermAdjust(Term t) {
  LookupAtom(AtomOfTerm(t));
  return t;
}

static inline Term TermToGlobalOrAtomAdjust(Term t) {
  if (t && IsAtomTerm(t))
    return AtomTermAdjust(t);
  return t;
}

#define IsOldCode(P) FALSE
#define IsOldCodeCellPtr(P) FALSE
#define IsOldDelay(P) FALSE
#define IsOldDelayPtr(P) FALSE
#define IsOldLocalInTR(P) FALSE
#define IsOldLocalInTRPtr(P) FALSE
#define IsOldGlobal(P) FALSE
#define IsOldGlobalPtr(P) FALSE
#define IsOldTrail(P) FALSE
#define IsOldTrailPtr(P) FALSE

#define CharP(X) ((char *)(X))

#define REINIT_LOCK(P)
#define REINIT_RWLOCK(P)
#define BlobTypeAdjust(P) (P)
#define NoAGCAtomAdjust(P) (P)
#define OrArgAdjust(P)
#define TabEntryAdjust(P)
#define IntegerAdjust(D) (D)
#define AddrAdjust(P) (P)
#define MFileAdjust(P) (P)
#define CodeVarAdjust(P) (P)
#define ConstantAdjust(P) (P)
#define ArityAdjust(P) (P)
#define DoubleInCodeAdjust(P)
#define IntegerInCodeAdjust(P)
#define OpcodeAdjust(P) (P)

static inline Term ModuleAdjust(Term t) {
  if (!t)
    return t;
  return AtomTermAdjust(t);
}

static inline PredEntry *PredEntryAdjust(PredEntry *pe) {
  LookupPredEntry(pe);
  return pe;
}

static inline PredEntry *PtoPredAdjust(PredEntry *pe) {
  LookupPredEntry(pe);
  return pe;
}

#define ExternalFunctionAdjust(P) (P)
#define DBRecordAdjust(P) (P)
#define ModEntryPtrAdjust(P) (P)
#define AtomEntryAdjust(P) (P)
#define GlobalEntryAdjust(P) (P)
#define BlobTermInCodeAdjust(P) (P)
#define CellPtoHeapAdjust(P) (P)
#define PtoAtomHashEntryAdjust(P) (P)
#define CellPtoHeapCellAdjust(P) (P)
#define CellPtoTRAdjust(P) (P)
#define CodeAddrAdjust(P) (P)
#define ConsultObjAdjust(P) (P)
#define DelayAddrAdjust(P) (P)
#define DelayAdjust(P) (P)
#define GlobalAdjust(P) (P)

#define DBRefAdjust(P, DoRef) DBRefAdjust__(P PASS_REGS)
static inline DBRef DBRefAdjust__(DBRef dbt USES_REGS) {
  LookupDBRef(dbt);
  return dbt;
}

#define DBRefPAdjust(P) (P)
#define DBTermAdjust(P) (P)
#define LUIndexAdjust(P) (P)
#define SIndexAdjust(P) (P)
#define LocalAddrAdjust(P) (P)
#define GlobalAddrAdjust(P) (P)
#define OpListAdjust(P) (P)
#define PtoLUCAdjust(P) (P)
#define PtoStCAdjust(P) (P)
#define PtoArrayEAdjust(P) (P)
#define PtoArraySAdjust(P) (P)
#define PtoGlobalEAdjust(P) (P)
#define PtoDelayAdjust(P) (P)
#define PtoGloAdjust(P) (P)
#define PtoLocAdjust(P) (P)
#define PtoHeapCellAdjust(P) (P)
#define TermToGlobalAdjust(P) (P)
#define PtoOpAdjust(P) (P)
#define PtoLUClauseAdjust(P) (P)
#define PtoLUIndexAdjust(P) (P)
#define PtoDBTLAdjust(P) (P)
#define PtoPtoPredAdjust(P) (P)
#define OpRTableAdjust(P) (P)
#define OpEntryAdjust(P) (P)
#define PropAdjust(P) (P)
#define TrailAddrAdjust(P) (P)
#define XAdjust(P) (P)
#define YAdjust(P) (P)
#define HoldEntryAdjust(P) (P)
#define CodeCharPAdjust(P) (P)
#define CodeConstCharPAdjust(P) (P)
#define CodeVoidPAdjust(P) (P)
#define HaltHookAdjust(P) (P)

#define recompute_mask(dbr)

#define rehash(oldcode, NOfE, KindOfEntries)

static void RestoreFlags(UInt NFlags) {}

#include "rheap.h"

static void RestoreHashPreds(USES_REGS1) {}

static void RestoreAtomList(Atom atm USES_REGS) {}

static size_t save_bytes(FILE *stream, void *ptr, size_t sz) {
  return fwrite(ptr, sz, 1, stream);
}

static size_t save_byte(FILE *stream, int byte) {
  fputc(byte, stream);
  return 1;
}

static size_t save_bits16(FILE *stream, BITS16 val) {
  BITS16 v = val;
  return save_bytes(stream, &v, sizeof(BITS16));
}

static size_t save_UInt(FILE *stream, UInt val) {
  UInt v = val;
  return save_bytes(stream, &v, sizeof(UInt));
}

static size_t save_Int(FILE *stream, Int val) {
  Int v = val;
  return save_bytes(stream, &v, sizeof(Int));
}

static size_t save_tag(FILE *stream, qlf_tag_t tag) {
  return save_byte(stream, tag);
}

static size_t save_predFlags(FILE *stream, pred_flags_t predFlags) {
  pred_flags_t v = predFlags;
  return save_bytes(stream, &v, sizeof(pred_flags_t));
}

static int SaveHash(FILE *stream) {
  CACHE_REGS
  UInt i;
  /* first, current opcodes */
  CHECK(save_tag(stream, QLY_START_X));
  save_UInt(stream, (UInt)&ARG1);
  CHECK(save_tag(stream, QLY_START_OPCODES));
  save_Int(stream, _std_top);
  for (i = 0; i <= _std_top; i++) {
    save_UInt(stream, (UInt)Yap_opcode(i));
  }
  CHECK(save_tag(stream, QLY_START_ATOMS));
  CHECK(save_UInt(stream, REMOTE_ExportAtomHashTableNum(worker_id)));
  for (i = 0; i < REMOTE_ExportAtomHashTableSize(worker_id); i++) {
    export_atom_hash_entry_t *a = REMOTE_ExportAtomHashChain(worker_id) + i;
    if (a->val) {
      Atom at = a->val;
      CHECK(save_UInt(stream, (UInt)at));
      CHECK(save_tag(stream, QLY_ATOM));
      CHECK(save_UInt(stream, strlen((char *)RepAtom(at)->StrOfAE)));
      CHECK(save_bytes(stream, (char *)at->StrOfAE,
                       (strlen((char *)at->StrOfAE) + 1) * sizeof(char)));
    }
  }
  save_tag(stream, QLY_START_FUNCTORS);
  save_UInt(stream, REMOTE_ExportFunctorHashTableNum(worker_id));
  for (i = 0; i < REMOTE_ExportFunctorHashTableSize(worker_id); i++) {
    export_functor_hash_entry_t *f = REMOTE_ExportFunctorHashChain(worker_id) + i;
    if (!(f->val))
      continue;
    CHECK(save_UInt(stream, (UInt)(f->val)));
    CHECK(save_UInt(stream, f->arity));
    CHECK(save_UInt(stream, (CELL)(f->name)));
  }
  save_tag(stream, QLY_START_PRED_ENTRIES);
  save_UInt(stream, REMOTE_ExportPredEntryHashTableNum(worker_id));
  for (i = 0; i < REMOTE_ExportPredEntryHashTableSize(worker_id); i++) {
    export_pred_entry_hash_entry_t *p = REMOTE_ExportPredEntryHashChain(worker_id) + i;
    if (!(p->val))
      continue;
    CHECK(save_UInt(stream, (UInt)(p->val)));
    CHECK(save_UInt(stream, p->arity));
    CHECK(save_UInt(stream, (UInt)p->module));
    CHECK(save_UInt(stream, (UInt)p->u_af.f));
  }
  save_tag(stream, QLY_START_DBREFS);
  save_UInt(stream, REMOTE_ExportDBRefHashTableNum(worker_id));
  for (i = 0; i < REMOTE_ExportDBRefHashTableSize(worker_id); i++) {
    export_dbref_hash_entry_t *p = REMOTE_ExportDBRefHashChain(worker_id) + i;
    if (p->val) {
      CHECK(save_UInt(stream, (UInt)(p->val)));
      CHECK(save_UInt(stream, p->sz));
      CHECK(save_UInt(stream, p->refs));
    }
  }
  save_tag(stream, QLY_FAILCODE);
  save_UInt(stream, (UInt)FAILCODE);
  return 1;
}

static size_t save_clauses(FILE *stream, PredEntry *pp) {
  yamop *FirstC, *LastC;

  FirstC = pp->FirstClause;
  LastC = pp->LastClause;
  if (FirstC == NULL && LastC == NULL) {
    return 1;
  }
  if (pp->PredFlags & LogUpdatePredFlag) {
    LogUpdClause *cl = ClauseCodeToLogUpdClause(FirstC);

    while (cl != NULL) {
      if (IN_BETWEEN(cl->ClTimeStart, pp->TimeStampOfPred, cl->ClTimeEnd)) {
        UInt size = cl->ClSize;
        CHECK(save_tag(stream, QLY_START_LU_CLAUSE));
        CHECK(save_UInt(stream, (UInt)cl));
        CHECK(save_UInt(stream, size));
        CHECK(save_bytes(stream, cl, size));
      }
      cl = cl->ClNext;
    }
    CHECK(save_tag(stream, QLY_END_LU_CLAUSES));
  } else if (pp->PredFlags & MegaClausePredFlag) {
    MegaClause *cl = ClauseCodeToMegaClause(FirstC);
    UInt size = cl->ClSize;

    CHECK(save_UInt(stream, (UInt)cl));
    CHECK(save_UInt(stream, (UInt)(cl->ClFlags)));
    CHECK(save_UInt(stream, size));
    CHECK(save_bytes(stream, cl, size));
  } else if (pp->PredFlags & DynamicPredFlag) {
    yamop *cl = FirstC;

    do {
      DynamicClause *dcl = ClauseCodeToDynamicClause(cl);
      UInt size = dcl->ClSize;

      CHECK(save_UInt(stream, (UInt)cl));
      CHECK(save_UInt(stream, size));
      CHECK(save_bytes(stream, dcl, size));
      if (cl == LastC)
        return 1;
      cl = NextDynamicClause(cl);
    } while (TRUE);
  } else {
    StaticClause *cl = ClauseCodeToStaticClause(FirstC);

    if (pp->PredFlags & SYSTEM_PRED_FLAGS) {
      return 1;
    }
    do {
      UInt size = cl->ClSize;

      CHECK(save_UInt(stream, (UInt)cl));
      CHECK(save_UInt(stream, size));
      CHECK(save_bytes(stream, cl, size));
      if (cl->ClCode == LastC)
        return 1;
      cl = cl->ClNext;
    } while (TRUE);
  }
  return 1;
}

static size_t save_pred(FILE *stream, PredEntry *ap) {
  CHECK(save_UInt(stream, (UInt)ap));
  CHECK(save_predFlags(stream, ap->PredFlags));
  if (ap->PredFlags & ForeignPredFlags)
    return 1;
  CHECK(save_UInt(stream, ap->NOfClauses));
  CHECK(save_UInt(stream, ap->src.IndxId));
  CHECK(save_UInt(stream, ap->TimeStampOfPred));
  return save_clauses(stream, ap);
}

static int clean_pred(PredEntry *pp USES_REGS) {
  if (pp->PredFlags & ForeignPredFlags) {
    return true;
  } else {
    CleanClauses(pp->FirstClause, pp->LastClause,
                 pp PASS_REGS);
  }
  return true;
}

static size_t mark_pred(PredEntry *ap) {
  CACHE_REGS
  if (ap->ModuleOfPred != IDB_MODULE) {
    if (ap->ArityOfPE) {
      FuncAdjust(ap->FunctorOfPred);
    } else {
      AtomAdjust((Atom)(ap->FunctorOfPred));
    }
  } else {
    if (ap->PredFlags & AtomDBPredFlag) {
      AtomAdjust((Atom)(ap->FunctorOfPred));
    } else if (!(ap->PredFlags & NumberDBPredFlag)) {
      FuncAdjust(ap->FunctorOfPred);
    }
  }
  if (!(ap->PredFlags & (MultiFileFlag | NumberDBPredFlag)) &&
      ap->src.OwnerFile) {
    AtomAdjust(ap->src.OwnerFile);
  }
  //  fprintf(stderr, "> %lx %lx: ", ap->PredFlags, ap->PredFlags & ForeignPredFlags); (Yap_DebugWriteIndicator(ap));
  CHECK(clean_pred(ap PASS_REGS));
  return 1;
}

static size_t mark_ops(FILE *stream, Term mod) {
  OpEntry *op = OpList;
  while (op) {
    if (!mod || op->OpModule == mod) {
      AtomAdjust(op->OpName);
      if (op->OpModule)
        AtomTermAdjust(op->OpModule);
    }
    op = op->OpNext;
  }
  return 1;
}

static size_t save_ops(FILE *stream, Term mod) {
  OpEntry *op = OpList;
  while (op) {
    if (!mod || op->OpModule == mod) {
      CHECK(save_tag(stream, QLY_NEW_OP));
      save_UInt(stream, (UInt)op->OpName);
      save_UInt(stream, (UInt)op->OpModule);
      save_bits16(stream, op->Prefix);
      save_bits16(stream, op->Infix);
      save_bits16(stream, op->Posfix);
    }
    op = op->OpNext;
  }
  CHECK(save_tag(stream, QLY_END_OPS));
  return 1;
}

static size_t save_header(FILE *stream, char type[]) {
  char msg[2048];

  memset(msg, 0, 2048);
  sprintf(msg,
          "#!/bin/sh\nexec_dir=${YAPBINDIR:-%s}\nexec $exec_dir/yap $0 "
          "\"$@\"\n%s %s\n",
          YAP_BINDIR, type, YAP_FULL_VERSION);
  return save_bytes(stream, msg, 2048);
}

static size_t save_module(FILE *stream, Term mod) {
  PredEntry *ap = Yap_ModulePred(mod);
  save_header(stream, "saved module,");
  InitHash();
  ModuleAdjust(mod);
  while (ap) {
    ap = PredEntryAdjust(ap);
    CHECK(mark_pred(ap));
    ap = ap->NextPredOfModule;
  }
  /* just to make sure */
  mark_ops(stream, mod);
  SaveHash(stream);
  CHECK(save_tag(stream, QLY_START_MODULE));
  CHECK(save_UInt(stream, (UInt)mod));
  ap = Yap_ModulePred(mod);
  while (ap) {
    CHECK(save_tag(stream, QLY_START_PREDICATE));
    CHECK(save_pred(stream, ap));
    ap = ap->NextPredOfModule;
  }
  CHECK(save_tag(stream, QLY_END_PREDICATES));
  CHECK(save_tag(stream, QLY_END_MODULES));
  save_ops(stream, mod);
  CloseHash();
  return 1;
}

static size_t save_program(FILE *stream) {
  ModEntry *me = CurrentModules;

  InitHash();
  save_header(stream, "saved state,");
  /* should we allow the user to see hidden predicates? */
  while (me) {
    PredEntry *pp;
    pp = me->PredForME;
    AtomAdjust(me->AtomOfME);
    while (pp != NULL) {
#if DEBUG
//    Yap_PrintPredName( pp );
#endif
      pp = PredEntryAdjust(pp);
      CHECK(mark_pred(pp));
      pp = pp->NextPredOfModule;
    }
    me = me->NextME;
  }

  /* just to make sure */
  mark_ops(stream, 0);
  SaveHash(stream);
  me = CurrentModules;
  while (me) {
    PredEntry *pp;
    pp = me->PredForME;
    CHECK(save_tag(stream, QLY_START_MODULE));
    CHECK(save_UInt(stream, (UInt)MkAtomTerm(me->AtomOfME)));
    while (pp != NULL) {
      CHECK(save_tag(stream, QLY_START_PREDICATE));
      CHECK(save_pred(stream, pp));
      pp = pp->NextPredOfModule;
    }
    CHECK(save_tag(stream, QLY_END_PREDICATES));
    me = me->NextME;
  }
  CHECK(save_tag(stream, QLY_END_MODULES));
  save_ops(stream, 0);
  CloseHash();
  return 1;
}

static size_t save_file(FILE *stream, Atom FileName) {
  ModEntry *me = CurrentModules;

  InitHash();
  save_header(stream, "saved file,");
  /* should we allow the user to see hidden predicates? */
  while (me) {
    PredEntry *pp;
    pp = me->PredForME;
    AtomAdjust(me->AtomOfME);
    while (pp != NULL) {
      pp = PredEntryAdjust(pp);
      if (pp &&
          !(pp->PredFlags & (MultiFileFlag | NumberDBPredFlag | AtomDBPredFlag |
                             CPredFlag | AsmPredFlag | UserCPredFlag)) &&
          pp->ModuleOfPred != IDB_MODULE && pp->src.OwnerFile == FileName) {
        CHECK(mark_pred(pp));
      }
      pp = pp->NextPredOfModule;
    }
    me = me->NextME;
  }

  /* just to make sure */
  mark_ops(stream, 0);
  SaveHash(stream);
  me = CurrentModules;
  while (me) {
    PredEntry *pp;
    pp = me->PredForME;
    CHECK(save_tag(stream, QLY_START_MODULE));
    CHECK(save_UInt(stream, (UInt)MkAtomTerm(me->AtomOfME)));
    while (pp != NULL) {
      if (pp &&
          !(pp->PredFlags & (MultiFileFlag | NumberDBPredFlag | AtomDBPredFlag |
                             CPredFlag | AsmPredFlag | UserCPredFlag)) &&
          pp->src.OwnerFile == FileName) {
        CHECK(save_tag(stream, QLY_START_PREDICATE));
        CHECK(save_pred(stream, pp));
      }
      pp = pp->NextPredOfModule;
    }
    CHECK(save_tag(stream, QLY_END_PREDICATES));
    me = me->NextME;
  }
  CHECK(save_tag(stream, QLY_END_MODULES));
  save_ops(stream, 0);
  CloseHash();
  return 1;
}

static Int qsave_module_preds(USES_REGS1) {
  FILE *stream;
  Term tmod = Deref(ARG2);
  Term t1 = Deref(ARG1);

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, "save_module/3");
    return FALSE;
  }
  if (!IsAtomTerm(t1)) {
    Yap_Error(TYPE_ERROR_ATOM, t1, "save_module/3");
    return (FALSE);
  }
  if (!(stream = Yap_GetOutputStream(t1, "save_module"))) {
    return FALSE;
  }
  if (IsVarTerm(tmod)) {
    Yap_Error(INSTANTIATION_ERROR, tmod, "save_module/2");
    return FALSE;
  }
  if (!IsAtomTerm(tmod)) {
    Yap_Error(TYPE_ERROR_ATOM, tmod, "save_module/2");
    return FALSE;
  }
  return save_module(stream, tmod) != 0;
}

static Int qsave_program(USES_REGS1) {
  FILE *stream;
  Term t1 = Deref(ARG1);

  if (!(stream = Yap_GetOutputStream(t1, "save_program"))) {
    return FALSE;
  }
  return save_program(stream) != 0;
}

static Int qsave_file(USES_REGS1) {
  FILE *stream;
  Term t1 = Deref(ARG1);
  Term tfile = Deref(ARG2);

  if (!(stream = Yap_GetOutputStream(t1, "save_file/2"))) {
    return FALSE;
  }
  if (IsVarTerm(tfile)) {
    Yap_Error(INSTANTIATION_ERROR, tfile, "save_file/2");
    return FALSE;
  }
  if (!IsAtomTerm(tfile)) {
    Yap_Error(TYPE_ERROR_ATOM, tfile, "save_file/2");
    return FALSE;
  }
  return save_file(stream, AtomOfTerm(tfile)) != 0;
}

void Yap_InitQLY(void) {
  Yap_InitCPred("$qsave_module_preds", 2, qsave_module_preds,
                SyncPredFlag | UserCPredFlag);
  Yap_InitCPred("$qsave_program", 1, qsave_program,
                SyncPredFlag | UserCPredFlag);
  Yap_InitCPred("$qsave_file_preds", 2, qsave_file,
                SyncPredFlag | UserCPredFlag);
  if (FALSE) {
    restore_codes();
  }
}

/// @}

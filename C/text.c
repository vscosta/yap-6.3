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
* File:		strings.c						 *
* comments:	General-conversion of character sequences.		 *
*									 *
* Last rev:     $Date: 2008-07-24 16:02:00 $,$Author: vsc $	     	 *
*									 *
*************************************************************************/

#include "Yap.h"
#include "YapHeap.h"
#include "YapText.h"
#include "Yatom.h"
#include "eval.h"
#include "yapio.h"

#include <YapText.h>
#include <string.h>
#include <wchar.h>

#ifndef HAVE_WCSNLEN
inline static size_t min_size(size_t i, size_t j) { return (i < j ? i : j); }
#define wcsnlen(S, N) min_size(N, wcslen(S))
#endif

#ifndef NAN
#define NAN (0.0 / 0.0)
#endif

#define  MAX_PATHNAME 2048


typedef struct TextBuffer_manager {
  void *buf, *ptr;
  size_t sz;
  struct TextBuffer_manager *prev;
  int lvl;
} text_buffer_t;

int lvl;

/**
 * TextBuffer is allocated as a chain of blocks, They area
 * recovered at the end if the translation.
 */
INLINE_ONLY  inline int init_alloc(int line)  {
  //  printf("l=%d\n",lvl);
  if (lvl )
    return;
  while (LOCAL_TextBuffer->prev ) {
    struct TextBuffer_manager *old = LOCAL_TextBuffer;
    LOCAL_TextBuffer = LOCAL_TextBuffer->prev;
    free(old);
  }
  LOCAL_TextBuffer->sz = (YAP_FILENAME_MAX + 1);
  LOCAL_TextBuffer->buf = LOCAL_TextBuffer->ptr = (void *)(LOCAL_TextBuffer + 1 );
  return lvl++;
}
 
INLINE_ONLY inline int mark_stack(void) { 
return lvl; }

INLINE_ONLY inline void restore_stack(int i ) {lvl = i;}		\
INLINE_ONLY inline void unprotect_stack(int i) { 
lvl = i;}

static void *Malloc(size_t sz USES_REGS) {
  sz = ALIGN_BY_TYPE(sz, CELL);
  void *o = LOCAL_TextBuffer->ptr;
  if ((char*)LOCAL_TextBuffer->ptr+sz>(char*)LOCAL_TextBuffer->buf + LOCAL_TextBuffer->sz) {
    size_t nsz = max(sz*4/3,YAP_FILENAME_MAX + 1);
    struct TextBuffer_manager *new = malloc(sizeof(struct TextBuffer_manager)+nsz);
      new->prev = LOCAL_TextBuffer;
      new->buf = (struct TextBuffer_manager *)new+1;
      new->ptr = new->buf + sz;
     new->sz = nsz;
     LOCAL_TextBuffer= new;
      return new->buf; 
  } 
  LOCAL_TextBuffer->ptr += sz;
 return o;
}

 void *Yap_InitTextAllocator( void )
{
  struct TextBuffer_manager *new = malloc(sizeof(struct TextBuffer_manager)\
					  +MAX_PATHNAME*2 );
  new->prev = NULL;
  new->ptr = new->buf = (struct TextBuffer_manager *)new+1;
  new->sz = MAX_PATHNAME*2;
  LOCAL_TextBuffer = new;
  new->lvl = 0;
  return  new;
}



static size_t MaxTmp(USES_REGS1) {

  return ((char*)LOCAL_TextBuffer->buf + LOCAL_TextBuffer->sz) - (char*)LOCAL_TextBuffer->ptr;
}

static Term Globalize(Term v USES_REGS) {
  if (!IsVarTerm(v = Deref(v))) {
    return v;
  }
  if (VarOfTerm(v) > HR && VarOfTerm(v) < LCL0) {
    Bind_Local(VarOfTerm(v), MkVarTerm());
    v = Deref(v);
  }
  return v;
}

static Int SkipListCodes(unsigned char **bufp, Term *l, Term **tailp,
                         Int *atoms, bool *wide, seq_tv_t *inp USES_REGS) {
  Int length = 0;
  Term *s; /* slow */
  Term v;  /* temporary */
  *wide = false;
  unsigned char *st0 = *bufp, *st;

  if (!st0) {
    st0 = Malloc(0);
  }

  do_derefa(v, l, derefa_unk, derefa_nonvar);
  *tailp = l;
  s = l;

  *bufp = st = st0;

  if (*l == TermNil) {
    st[0] = '\0';
    return 0;
  }
  if (IsPairTerm(*l)) {
    Term hd0 = HeadOfTerm(*l);
    if (IsVarTerm(hd0)) {
      return -INSTANTIATION_ERROR;
    }
    // are we looking for atoms/codes?
    // whatever the case, we should be consistent throughout,
    // so we should be consistent with the first arg.
    if (*atoms == 1) {
      if (!IsIntegerTerm(hd0)) {
        return -INSTANTIATION_ERROR;
      }
    } else if (*atoms == 2) {
      if (!IsAtomTerm(hd0)) {
        return -TYPE_ERROR_ATOM;
      }
    }

    do {
      int ch;
      length++;
      {
        Term hd = Deref(RepPair(*l)[0]);
        if (IsVarTerm(hd)) {
          return -INSTANTIATION_ERROR;
        } else if (IsAtomTerm(hd)) {
          (*atoms)++;
          if (*atoms < length) {
            *tailp = l;
            return -TYPE_ERROR_NUMBER;
          }
          if (IsWideAtom(AtomOfTerm(hd))) {
            int ch;
            if ((RepAtom(AtomOfTerm(hd))->WStrOfAE)[1] != '\0') {
              length = -REPRESENTATION_ERROR_CHARACTER;
            }
            ch = RepAtom(AtomOfTerm(hd))->WStrOfAE[0];
            *wide = true;
          } else {
            AtomEntry *ae = RepAtom(AtomOfTerm(hd));
            if ((ae->StrOfAE)[1] != '\0') {
              length = -REPRESENTATION_ERROR_CHARACTER;
            } else {
              ch = RepAtom(AtomOfTerm(hd))->StrOfAE[0];
              *wide |= ch > 0x80;
            }
          }
        } else if (IsIntegerTerm(hd)) {
          ch = IntegerOfTerm(hd);
          if (*atoms)
            length = -TYPE_ERROR_ATOM;
          else if (ch < 0) {
            *tailp = l;
            length = -DOMAIN_ERROR_NOT_LESS_THAN_ZERO;
          } else {
            *wide |= ch > 0x80;
          }
        } else {
          length = -TYPE_ERROR_INTEGER;
        }
        if (length < 0) {
          *tailp = l;
          return length;
        }
      }
      // now copy char to buffer
      int chsz = put_utf8(st, ch);
      if (chsz > 0) {
        st += chsz;
      }
      l = RepPair(*l) + 1;
      do_derefa(v, l, derefa2_unk, derefa2_nonvar);
    } while (*l != *s && IsPairTerm(*l));
  }
  if (IsVarTerm(*l)) {
    return -INSTANTIATION_ERROR;
  }
  if (*l != TermNil) {
    return -TYPE_ERROR_LIST;
  }
  st[0] = '\0';
  Malloc((st - st0) + 1);
  *tailp = l;

  return length;
}

static unsigned char *latin2utf8(seq_tv_t *inp, size_t *lengp) {
  unsigned char *b0 = inp->val.uc;
  size_t sz = *lengp = strlen(inp->val.c);
  sz *= 2;
  int ch;
  unsigned char *buf = Malloc(sz + 1), *pt = buf;
  *lengp = strlen(inp->val.c);
  if (!buf)
    return NULL;
  while ((ch = *b0++)) {
    int off = put_utf8(pt, ch);
    if (off < 0)
      continue;
    pt += off;
  }
  *pt++ = '\0';
  return buf;
}

static unsigned char *wchar2utf8(seq_tv_t *inp, size_t *lengp) {
  *lengp = wcslen(inp->val.w);
  size_t sz = *lengp * 4;
  wchar_t *b0 = inp->val.w;
  unsigned char *buf = Malloc(sz + 1), *pt = buf;
  int ch;
  if (!buf)
    return NULL;
  while ((ch = *b0++))
    pt += put_utf8(pt, ch);
  *pt++ = '\0';
  return buf;
}

static void *slice(size_t min, size_t max, unsigned char *buf USES_REGS);

static unsigned char *to_buffer(unsigned char *buf, Term t, seq_tv_t *inp,
                                bool *widep, Int *atoms,
                                size_t *lenp USES_REGS) {
  CELL *r = NULL;
  Int n;

  if (!buf) {
    inp->max = *lenp;
  }
  unsigned char *bufc = buf;
  n = SkipListCodes(&bufc, &t, &r, atoms, widep, inp PASS_REGS);
  if (n < 0) {
    LOCAL_Error_TYPE = -n;
    LOCAL_Error_Term = *r;
    return NULL;
  }
  *lenp = n;
  return bufc;
}

static unsigned char *Yap_ListOfCodesToBuffer(unsigned char *buf, Term t,
                                              seq_tv_t *inp, bool *widep,
                                              size_t *lenp USES_REGS) {
  Int atoms = 1; // we only want lists of atoms
  return to_buffer(buf, t, inp, widep, &atoms, lenp PASS_REGS);
}

static unsigned char *Yap_ListOfAtomsToBuffer(unsigned char *buf, Term t,
                                              seq_tv_t *inp, bool *widep,
                                              size_t *lenp USES_REGS) {
  Int atoms = 2; // we only want lists of integer codes
  return to_buffer(buf, t, inp, widep, &atoms, lenp PASS_REGS);
}

static unsigned char *Yap_ListToBuffer(unsigned char *buf, Term t,
                                       seq_tv_t *inp, bool *widep,
                                       size_t *lenp USES_REGS) {
  Int atoms = 0; // we accept both types of lists.
  return to_buffer(buf, t, inp, widep, &atoms, lenp PASS_REGS);
}

#if USE_GEN_TYPE_ERROR
static yap_error_number gen_type_error(int flags) {
  if ((flags & (YAP_STRING_STRING | YAP_STRING_ATOM | YAP_STRING_INT |
                YAP_STRING_FLOAT | YAP_STRING_ATOMS_CODES | YAP_STRING_BIG)) ==
      (YAP_STRING_STRING | YAP_STRING_ATOM | YAP_STRING_INT | YAP_STRING_FLOAT |
       YAP_STRING_ATOMS_CODES | YAP_STRING_BIG))
    return TYPE_ERROR_TEXT;
  if ((flags & (YAP_STRING_STRING | YAP_STRING_ATOM | YAP_STRING_INT |
                YAP_STRING_FLOAT | YAP_STRING_BIG)) ==
      (YAP_STRING_STRING | YAP_STRING_ATOM | YAP_STRING_INT | YAP_STRING_FLOAT |
       YAP_STRING_BIG))
    return TYPE_ERROR_ATOMIC;
  if ((flags & (YAP_STRING_INT | YAP_STRING_FLOAT | YAP_STRING_BIG)) ==
      (YAP_STRING_INT | YAP_STRING_FLOAT | YAP_STRING_BIG))
    return TYPE_ERROR_NUMBER;
  if (flags & YAP_STRING_ATOM)
    return TYPE_ERROR_ATOM;
  if (flags & YAP_STRING_STRING)
    return TYPE_ERROR_STRING;
  if (flags & (YAP_STRING_CODES | YAP_STRING_ATOMS))
    return TYPE_ERROR_LIST;
  return TYPE_ERROR_NUMBER;
}
#endif

unsigned char *Yap_readText(seq_tv_t *inp, size_t *lengp) {
  unsigned char *s0 = NULL;
  bool wide;

  /* we know what the term is */
  if (!(inp->type & (YAP_STRING_CHARS | YAP_STRING_WCHARS))) {
    if (!(inp->type & YAP_STRING_TERM)) {
      if (IsVarTerm(inp->val.t)) {
        LOCAL_Error_TYPE = INSTANTIATION_ERROR;
      } else if (!IsAtomTerm(inp->val.t) && inp->type == YAP_STRING_ATOM) {
        LOCAL_Error_TYPE = TYPE_ERROR_ATOM;
      } else if (!IsStringTerm(inp->val.t) && inp->type == YAP_STRING_STRING) {
        LOCAL_Error_TYPE = TYPE_ERROR_STRING;
      } else if (!IsPairOrNilTerm(inp->val.t) && !IsStringTerm(inp->val.t) &&
                 inp->type == (YAP_STRING_ATOMS_CODES | YAP_STRING_STRING)) {
        LOCAL_Error_TYPE = TYPE_ERROR_LIST;
      } else if (!IsNumTerm(inp->val.t) &&
                 (inp->type & (YAP_STRING_INT | YAP_STRING_FLOAT |
                               YAP_STRING_BIG)) == inp->type) {
        LOCAL_Error_TYPE = TYPE_ERROR_NUMBER;
      }
      LOCAL_Error_Term = inp->val.t;
    }
  }
  if (LOCAL_Error_TYPE != YAP_NO_ERROR)
    return NULL;

  if (IsAtomTerm(inp->val.t) && inp->type & YAP_STRING_ATOM) {
    // this is a term, extract to a buffer, and representation is wide
    // Yap_DebugPlWriteln(inp->val.t);
    Atom at = AtomOfTerm(inp->val.t);
    if (IsWideAtom(at)) {
      inp->val.w = at->WStrOfAE;
      return wchar2utf8(inp, lengp);
    } else {
      inp->val.c = at->StrOfAE;
      return latin2utf8(inp, lengp);
    }
  }
  if (IsStringTerm(inp->val.t) && inp->type & YAP_STRING_STRING) {
    // this is a term, extract to a buffer, and representation is wide
    // Yap_DebugPlWriteln(inp->val.t);
    return (unsigned char *)UStringOfTerm(inp->val.t);
  }
  if (((inp->type & (YAP_STRING_CODES | YAP_STRING_ATOMS)) ==
       (YAP_STRING_CODES | YAP_STRING_ATOMS)) &&
      IsPairOrNilTerm(inp->val.t)) {
    // Yap_DebugPlWriteln(inp->val.t);
    return inp->val.uc =
               Yap_ListToBuffer(s0, inp->val.t, inp, &wide, lengp PASS_REGS);
    // this is a term, extract to a sfer, and representation is wide
  }
  if (inp->type & YAP_STRING_CODES && IsPairOrNilTerm(inp->val.t)) {
    // Yap_DebugPlWriteln(inp->val.t);
    return inp->val.uc = Yap_ListOfCodesToBuffer(s0, inp->val.t, inp, &wide,
                                                 lengp PASS_REGS);
    // this is a term, extract to a sfer, and representation is wide
  }
  if (inp->type & YAP_STRING_ATOMS && IsPairOrNilTerm(inp->val.t)) {
    // Yap_DebugPlWriteln(inp->val.t);
    return inp->val.uc = Yap_ListOfAtomsToBuffer(s0, inp->val.t, inp, &wide,
                                                 lengp PASS_REGS);
    // this is a term, extract to a buffer, and representation is wide
  }
  if (inp->type & YAP_STRING_INT && IsIntegerTerm(inp->val.t)) {
    // ASCII, so both LATIN1 and UTF-8
    // Yap_DebugPlWriteln(inp->val.t);
    char *s;
    if (s0)
      s = (char *)s0;
    else
      s = Malloc(0);
    if (snprintf(s, MaxTmp(PASS_REGS1) - 1, Int_FORMAT,
                 IntegerOfTerm(inp->val.t)) < 0) {
      AUX_ERROR(inp->val.t, 2 * MaxTmp(PASS_REGS1), s, char);
    }
    *lengp = strlen(s);
    Malloc(*lengp);
    return inp->val.uc = (unsigned char *)s;
  }
  if (inp->type & YAP_STRING_FLOAT && IsFloatTerm(inp->val.t)) {
    char *s;
    // Yap_DebugPlWriteln(inp->val.t);
    if (s0)
      s = (char *)s0;
    else
      s = Malloc(0);
    AUX_ERROR(inp->val.t, MaxTmp(PASS_REGS1), s, char);
    if (!Yap_FormatFloat(FloatOfTerm(inp->val.t), &s, MaxTmp() - 1)) {
      AUX_ERROR(inp->val.t, 2 * MaxTmp(PASS_REGS1), s, char);
    }
    *lengp = strlen(s);
    Malloc(*lengp);
    return inp->val.uc = (unsigned char *)s;
  }
#if USE_GMP
  if (inp->type & YAP_STRING_BIG && IsBigIntTerm(inp->val.t)) {
    // Yap_DebugPlWriteln(inp->val.t);
    char *s;
    if (s0)
      s = 0;
    else
      s = Malloc(0);
    if (!Yap_mpz_to_string(Yap_BigIntOfTerm(inp->val.t), s, MaxTmp() - 1, 10)) {
      AUX_ERROR(inp->val.t, MaxTmp(PASS_REGS1), s, char);
    }
    *lengp = strlen(s);
    Malloc(*lengp);
    return inp->val.uc = (unsigned char *)s;
  }
#endif
  if (inp->type & YAP_STRING_TERM) {
    // Yap_DebugPlWriteln(inp->val.t);
    char *s = (char *)Yap_TermToString(inp->val.t, lengp, ENC_ISO_UTF8, 0);
    return inp->val.uc = (unsigned char *)s;
  }
  if (inp->type & YAP_STRING_CHARS) {
    // printf("%s\n",inp->val.c);
    if (inp->enc == ENC_ISO_UTF8) {
      if (lengp)
        *lengp = strlen_utf8(inp->val.uc);
      return inp->val.uc;
    } else if (inp->enc == ENC_ISO_LATIN1) {
      return latin2utf8(inp, lengp);
    } else if (inp->enc == ENC_ISO_ASCII) {
      if (lengp)
        *lengp = strlen(inp->val.c);
      return inp->val.uc;
    }
  }
  if (inp->type & YAP_STRING_WCHARS) {
    // printf("%S\n",inp->val.w);
    return wchar2utf8(inp, lengp);
  }
  return NULL;
}

static Term write_strings(unsigned char *s0, seq_tv_t *out,
                          size_t leng USES_REGS) {
  size_t min = 0, max = leng;

  if (out->type & (YAP_STRING_NCHARS | YAP_STRING_TRUNC)) {
    if (out->type & YAP_STRING_NCHARS)
      min = out->max;
    if (out->type & YAP_STRING_TRUNC && out->max < max)
      max = out->max;
  }

  unsigned char *s = s0, *lim = s + (max = strlen_utf8(s));
  Term t = init_tstring(PASS_REGS1);
  unsigned char *cp = s, *buf;

  LOCAL_TERM_ERROR(t, 2 * (lim - s));
  buf = buf_from_tstring(HR);
  while (*cp && cp < lim) {
    utf8proc_int32_t chr;
    int off;
    off = get_utf8(cp, -1, &chr);
    if (off > 0)
      cp += off;
    else {
      // Yap_Error(TYPE_ERROR_TEXT, t, NULL);
      cp++;
    }
    off = put_utf8(buf, chr);
    if (off > 0)
      buf += off;
  }
  if (max >= min)
    *buf++ = '\0';
  else
    while (max < min) {
      max++;
      buf += put_utf8(buf, '\0');
    }

  close_tstring(buf PASS_REGS);
  out->val.t = t;

  return out->val.t;
}

static Term write_atoms(void *s0, seq_tv_t *out, size_t leng USES_REGS) {
  Term t = AbsPair(HR);
  size_t sz = 0;
  size_t max = leng;
  if (leng == 0) {
    out->val.t = t;
    return TermNil;
  }
  if (out->type & (YAP_STRING_NCHARS | YAP_STRING_TRUNC)) {
    if (out->type & YAP_STRING_TRUNC && out->max < max)
      max = out->max;
  }

  unsigned char *s = s0, *lim = s + strnlen((char *)s, max);
  unsigned char *cp = s;
  wchar_t w[2];
  w[1] = '\0';
  LOCAL_TERM_ERROR(t, 2 * (lim - s));
  while (cp < lim && *cp) {
    utf8proc_int32_t chr;
    CELL *cl;
    cp += get_utf8(cp, -1, &chr);
    if (chr == '\0')
      break;
    w[0] = chr;
    cl = HR;
    HR += 2;
    cl[0] = MkAtomTerm(Yap_LookupMaybeWideAtom(w));
    cl[1] = AbsPair(HR);
    sz++;
    if (sz == max)
      break;
  }
  if (out->type & YAP_STRING_DIFF) {
    if (sz == 0)
      t = out->dif;
    else
      HR[-1] = Globalize(out->dif PASS_REGS);
  } else {
    if (sz == 0)
      t = TermNil;
    else
      HR[-1] = TermNil;
  }
  out->val.t = t;
  return (t);
}

static Term write_codes(void *s0, seq_tv_t *out, size_t leng USES_REGS) {
  Term t = AbsPair(HR);
  size_t sz = 0;
  size_t max = leng;
  if (leng == 0) {
    out->val.t = t;
    return TermNil;
  }
  if (out->type & (YAP_STRING_NCHARS | YAP_STRING_TRUNC)) {
    if (out->type & YAP_STRING_TRUNC && out->max < max)
      max = out->max;
  }

  unsigned char *s = s0, *lim = s + strlen((char *)s);
  unsigned char *cp = s;
  wchar_t w[2];
  w[1] = '\0';
  LOCAL_TERM_ERROR(t, 2 * (lim - s));
  while (*cp) {
    utf8proc_int32_t chr;
    CELL *cl;
    cp += get_utf8(cp, -1, &chr);
    if (chr == '\0')
      break;
    cl = HR;
    HR += 2;
    cl[0] = MkIntegerTerm(chr);
    cl[1] = AbsPair(HR);
    sz++;
    if (sz == max)
      break;
  }
  if (out->type & YAP_STRING_DIFF) {
    if (sz == 0)
      t = out->dif;
    else
      HR[-1] = Globalize(out->dif PASS_REGS);
  } else {
    if (sz == 0)
      t = TermNil;
    else
      HR[-1] = TermNil;
  }
  out->val.t = t;
  return (t);
}

static Atom write_atom(void *s0, seq_tv_t *out, size_t leng USES_REGS) {
  {
    unsigned char *s = s0;
    utf8proc_int32_t chr;
    while (*s && get_utf8(s, -1, &chr) == 1)
      s++;
    if (*s == '\0')
      return out->val.a = Yap_LookupAtom((char *)s0);
    s = s0;
    size_t l = strlen(s0);
    wchar_t *wbuf = Malloc(sizeof(wchar_t) * ((l + 1))), *wptr = wbuf;
    Atom at;
    if (!wbuf)
      return NULL;
    while (*s) {
      utf8proc_int32_t chr;
      int off = get_utf8(s, -1, &chr);
      if (off < 0) {
        s++;
        continue;
      }
      s++;
      *wptr++ = chr;
    }
    *wptr++ = '\0';

    at = Yap_LookupMaybeWideAtom(wbuf);
    out->val.a = at;
    return at;
  }
}

size_t write_buffer(unsigned char *s0, seq_tv_t *out, size_t leng USES_REGS) {
  size_t min = 0, max = leng, room_end;
  if (out->enc == ENC_ISO_UTF8) {
    room_end = strlen((char *)s0) + 1;
    if (out->val.uc == NULL) {
      out->val.uc = malloc(room_end < 16 ? 16 : room_end);
    }
    if (out->val.uc != s0) {
      strcpy(out->val.c, (char *)s0);
    }
  } else if (out->enc == ENC_ISO_LATIN1) {
    room_end = strlen((char *)s0) + 1;
    unsigned char *s = s0;
    unsigned char *cp = s;
    unsigned char *buf = out->val.uc;
    if (!buf)
      return -1;
    while (*cp) {
      utf8proc_int32_t chr;
      int off = get_utf8(cp, -1, &chr);
      if (off <= 0 || chr > 255)
        return -1;
      if (off == max)
        break;
      cp += off;
      *buf++ = chr;
    }
    if (max >= min)
      *buf++ = '\0';
    else
      while (max < min) {
        utf8proc_int32_t chr;
        max++;
        cp += get_utf8(cp, -1, &chr);
        *buf++ = chr;
      }
    room_end = buf - out->val.uc;
  } else if (out->enc == ENC_WCHAR) {
    unsigned char *s = s0, *lim = s + (max = strnlen((char *)s0, max));
    unsigned char *cp = s;
    wchar_t *buf0, *buf;

    buf = buf0 = out->val.w;
    if (!buf)
      return -1;
    while (*cp && cp < lim) {
      utf8proc_int32_t chr;
      cp += get_utf8(cp, -1, &chr);
      *buf++ = chr;
    }
    if (max >= min)
      *buf++ = '\0';
    else
      while (max < min) {
        utf8proc_int32_t chr;
        max++;
        cp += get_utf8(cp, -1, &chr);
        *buf++ = chr;
      }
    *buf = '\0';
    room_end = (buf - buf0) + 1;
  } else {
    // no other encodings are supported.
    room_end = -1;
  }
  return room_end;
}

static size_t write_length(const unsigned char *s0, seq_tv_t *out,
                           size_t leng USES_REGS) {
  return leng;
}

static Term write_number(unsigned char *s, seq_tv_t *out, int size USES_REGS) {
  Term t;
  int i = mark_stack();
  t = Yap_StringToNumberTerm((char *)s, &out->enc);
  restore_stack(i);
  return t;
}

static Term string_to_term(void *s, seq_tv_t *out, size_t leng USES_REGS) {
  Term o;
  int i = mark_stack();
  o = out->val.t =
      Yap_StringToTerm(s, strlen(s) + 1, &out->enc, GLOBAL_MaxPriority, NULL);
  restore_stack(i);
  return o;
}

bool write_Text(unsigned char *inp, seq_tv_t *out, size_t leng USES_REGS) {
  /* we know what the term is */
  if (out->type & YAP_STRING_TERM) {
    if ((out->val.t = string_to_term(inp, out, leng PASS_REGS)) != 0L)
      return out->val.t != 0;
  }
  if (out->type & (YAP_STRING_INT | YAP_STRING_FLOAT | YAP_STRING_BIG)) {
    if ((out->val.t = write_number(inp, out, leng PASS_REGS)) != 0L) {
      // Yap_DebugPlWriteln(out->val.t);

      return true;
    }

    if (!(out->type & YAP_STRING_ATOM))
      return false;
  }
  if (out->type & (YAP_STRING_ATOM)) {
    if (write_atom(inp, out, leng PASS_REGS) != NIL) {
      Atom at = out->val.a;
      if (at && (out->type & YAP_STRING_OUTPUT_TERM))
        out->val.t = MkAtomTerm(at);
      // Yap_DebugPlWriteln(out->val.t);
      return at != NIL;
    }
  }

  switch (out->type & YAP_TYPE_MASK) {
  case YAP_STRING_CHARS: {
    size_t room = write_buffer(inp, out, leng PASS_REGS);
    // printf("%s\n", out->val.c);
    return ((Int)room > 0);
  }
  case YAP_STRING_WCHARS: {
    size_t room = write_buffer(inp, out, leng PASS_REGS);
    // printf("%S\n", out->val.w);
    return ((Int)room > 0);
  }
  case YAP_STRING_STRING:
    out->val.t = write_strings(inp, out, leng PASS_REGS);
    // Yap_DebugPlWriteln(out->val.t);
    return out->val.t != 0;
  case YAP_STRING_ATOMS:
    out->val.t = write_atoms(inp, out, leng PASS_REGS);
    // Yap_DebugPlWriteln(out->val.t);
    return out->val.t != 0;
  case YAP_STRING_CODES:
    out->val.t = write_codes(inp, out, leng PASS_REGS);
    // Yap_DebugPlWriteln(out->val.t);
    return out->val.t != 0;
  case YAP_STRING_LENGTH:
    out->val.l = write_length(inp, out, leng PASS_REGS);
    // printf("s\n",out->val.l);
    return out->val.l != (size_t)(-1);
  case YAP_STRING_ATOM:
    out->val.a = write_atom(inp, out, leng PASS_REGS);
    // Yap_DebugPlWriteln(out->val.t);
    return out->val.a != NULL;
  case YAP_STRING_INT | YAP_STRING_FLOAT | YAP_STRING_BIG:
    out->val.t = write_number(inp, out, leng PASS_REGS);
    // Yap_DebugPlWriteln(out->val.t);
    return out->val.t != 0;
  default: {}
  }
  return false;
}

static size_t upcase(void *s0, seq_tv_t *out USES_REGS) {

  unsigned char *s = s0;
  while (*s) {
    // assumes the two code have always the same size;
    utf8proc_int32_t chr;
    get_utf8(s, -1, &chr);
    chr = utf8proc_toupper(chr);
    s += put_utf8(s, chr);
  }
  return true;
}

static size_t downcase(void *s0, seq_tv_t *out USES_REGS) {

  unsigned char *s = s0;
  while (*s) {
    // assumes the two code have always the same size;
    utf8proc_int32_t chr;
    get_utf8(s, -1, &chr);
    chr = utf8proc_tolower(chr);
    s += put_utf8(s, chr);
  }
  return true;
}

bool Yap_CVT_Text(seq_tv_t *inp, seq_tv_t *out USES_REGS) {
  unsigned char *buf;
  bool rc;

  size_t leng;
  int l = init_alloc(__LINE__);
  /*
  f//printf(stderr, "[ %d ", n++)    ;
  if (inp->type & (YAP_STRING_TERM|YAP_STRING_ATOM|YAP_STRING_ATOMS_CODES
                   |YAP_STRING_STRING))
      //Yap_DebugPlWriteln(inp->val.t);
  else if (inp->type & YAP_STRING_WCHARS) fprintf(stderr,"S %S\n", inp->val
              .w);
  else  fprintf(stderr,"s %s\n", inp->val.c);
*/
  buf = Yap_readText(inp, &leng PASS_REGS);
  if (out->type & (YAP_STRING_NCHARS | YAP_STRING_TRUNC)) {
    if (out->max < leng) {
      const unsigned char *ptr = skip_utf8(buf, leng);
      size_t diff = (ptr - buf);
      char *nbuf = Malloc(diff + 1);
      memcpy(nbuf, buf, diff);
      nbuf[diff] = '\0';
      leng = out->max;
    }
    // else if (out->type & YAP_STRING_NCHARS &&
    // const unsigned char *ptr = skip_utf8(buf, leng)
  }

  if (!buf) {
    unprotect_stack(0);
    return 0L;
  }
  if (out->type & (YAP_STRING_UPCASE | YAP_STRING_DOWNCASE)) {
    if (out->type & YAP_STRING_UPCASE) {
      if (!upcase(buf, out)) {
        unprotect_stack(0);
        return false;
      }
    }
    if (out->type & YAP_STRING_DOWNCASE) {
      if (!downcase(buf, out)) {
        unprotect_stack(0);
        return false;
      }
    }
  }

  rc = write_Text(buf, out, leng PASS_REGS);
  unprotect_stack(l);
  /*    fprintf(stderr, " -> ");
      if (!rc) fprintf(stderr, "NULL");
      else if (out->type &
               (YAP_STRING_TERM|YAP_STRING_ATOMS_CODES
                |YAP_STRING_STRING)) //Yap_DebugPlWrite(out->val.t);
      else if (out->type &
               YAP_STRING_ATOM) //Yap_DebugPlWriteln(MkAtomTerm(out->val.a));
      else if (out->type & YAP_STRING_WCHARS) fprintf(stderr, "%S",
                                                      out->val.w);
     else
           fprintf(stderr, "%s", out->val.c);
  fprintf(stderr, "\n]\n"); */
  return rc;
}

static int cmp_Text(const unsigned char *s1, const unsigned char *s2, int l) {
  const unsigned char *w1 = s1;
  utf8proc_int32_t chr1, chr2;
  const unsigned char *w2 = s2;
  int i;
  for (i = 0; i < l; i++) {
    w2 += get_utf8(w2, -1, &chr2);
    w1 += get_utf8(w1, -1, &chr1);
    if (chr1 - chr2)
      return chr1 - chr2;
  }
  return 0;
}

static unsigned char *concat(int n, unsigned char *sv[] USES_REGS) {
  char *buf;
  unsigned char *buf0;
  size_t room = 0;
  int i;

  for (i = 0; i < n; i++) {
    room += strlen((char *)sv[i]);
  }
  buf = Malloc(room + 1);
  buf0 = (unsigned char *)buf;
  for (i = 0; i < n; i++) {
    char *s = (char *)sv[i];
    buf = strcpy(buf, s);
    buf += strlen(s);
  }
  return buf0;
}

static void *slice(size_t min, size_t max, unsigned char *buf USES_REGS) {
  unsigned char *nbuf = Malloc((max - min) * 4 + 1);
  const unsigned char *ptr = skip_utf8(buf, min);
  unsigned char *nptr = nbuf;
  utf8proc_int32_t chr;

  while (min++ < max) {
    ptr += get_utf8(ptr, -1, &chr);
    nptr += put_utf8(nptr, chr);
  }
  nptr[0] = '\0';
  return nbuf;
}

//
// Out must be an atom or a string
bool Yap_Concat_Text(int tot, seq_tv_t inp[], seq_tv_t *out USES_REGS) {
  unsigned char **bufv;
  unsigned char *buf;
  size_t leng;
  int i;
  int l =  init_alloc(__LINE__);
  bufv = Malloc(tot * sizeof(unsigned char *));
  if (!bufv) {
    unprotect_stack(0);
    return NULL;
  }
  for (i = 0; i < tot; i++) {
    inp[i].type |= YAP_STRING_IN_TMP;
    unsigned char *nbuf = Yap_readText(inp + i, &leng PASS_REGS);

    if (!nbuf) {
      unprotect_stack(0);
      return NULL;
    }
    bufv[i] = nbuf;
  }
  buf = concat(tot, bufv PASS_REGS);
  bool rc = write_Text(buf, out, leng PASS_REGS);
  unprotect_stack(l);
  return rc;
}

//
bool Yap_Splice_Text(int n, size_t cuts[], seq_tv_t *inp,
                     seq_tv_t outv[] USES_REGS) {
  unsigned char *buf;
  int l =  init_alloc(__LINE__);
  inp->type |= YAP_STRING_IN_TMP;
  buf = Yap_readText(inp, &l PASS_REGS);
  if (!buf) {
    unprotect_stack(0);

    return false;
  }
  if (!cuts) {
    if (n == 2) {
      size_t l0, l1;
      unsigned char *buf0, *buf1;

      if (outv[0].val.t) {
        buf0 = Yap_readText(outv, &l0 PASS_REGS);
        if (!buf0) {
          unprotect_stack(0);
          return false;
        }
        if (cmp_Text(buf, buf0, l0) != 0) {
          unprotect_stack(0);
          return false;
        }
        l1 = l - l0;

        buf1 = slice(l0, l, buf PASS_REGS);
        bool rc = write_Text(buf1, outv + 1, l1 PASS_REGS);
        if (!rc) {
          unprotect_stack(0);
          return false;
        }
        unprotect_stack(l);
        return rc;
      } else /* if (outv[1].val.t) */ {
        buf1 = Yap_readText(outv + 1, &l1 PASS_REGS);
        if (!buf1) {
          unprotect_stack(0);
          return false;
        }
        l0 = l - l1;
        if (cmp_Text(skip_utf8((const unsigned char *)buf, l0), buf1, l1) !=
            0) {
          unprotect_stack(0);
          return false;
        }
        buf0 = slice(0, l0, buf PASS_REGS);
        bool rc = write_Text(buf0, outv, l0 PASS_REGS);
        unprotect_stack((rc ? 0 : l + 0));
        return rc;
      }
    }
  }
  int i, next;
  for (i = 0; i < n; i++) {
    if (i == 0)
      next = 0;
    else
      next = cuts[i - 1];
    void *bufi = slice(next, cuts[i], buf PASS_REGS);
    if (!write_Text(bufi, outv + i, cuts[i] - next PASS_REGS)) {
      unprotect_stack(0);
      return false;
    }
  }
  unprotect_stack(l);

  return true;
}

/**
 * Function to convert a generic text term (string, atom, list of codes, list
of
atoms)  into a buff
er.
 *
 * @param t     the term
 * @param buf   the buffer, if NULL a buffer is malloced, and the user should
reclai it
 * @param len   buffer size
 * @param enc   encoding (UTF-8 is strongly recommended)
 *
 * @return the buffer, or NULL in case of failure. If so, Yap_Error may be
called.
 */
const char *Yap_TextTermToText(Term t, char *buf, size_t len, encoding_t enc) {
  CACHE_REGS
  seq_tv_t inp, out;
  inp.val.t = t;
  if (IsAtomTerm(t) && t != TermNil) {
    inp.type = YAP_STRING_ATOM;
    if (IsWideAtom(AtomOfTerm(t)))
      inp.enc = ENC_WCHAR;
    else
      inp.enc = ENC_ISO_LATIN1;
  } else if (IsStringTerm(t)) {
    inp.type = YAP_STRING_STRING;
    inp.enc = ENC_ISO_UTF8;
  } else if (IsPairOrNilTerm(t)) {
    inp.type = (YAP_STRING_CODES | YAP_STRING_ATOMS);
  } else {
    Yap_Error(TYPE_ERROR_TEXT, t, NULL);
    return false;
  }
  out.enc = enc;
  out.type = YAP_STRING_CHARS;
  out.val.c = buf;
  if (!Yap_CVT_Text(&inp, &out PASS_REGS))
    return NULL;
  return out.val.c;
}

/**
 * Convert from a predicate structure to an UTF-8 string of the form
 *
 * module:name/arity.
 *
 * The result is in very volatile memory.
 *
 * @param s        the buffer
 *
 * @return the temporary string
 */
const char *Yap_PredIndicatorToUTF8String(PredEntry *ap) {
  CACHE_REGS
  Atom at;
  arity_t arity;
  Functor f;
  char *s, *smax, *s0;
  s = s0 = malloc(1024);
  smax = s + 1024;
  Term tmod = ap->ModuleOfPred;
  if (tmod) {
    Yap_AtomToUTF8Text(AtomOfTerm(tmod), s);
    s += strlen(s);
    if (smax - s > 1) {
      strcat(s, ":");
    } else {
      return NULL;
    }
    s++;
  } else {
    if (smax - s > strlen("prolog:")) {
      s = strcpy(s, "prolog:");
    } else {
      return NULL;
    }
  }
  // follows the actual functor
  if (ap->ModuleOfPred == IDB_MODULE) {
    if (ap->PredFlags & NumberDBPredFlag) {
      Int key = ap->src.IndxId;
      snprintf(s, smax - s, "%" PRIdPTR, key);
      return LOCAL_FileNameBuf;
    } else if (ap->PredFlags & AtomDBPredFlag) {
      at = (Atom)(ap->FunctorOfPred);
      if (!Yap_AtomToUTF8Text(at, s))
        return NULL;
    } else {
      f = ap->FunctorOfPred;
      at = NameOfFunctor(f);
      arity = ArityOfFunctor(f);
    }
  } else {
    arity = ap->ArityOfPE;
    if (arity) {
      at = NameOfFunctor(ap->FunctorOfPred);
    } else {
      at = (Atom)(ap->FunctorOfPred);
    }
  }
  if (!Yap_AtomToUTF8Text(at, s)) {
    return NULL;
  }
  s += strlen(s);
  snprintf(s, smax - s, "/%" PRIdPTR, arity);
  return s0;
}

/**
 * Convert from a text buffer (8-bit) to a term that has the same type as
 * _Tguide_
 *
 ≈* @param s        the buffer
≈ * @param tguide   the guide
 *
≈  * @return the term
 */
Term Yap_MkTextTerm(const char *s, encoding_t enc, Term tguide) {
  CACHE_REGS
  if (IsAtomTerm(tguide))
    return MkAtomTerm(Yap_LookupAtom(s));
  if (IsStringTerm(tguide))
    return MkStringTerm(s);
  if (IsPairTerm(tguide) && IsAtomTerm(HeadOfTerm(tguide))) {
    return Yap_CharsToListOfAtoms(s, enc PASS_REGS);
  }
  return Yap_CharsToListOfCodes(s, enc PASS_REGS);
}

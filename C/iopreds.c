/*************************************************************************
*									 *
*	 YAP Prolog 							 *
*									 *
*	Yap Prolog was developed at NCCUP - Universidade do Porto	 *
*									 *
* Copyright L.Damas, V.S.Costa and Universidade do Porto 1985-1997	 *
*									 *
**************************************************************************
*									 *
* File:		iopreds.c						 *
* Last rev:	5/2/88							 *
* mods:									 *
* comments:	Input/Output C implemented predicates			 *
*									 *
*************************************************************************/
#ifdef SCCS
static char SccsId[] = "%W% %G%";
#endif

/*
 * This file includes the definition of a miscellania of standard predicates
 * for yap refering to: Files and Streams, Simple Input/Output, 
 *
 */

#include "Yap.h"
#include "Yatom.h"
#include "YapHeap.h"
#include "yapio.h"
#include "eval.h"
#include <stdlib.h>
#if HAVE_STDARG_H
#include <stdarg.h>
#endif
#if HAVE_CTYPE_H
#include <ctype.h>
#endif
#if HAVE_WCTYPE_H
#include <wctype.h>
#endif
#if HAVE_SYS_TIME_H
#include <sys/time.h>
#endif
#if HAVE_SYS_TYPES_H
#include <sys/types.h>
#endif
#ifdef HAVE_SYS_STAT_H
#include <sys/stat.h>
#endif
#if HAVE_SYS_SELECT_H && !_MSC_VER && !defined(__MINGW32__) 
#include <sys/select.h>
#endif
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#if HAVE_STRING_H
#include <string.h>
#endif
#if HAVE_SIGNAL_H
#include <signal.h>
#endif
#if HAVE_FCNTL_H
/* for O_BINARY and O_TEXT in WIN32 */
#include <fcntl.h>
#endif
#ifdef _WIN32
#if HAVE_IO_H
/* Windows */
#include <io.h>
#endif
#endif
#if !HAVE_STRNCAT
#define strncat(X,Y,Z) strcat(X,Y)
#endif
#if !HAVE_STRNCPY
#define strncpy(X,Y,Z) strcpy(X,Y)
#endif
#if _MSC_VER || defined(__MINGW32__) 
#include <windows.h>
#ifndef S_ISDIR
#define S_ISDIR(x) (((x)&_S_IFDIR)==_S_IFDIR)
#endif
#endif
#include "iopreds.h"

STATIC_PROTO (Int p_set_read_error_handler, (void));
STATIC_PROTO (Int p_get_read_error_handler, (void));
STATIC_PROTO (Int p_read, (void));
STATIC_PROTO (Int p_startline, (void));
STATIC_PROTO (Int p_change_type_of_char, (void));
STATIC_PROTO (Int p_type_of_char, (void));
STATIC_PROTO (Term StreamPosition, (IOSTREAM *));

extern Atom Yap_FileName(IOSTREAM *s);

static Term
StreamName(IOSTREAM *s)
{
  return MkAtomTerm(Yap_FileName(s));
}


void
Yap_InitStdStreams (void)
{
}

void
Yap_InitPlIO (void)
{
}

/*
 * Used by the prompts to check if they are after a newline, and then a
 * prompt should be output, or if we are in the middle of a line.
 */
static int newline = TRUE;

#ifdef DEBUG

static       int   eolflg = 1;



static char     my_line[200] = {0};
static char    *lp = my_line;

static YP_File     curfile;

#ifdef MACC

static void 
InTTYLine(char *line)
{
	char           *p = line;
	char            ch;
	while ((ch = InKey()) != '\n' && ch != '\r')
		if (ch == 8) {
			if (line < p)
				BackupTTY(*--p);
		} else
			TTYChar(*p++ = ch);
	TTYChar('\n');
	*p = 0;
}

#endif

void 
Yap_DebugSetIFile(char *fname)
{
  if (curfile)
    YP_fclose(curfile);
  curfile = YP_fopen(fname, "r");
  if (curfile == NULL) {
    curfile = stdin;
    fprintf(stderr,"%% YAP Warning: can not open %s for input\n", fname);
  }
}

void 
Yap_DebugEndline()
{
	*lp = 0;

}

int 
Yap_DebugGetc()
{
  int             ch;
  if (eolflg) {
    if (curfile != NULL) {
      if (YP_fgets(my_line, 200, curfile) == 0)
	curfile = NULL;
    }
    if (curfile == NULL)
      if (YP_fgets(my_line, 200, stdin) == NULL) {
	return EOF;
      }
    eolflg = 0;
    lp = my_line;
  }
  if ((ch = *lp++) == 0)
    ch = '\n', eolflg = 1;
  if (Yap_Option['l' - 96])
    putc(ch, Yap_logfile);
  return (ch);
}

int 
Yap_DebugPutc(int sno, wchar_t ch)
{
  if (Yap_Option['l' - 96])
    (void) putc(ch, Yap_logfile);
  return (putc(ch, Yap_stderr));
}

void
Yap_DebugPlWrite(Term t)
{
  Yap_plwrite(t, Yap_DebugPutc, 0, 1200);
}

void 
Yap_DebugErrorPutc(int c)
{
   Yap_DebugPutc (Yap_c_error_stream, c);
}

#endif




static Int
p_has_readline(void)
{
#if HAVE_LIBREADLINE && HAVE_READLINE_READLINE_H
  return TRUE;
#else
  return FALSE;
#endif
}


int
Yap_GetCharForSIGINT(void)
{
  int ch;
  /* ask for a new line */
  fprintf(stderr, "Action (h for help): ");
  ch = getc(stdin);
  /* first process up to end of line */
  while ((fgetc(stdin)) != '\n');
  newline = TRUE;
  return ch;
}



typedef struct stream_ref
{ struct io_stream *read;
  struct io_stream *write;
} stream_ref;

#ifdef BEAM
int beam_write (void)
{
  Yap_StartSlots();
  Yap_plwrite (ARG1, Stream[Yap_c_output_stream].stream_wputc, 0, 1200);
  Yap_CloseSlots();
  if (EX != 0L) {
    Term ball = Yap_PopTermFromDB(EX);
    EX = 0L;
    Yap_JumpToEnv(ball);
    return(FALSE);
  }
  return (TRUE);
}
#endif

static void
clean_vars(VarEntry *p)
{
  if (p == NULL) return;
  p->VarAdr = TermNil;
  clean_vars(p->VarLeft);
  clean_vars(p->VarRight);
}

static Term
syntax_error (TokEntry * tokptr, IOSTREAM *st, Term *outp)
{
  Term info;
  int count = 0, out = 0;
  Int start, err = 0, end;
  Term tf[7];
  Term *error = tf+3;
  CELL *Hi = H;

  /* make sure to globalise variable */
  Yap_unify(*outp, MkVarTerm());
  start = tokptr->TokPos;
  clean_vars(Yap_VarTable);
  clean_vars(Yap_AnonVarTable);
  while (1) {
    Term ts[2];

    if (H > ASP-1024) {
      tf[3] = TermNil;
      err = 0;
      end = 0;
      /* for some reason moving this earlier confuses gcc on solaris */
      H = Hi;
      break;
    }
    if (tokptr == Yap_toktide) {
      err = tokptr->TokPos;
      out = count;
    }
    info = tokptr->TokInfo;
    switch (tokptr->Tok) {
    case Name_tok:
      {
	Term t0[1];
	t0[0] = MkAtomTerm((Atom)info);
	ts[0] = Yap_MkApplTerm(Yap_MkFunctor(AtomAtom,1),1,t0);
      }
      break;
    case Number_tok:
      ts[0] = Yap_MkApplTerm(Yap_MkFunctor(AtomNumber,1),1,&(tokptr->TokInfo));
      break;
    case Var_tok:
      {
	Term t[3];
	VarEntry *varinfo = (VarEntry *)info;

	t[0] = MkIntTerm(0);
	t[1] = Yap_StringToList(varinfo->VarRep);
	if (varinfo->VarAdr == TermNil) {
	  t[2] = varinfo->VarAdr = MkVarTerm();
	} else {
	  t[2] = varinfo->VarAdr;
	}
	ts[0] = Yap_MkApplTerm(Yap_MkFunctor(AtomGVar,3),3,t);
      }
      break;
    case String_tok:
      {
	Term t0 = Yap_StringToList((char *)info);
	ts[0] = Yap_MkApplTerm(Yap_MkFunctor(AtomString,1),1,&t0);
      }
      break;
    case WString_tok:
      {
	Term t0 = Yap_WideStringToList((wchar_t *)info);
	ts[0] = Yap_MkApplTerm(Yap_MkFunctor(AtomString,1),1,&t0);
      }
      break;
    case Error_tok:
    case eot_tok:
      break;
    case Ponctuation_tok:
      {
	char s[2];
	s[1] = '\0';
	if (Ord (info) == 'l') {
	  s[0] = '(';
	} else  {
	  s[0] = (char)info;
	}
	ts[0] = MkAtomTerm(Yap_LookupAtom(s));
      }
    }
    if (tokptr->Tok == Ord (eot_tok)) {
      *error = TermNil;
      end = tokptr->TokPos;
      break;
    } else if (tokptr->Tok != Ord (Error_tok)) {
      ts[1] = MkIntegerTerm(tokptr->TokPos);
      *error =
	MkPairTerm(Yap_MkApplTerm(FunctorMinus,2,ts),TermNil);
      error = RepPair(*error)+1;
      count++;
    }
    tokptr = tokptr->TokNext;
  }
  if (IsVarTerm(*outp) && (VarOfTerm(*outp) > H || VarOfTerm(*outp) < H0)) {
    tf[0] = Yap_MkNewApplTerm(Yap_MkFunctor(AtomRead,1),1);
  } else {
    tf[0] = Yap_MkApplTerm(Yap_MkFunctor(AtomRead,1),1,outp);
  }
  {
    Term t[3];

    t[0] = MkIntegerTerm(start);
    t[1] = MkIntegerTerm(err);
    t[2] = MkIntegerTerm(end);
    tf[1] = Yap_MkApplTerm(Yap_MkFunctor(AtomBetween,3),3,t);
  }
  tf[2] = MkAtomTerm(AtomHERE);
  tf[4] = MkIntegerTerm(out);
  tf[5] = MkIntegerTerm(err);
  tf[6] = StreamName(st);
  return(Yap_MkApplTerm(FunctorSyntaxError,7,tf));
}

static void
GenerateSyntaxError(Term *tp, TokEntry *tokstart, IOSTREAM *sno)
{
  if (tp) {
    Term et[2];
    Term t = MkVarTerm();
    et[0] = syntax_error(tokstart, sno, &t);
    et[1] = MkAtomTerm(Yap_LookupAtom("Syntax error"));
    *tp = Yap_MkApplTerm(FunctorError, 2, et);
  }
}

Term
Yap_StringToTerm(char *s,Term *tp)
{
  IOSTREAM *sno = Sopenmem(&s, NULL, "r");
  Term t;
  TokEntry *tokstart;
  tr_fr_ptr TR_before_parse;
  Term tpos = TermNil;

  if (sno == NULL)
    return FALSE;
  TR_before_parse = TR;
  tokstart = Yap_tokptr = Yap_toktide = Yap_tokenizer(sno, &tpos);
  if (tokstart == NIL || tokstart->Tok == Ord (eot_tok)) {
    if (tp) {
      *tp = MkAtomTerm(AtomEOFBeforeEOT);
    }
    Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
    Sclose(sno);
    return FALSE;
  } else if (Yap_ErrorMessage) {
    if (tp) {
      *tp = MkAtomTerm(Yap_LookupAtom(Yap_ErrorMessage));
    }
    Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
    Sclose(sno);
    return FALSE;
  }
  t = Yap_Parse();
  TR = TR_before_parse;
  if (!t || Yap_ErrorMessage) {
    GenerateSyntaxError(tp, tokstart, sno);
    Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
    Sclose(sno);
    return FALSE;
  }
  Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
  Sclose(sno);
  return t;
}


Int
Yap_FirstLineInParse (void)
{
  return StartLine;
}

static Int
p_startline (void)
{
  return (Yap_unify_constant (ARG1, MkIntegerTerm (StartLine)));
}

/* control the parser error handler */
static Int
p_set_read_error_handler(void)
{
  Term t = Deref(ARG1);
  char *s;
  if (IsVarTerm(t)) {
    Yap_Error(INSTANTIATION_ERROR,t,"set_read_error_handler");
    return(FALSE);
  }
  if (!IsAtomTerm(t)) {
    Yap_Error(TYPE_ERROR_ATOM,t,"bad syntax_error handler");
    return(FALSE);
  }
  s = RepAtom(AtomOfTerm(t))->StrOfAE;
  if (!strcmp(s, "fail")) {
    ParserErrorStyle = FAIL_ON_PARSER_ERROR;
  } else if (!strcmp(s, "error")) {
    ParserErrorStyle = EXCEPTION_ON_PARSER_ERROR;
  } else if (!strcmp(s, "quiet")) {
    ParserErrorStyle = QUIET_ON_PARSER_ERROR;
  } else if (!strcmp(s, "dec10")) {
    ParserErrorStyle = CONTINUE_ON_PARSER_ERROR;
  } else {
    Yap_Error(DOMAIN_ERROR_SYNTAX_ERROR_HANDLER,t,"bad syntax_error handler");
    return(FALSE);
  }
  return(TRUE);
}

/* return the status for the parser error handler */
static Int
p_get_read_error_handler(void)
{
  Term t;

  switch (ParserErrorStyle) {
  case FAIL_ON_PARSER_ERROR:
    t = MkAtomTerm(AtomFail);
    break;
  case EXCEPTION_ON_PARSER_ERROR:
    t = MkAtomTerm(AtomError);
    break;
  case QUIET_ON_PARSER_ERROR:
    t = MkAtomTerm(AtomQuiet);
    break;
  case CONTINUE_ON_PARSER_ERROR:
    t = MkAtomTerm(AtomDec10);
    break;
  default:
    Yap_Error(SYSTEM_ERROR,TermNil,"corrupted syntax_error handler");
    return(FALSE);
  }
  return (Yap_unify_constant (ARG1, t));
}

int
Yap_readTerm(void *st0, Term *tp, Term *varnames, Term *terror, Term *tpos)
{
  TokEntry *tokstart;
  Term pt;
  IOSTREAM *st = (IOSTREAM *)st0;

  if (st == NULL) {
    return FALSE;
  }
  tokstart = Yap_tokptr = Yap_toktide = Yap_tokenizer(st, tpos);
  if (Yap_ErrorMessage)
    {
      Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
      if (terror)
	*terror = MkAtomTerm(Yap_LookupAtom(Yap_ErrorMessage));
      Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
      return FALSE;
    }
  pt = Yap_Parse();
  if (Yap_ErrorMessage || pt == (CELL)0) {
    GenerateSyntaxError(terror, tokstart, st);
    Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
    return FALSE;
  }
  if (varnames) {
    *varnames = Yap_VarNames(Yap_VarTable, TermNil);
    if (!*varnames) {
      Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
      return FALSE;
    }
  }
  *tp = pt;
  if (!pt)
    return FALSE;
  return TRUE;
}

/*
  Assumes
  Flag: ARG1
  Term: ARG2
  Module: ARG3
  Vars: ARG4
  Pos: ARG5
  Err: ARG6
 */
static Int
  do_read(IOSTREAM *inp_stream, int nargs)
{
  Term t, v;
  TokEntry *tokstart;
#if EMACS
  int emacs_cares = FALSE;
#endif
  Term tmod = Deref(ARG3), OCurrentModule = CurrentModule, tpos;

  if (IsVarTerm(tmod)) {
    tmod = CurrentModule;
  } else if (!IsAtomTerm(tmod)) {
    Yap_Error(TYPE_ERROR_ATOM, tmod, "read_term/2");
    return FALSE;
  }
  if (!(inp_stream->flags & SIO_TEXT)) {
    Yap_Error(PERMISSION_ERROR_INPUT_BINARY_STREAM, StreamName(inp_stream), "read_term/2");
    return FALSE;
  }
  Yap_Error_TYPE = YAP_NO_ERROR;
  tpos = StreamPosition(inp_stream);
  if (!Yap_unify(tpos,ARG5)) {
    /* do this early so that we do not have to protect it in case of stack expansion */  
    return FALSE;
  }
  while (TRUE) {
    CELL *old_H;
    int64_t cpos = 0;
    int seekable = inp_stream->functions->seek != NULL;

    /* two cases where we can seek: memory and console */
    if (seekable) {
      cpos = inp_stream->posbuf.byteno;
    }
    /* Scans the term using stack space */
    while (TRUE) {
      old_H = H;
      Yap_eot_before_eof = FALSE;
      tpos = StreamPosition(inp_stream);
      tokstart = Yap_tokptr = Yap_toktide = Yap_tokenizer(inp_stream, &tpos);
      if (Yap_Error_TYPE != YAP_NO_ERROR && seekable) {
	H = old_H;
	Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
	if (seekable) {
	  Sseek64(inp_stream, cpos, SIO_SEEK_SET);
	}
	if (Yap_Error_TYPE == OUT_OF_TRAIL_ERROR) {
	  Yap_Error_TYPE = YAP_NO_ERROR;
	  if (!Yap_growtrail (sizeof(CELL) * K16, FALSE)) {
	    return FALSE;
	  }
	} else if (Yap_Error_TYPE == OUT_OF_AUXSPACE_ERROR) {
	  Yap_Error_TYPE = YAP_NO_ERROR;
	  if (!Yap_ExpandPreAllocCodeSpace(0, NULL, TRUE)) {
	    return FALSE;
	  }
	} else if (Yap_Error_TYPE == OUT_OF_HEAP_ERROR) {
	  Yap_Error_TYPE = YAP_NO_ERROR;
	  if (!Yap_growheap(FALSE, 0, NULL)) {
	    return FALSE;
	  }
	} else if (Yap_Error_TYPE == OUT_OF_STACK_ERROR) {
	  Yap_Error_TYPE = YAP_NO_ERROR;
	  if (!Yap_gcl(Yap_Error_Size, nargs, ENV, CP)) {
	    return FALSE;
	  }
	}
      } else {
	/* done with this */
	break;
      }
    }
    Yap_Error_TYPE = YAP_NO_ERROR;
    /* preserve value of H after scanning: otherwise we may lose strings
       and floats */
    old_H = H;
    if (tokstart != NULL && tokstart->Tok == Ord (eot_tok)) {
      /* did we get the end of file from an abort? */
      if (Yap_ErrorMessage &&
	  !strcmp(Yap_ErrorMessage,"Abort")) {
	Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
	return FALSE;
      } else {
	Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
	
	return Yap_unify_constant(ARG2, MkAtomTerm (AtomEof))
	  && Yap_unify_constant(ARG4, TermNil);
      }
    }
  repeat_cycle:
    CurrentModule = tmod;
    if (Yap_ErrorMessage || (t = Yap_Parse()) == 0) {
      CurrentModule = OCurrentModule;
      if (Yap_ErrorMessage) {
	int res;

	if (!strcmp(Yap_ErrorMessage,"Stack Overflow") ||
	    !strcmp(Yap_ErrorMessage,"Trail Overflow") ||
	    !strcmp(Yap_ErrorMessage,"Heap Overflow")) {
	  /* ignore term we just built */
	  tr_fr_ptr old_TR = TR;


	  H = old_H;
	  TR = (tr_fr_ptr)ScannerStack;
	  
	  if (!strcmp(Yap_ErrorMessage,"Stack Overflow"))
	    res = Yap_growstack_in_parser(&old_TR, &tokstart, &Yap_VarTable);
	  else if (!strcmp(Yap_ErrorMessage,"Heap Overflow"))
	    res = Yap_growheap_in_parser(&old_TR, &tokstart, &Yap_VarTable);
	  else
	    res = Yap_growtrail_in_parser(&old_TR, &tokstart, &Yap_VarTable);
	  if (res) {
	    ScannerStack = (char *)TR;
	    TR = old_TR;
	    old_H = H;
	    Yap_tokptr = Yap_toktide = tokstart;
	    Yap_ErrorMessage = NULL;
	    goto repeat_cycle;
	  }
	  ScannerStack = (char *)TR;
	  TR = old_TR;
	}
      }
      if (ParserErrorStyle == QUIET_ON_PARSER_ERROR) {
	/* just fail */
	Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
	return FALSE;
      } else if (ParserErrorStyle == CONTINUE_ON_PARSER_ERROR) {
	Yap_ErrorMessage = NULL;
	/* try again */
	goto repeat_cycle;
      } else {
	Term terr = syntax_error(tokstart, inp_stream, &ARG2);
	if (Yap_ErrorMessage == NULL)
	  Yap_ErrorMessage = "SYNTAX ERROR";
	
	if (ParserErrorStyle == EXCEPTION_ON_PARSER_ERROR) {
	  Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
	  Yap_Error(SYNTAX_ERROR,terr,Yap_ErrorMessage);
	  return FALSE;
	} else /* FAIL ON PARSER ERROR */ {
	  Term t[2];
	  t[0] = terr;
	  t[1] = MkAtomTerm(Yap_LookupAtom(Yap_ErrorMessage));
	  Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
	  return Yap_unify(ARG6,Yap_MkApplTerm(Yap_MkFunctor(AtomError,2),2,t));
	}
      }
    } else {
      CurrentModule = OCurrentModule;
      /* parsing succeeded */
      break;
    }
  }
#if EMACS
  first_char = tokstart->TokPos;
#endif /* EMACS */
  if (!Yap_unify(t, ARG2))
    return FALSE;
  if (AtomOfTerm (Deref (ARG1)) == AtomTrue) {
    while (TRUE) {
      CELL *old_H = H;

      if (setjmp(Yap_IOBotch) == 0) {
	v = Yap_VarNames(Yap_VarTable, TermNil);
	break;
      } else {
	tr_fr_ptr old_TR;
	restore_machine_regs();

	old_TR = TR;
	/* restart global */
	H = old_H;
	TR = (tr_fr_ptr)ScannerStack;
	Yap_growstack_in_parser(&old_TR, &tokstart, &Yap_VarTable);
	ScannerStack = (char *)TR;
	TR = old_TR;
      }
    }
    Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
    return Yap_unify (v, ARG4);
  } else {
    Yap_clean_tokenizer(tokstart, Yap_VarTable, Yap_AnonVarTable);
    return TRUE;
  }
}

static Int
p_read (void)
{				/* '$read'(+Flag,?Term,?Module,?Vars,-Pos,-Err)    */
  return do_read(NULL, 6);
}

extern int getInputStream(Int, IOSTREAM **);

static Int
p_read2 (void)
{				/* '$read2'(+Flag,?Term,?Module,?Vars,-Pos,-Err,+Stream)  */
  IOSTREAM *inp_stream;
  Int out;

  if (!getInputStream(Yap_InitSlot(Deref(ARG7)), &inp_stream)) {
    return(FALSE);
  }
  out = do_read(inp_stream, 7);
  return out;
}


static Term
StreamPosition(IOSTREAM *st)
{
  Term t[4];
  t[0] = MkIntegerTerm(st->posbuf.charno);
  t[1] = MkIntegerTerm(st->posbuf.lineno);
  t[2] = MkIntegerTerm(st->posbuf.linepos);
  t[3] = MkIntegerTerm(st->posbuf.byteno);
  return Yap_MkApplTerm(FunctorStreamPos,4,t);
}

Term
Yap_StreamPosition(IOSTREAM *st)
{
  return StreamPosition(st);
}

#if HAVE_SELECT && FALSE
/* stream_select(+Streams,+TimeOut,-Result)      */
static Int
p_stream_select(void)
{
  Term t1 = Deref(ARG1), t2;
  fd_set readfds, writefds, exceptfds;
  struct timeval timeout, *ptime;

#if _MSC_VER
  u_int fdmax=0;
#else
  int fdmax=0;
#endif
  Term tout = TermNil, ti, Head;

  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR,t1,"stream_select/3");
    return FALSE;
  }
  if (!IsPairTerm(t1)) {
    Yap_Error(TYPE_ERROR_LIST,t1,"stream_select/3");
    return(FALSE);
  }
  FD_ZERO(&readfds);
  FD_ZERO(&writefds);
  FD_ZERO(&exceptfds);
  ti = t1;
  while (ti != TermNil) {
#if _MSC_VER
    u_int fd;
#else
    int fd;
#endif
    int sno;

    Head = HeadOfTerm(ti);
    sno  = CheckStream(Head, Input_Stream_f, "stream_select/3");
    if (sno < 0)
      return(FALSE);
    fd = GetStreamFd(sno);
    FD_SET(fd, &readfds);
    UNLOCK(Stream[sno].streamlock);
    if (fd > fdmax)
      fdmax = fd;
    ti = TailOfTerm(ti);
  }
  t2 = Deref(ARG2);
  if (IsVarTerm(t2)) {
    Yap_Error(INSTANTIATION_ERROR,t2,"stream_select/3");
    return(FALSE);
  }
  if (IsAtomTerm(t2)) {
    if (t2 == MkAtomTerm(AtomOff)) {
      /* wait indefinitely */
      ptime = NULL;
    } else {
      Yap_Error(DOMAIN_ERROR_TIMEOUT_SPEC,t1,"stream_select/3");
      return(FALSE);
    }
  } else {
    Term t21, t22;

    if (!IsApplTerm(t2) || FunctorOfTerm(t2) != FunctorModule) {
      Yap_Error(DOMAIN_ERROR_TIMEOUT_SPEC,t2,"stream_select/3");
      return(FALSE);
    }
    t21 = ArgOfTerm(1, t2);
    if (IsVarTerm(t21)) {
      Yap_Error(INSTANTIATION_ERROR,t2,"stream_select/3");
      return(FALSE);
    }
    if (!IsIntegerTerm(t21)) {
      Yap_Error(DOMAIN_ERROR_TIMEOUT_SPEC,t2,"stream_select/3");
      return(FALSE);
    }
    timeout.tv_sec = IntegerOfTerm(t21);
    if (timeout.tv_sec < 0) {
      Yap_Error(DOMAIN_ERROR_TIMEOUT_SPEC,t2,"stream_select/3");
      return(FALSE);
    }
    t22 = ArgOfTerm(2, t2);
    if (IsVarTerm(t22)) {
      Yap_Error(INSTANTIATION_ERROR,t2,"stream_select/3");
      return(FALSE);
    }
    if (!IsIntegerTerm(t22)) {
      Yap_Error(DOMAIN_ERROR_TIMEOUT_SPEC,t2,"stream_select/3");
      return(FALSE);
    }
    timeout.tv_usec = IntegerOfTerm(t22);
    if (timeout.tv_usec < 0) {
      Yap_Error(DOMAIN_ERROR_TIMEOUT_SPEC,t2,"stream_select/3");
      return(FALSE);
    }
    ptime = &timeout;
  }
  /* do the real work */
  if (select(fdmax+1, &readfds, &writefds, &exceptfds, ptime) < 0) {
#if HAVE_STRERROR
      Yap_Error(SYSTEM_ERROR, TermNil, 
	    "stream_select/3 (select: %s)", strerror(errno));
#else
      Yap_Error(SYSTEM_ERROR, TermNil,
	    "stream_select/3 (select)");
#endif
  }
  while (t1 != TermNil) {
    int fd;
    int sno;

    Head = HeadOfTerm(t1);
    sno  = CheckStream(Head, Input_Stream_f, "stream_select/3");
    fd = GetStreamFd(sno);
    if (FD_ISSET(fd, &readfds))
      tout = MkPairTerm(Head,tout);
    else 
      tout = MkPairTerm(TermNil,tout);
    UNLOCK(Stream[sno].streamlock);
    t1 = TailOfTerm(t1);
  }
  /* we're done, just pass the info back */
  return(Yap_unify(ARG3,tout));

}
#endif

static Int
p_change_type_of_char (void)
{				/* change_type_of_char(+char,+type)      */
  Term t1 = Deref (ARG1);
  Term t2 = Deref (ARG2);
  if (!IsVarTerm (t1) && !IsIntegerTerm (t1))
    return FALSE;
  if (!IsVarTerm(t2) && !IsIntegerTerm(t2))
    return FALSE;
  Yap_chtype[IntegerOfTerm(t1)] = IntegerOfTerm(t2);
  return TRUE;
}

static Int
p_type_of_char (void)
{				/* type_of_char(+char,-type)      */
  Term t;

  Term t1 = Deref (ARG1);
  if (!IsVarTerm (t1) && !IsIntegerTerm (t1))
    return FALSE;
  t = MkIntTerm(Yap_chtype[IntegerOfTerm (t1)]);
  return Yap_unify(t,ARG2);
}


static Int 
p_force_char_conversion(void)
{
  /* don't actually enable it until someone tries to add a conversion */
  if (CharConversionTable2 == NULL)
    return(TRUE);
  CharConversionTable = CharConversionTable2;
  return(TRUE);
}

static Int 
p_disable_char_conversion(void)
{
  int i;

  for (i = 0; i < MaxStreams; i++) {
    if (!(Stream[i].status & Free_Stream_f))
      Stream[i].stream_wgetc_for_read = Stream[i].stream_wgetc;
  }
  CharConversionTable = NULL;
  return(TRUE);
}

static Int 
p_char_conversion(void)
{
  Term t0 = Deref(ARG1), t1 = Deref(ARG2);
  char *s0, *s1;

  if (IsVarTerm(t0)) {
    Yap_Error(INSTANTIATION_ERROR, t0, "char_conversion/2");
    return (FALSE);    
  }
  if (!IsAtomTerm(t0)) {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t0, "char_conversion/2");
    return (FALSE);    
  }
  s0 = RepAtom(AtomOfTerm(t0))->StrOfAE;
  if (s0[1] != '\0') {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t0, "char_conversion/2");
    return (FALSE);    
  }
  if (IsVarTerm(t1)) {
    Yap_Error(INSTANTIATION_ERROR, t1, "char_conversion/2");
    return (FALSE);    
  }
  if (!IsAtomTerm(t1)) {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t1, "char_conversion/2");
    return (FALSE);    
  }
  s1 = RepAtom(AtomOfTerm(t1))->StrOfAE;
  if (s1[1] != '\0') {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t1, "char_conversion/2");
    return (FALSE);    
  }
  /* check if we do have a table for converting characters */
  if (CharConversionTable2 == NULL) {
    int i;

    /* don't create a table if we don't need to */
    if (s0[0] == s1[0])
      return(TRUE);
    CharConversionTable2 = Yap_AllocCodeSpace(NUMBER_OF_CHARS*sizeof(char));
    while (CharConversionTable2 == NULL) {
      if (!Yap_growheap(FALSE, NUMBER_OF_CHARS*sizeof(char), NULL)) {
	Yap_Error(OUT_OF_HEAP_ERROR, TermNil, Yap_ErrorMessage);
	return(FALSE);
      }
    }
    if (yap_flags[CHAR_CONVERSION_FLAG] != 0) {
      if (p_force_char_conversion() == FALSE)
	return(FALSE);
    }
    for (i = 0; i < NUMBER_OF_CHARS; i++) 
      CharConversionTable2[i] = i;
  }
  /* just add the new entry */
  CharConversionTable2[(int)s0[0]] = s1[0];
  /* done */
  return(TRUE);
}

static Int 
p_current_char_conversion(void)
{
  Term t0, t1;
  char *s0, *s1;

  if (CharConversionTable == NULL) {
    return(FALSE);
  }
  t0 = Deref(ARG1);
  if (IsVarTerm(t0)) {
    Yap_Error(INSTANTIATION_ERROR, t0, "current_char_conversion/2");
    return (FALSE);    
  }
  if (!IsAtomTerm(t0)) {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t0, "current_char_conversion/2");
    return (FALSE);    
  }
  s0 = RepAtom(AtomOfTerm(t0))->StrOfAE;
  if (s0[1] != '\0') {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t0, "current_char_conversion/2");
    return (FALSE);    
  }
  t1 = Deref(ARG2);
  if (IsVarTerm(t1)) {
    char out[2];
    if (CharConversionTable[(int)s0[0]] == '\0') return(FALSE);
    out[0] = CharConversionTable[(int)s0[0]];
    out[1] = '\0';
    return(Yap_unify(ARG2,MkAtomTerm(Yap_LookupAtom(out))));
  }
  if (!IsAtomTerm(t1)) {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t1, "current_char_conversion/2");
    return (FALSE);    
  }
  s1 = RepAtom(AtomOfTerm(t1))->StrOfAE;
  if (s1[1] != '\0') {
    Yap_Error(REPRESENTATION_ERROR_CHARACTER, t1, "current_char_conversion/2");
    return (FALSE);    
  } else {
    return (CharConversionTable[(int)s0[0]] == '\0' &&
	    CharConversionTable[(int)s0[0]] == s1[0] );
  }
}

static Int 
p_all_char_conversions(void)
{
  Term out = TermNil;
  int i;

  if (CharConversionTable == NULL) {
    return(FALSE);
  }
  for (i = NUMBER_OF_CHARS; i > 0; ) {
    i--;
    if (CharConversionTable[i] != '\0') {
      Term t1, t2;
      char s[2];
      s[1] = '\0';
      s[0] = CharConversionTable[i];
      t1 = MkAtomTerm(Yap_LookupAtom(s));
      out = MkPairTerm(t1,out);
      s[0] = i;
      t2 = MkAtomTerm(Yap_LookupAtom(s));
      out = MkPairTerm(t2,out);
    }
  }
  return(Yap_unify(ARG1,out));
}

static Int
p_float_format(void)
{
  Term in = Deref(ARG1);
  if (IsVarTerm(in))
    return Yap_unify(ARG1, MkAtomTerm(AtomFloatFormat));
  AtomFloatFormat = AtomOfTerm(in);
  return TRUE;
}

extern IOENC Yap_DefaultEncoding(void);
extern void  Yap_SetDefaultEncoding(IOENC);
extern int   PL_get_stream_handle(Int, IOSTREAM **);

static Int
p_get_default_encoding(void)
{
  Term out = MkIntegerTerm(Yap_DefaultEncoding());
  return Yap_unify(ARG1, out);
}

static Int
p_encoding (void)
{				/* '$encoding'(Stream,N)                      */
  IOSTREAM *st;
  Term t = Deref(ARG2);
  if (!PL_get_stream_handle(Yap_InitSlot(Deref(ARG1)), &st)) {
    return FALSE;
  }
  if (IsVarTerm(t)) {
    return Yap_unify(ARG2, MkIntegerTerm(st->encoding));
  }
  st->encoding = IntegerOfTerm(Deref(ARG2));
  return TRUE;
}


void
Yap_InitBackIO (void)
{
}


void
Yap_InitIOPreds(void)
{
  Yap_stdin = stdin;
  Yap_stdout = stdout;
  Yap_stderr = stderr;
  if (!Stream)
    Stream = (StreamDesc *)Yap_AllocCodeSpace(sizeof(StreamDesc)*MaxStreams);
  /* here the Input/Output predicates */
  Yap_InitCPred ("$set_read_error_handler", 1, p_set_read_error_handler, SafePredFlag|SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$get_read_error_handler", 1, p_get_read_error_handler, SafePredFlag|SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$read", 6, p_read, SyncPredFlag|HiddenPredFlag|UserCPredFlag);
  Yap_InitCPred ("$read", 7, p_read2, SyncPredFlag|HiddenPredFlag|UserCPredFlag);
  Yap_InitCPred ("$start_line", 1, p_startline, SafePredFlag|SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$change_type_of_char", 2, p_change_type_of_char, SafePredFlag|SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$type_of_char", 2, p_type_of_char, SafePredFlag|SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("char_conversion", 2, p_char_conversion, SyncPredFlag);
  Yap_InitCPred ("$current_char_conversion", 2, p_current_char_conversion, SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$all_char_conversions", 1, p_all_char_conversions, SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$force_char_conversion", 0, p_force_char_conversion, SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$disable_char_conversion", 0, p_disable_char_conversion, SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$get_default_encoding", 1, p_get_default_encoding, SafePredFlag|TestPredFlag);
  Yap_InitCPred ("$encoding", 2, p_encoding, SafePredFlag|SyncPredFlag),
#if HAVE_SELECT
    //  Yap_InitCPred ("stream_select", 3, p_stream_select, SafePredFlag|SyncPredFlag);
#endif
  Yap_InitCPred ("$float_format", 1, p_float_format, SafePredFlag|SyncPredFlag|HiddenPredFlag);
  Yap_InitCPred ("$has_readline", 0, p_has_readline, SafePredFlag|HiddenPredFlag);

}

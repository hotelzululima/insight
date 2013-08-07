/*-
 * Copyright (C) 2010-2013, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS AND CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#ifndef X86_TRANSLATE_HH
#define X86_TRANSLATE_HH

#include <string>
#include <vector>
#include <stdexcept>

#include <decoders/Decoder.hh>
#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>

#include "decoders/binutils/x86/x86_parser.hh"

typedef x86::parser::token_type TokenType;

#define TMPREG(_i) ("tmpr" #_i)

#define X86_TOKEN(tok) x86::parser::token:: TOK_ ## tok

typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;

/* --------------- */

template<TokenType> void
x86_translate(x86::parser_data &data, bool)
{
  throw Decoder::UnknownMnemonic (data.instruction);
}

#define X86_TRANSLATE_PREFIX(_tok) \
  template<> void \
  x86_translate<X86_TOKEN(_tok)> (x86::parser_data &data, bool start)

/* --------------- */

#if 1
#define DEFAULT_DATA data
#define DEFAULT_BEHAVIOR() \
  do { throw Decoder::UnknownMnemonic (data.instruction); } while(0)
#else
#define DEFAULT_DATA data
#define DEFAULT_BEHAVIOR() \
  do { std::cout << data.instruction << std::endl; \
    data.mc->add_skip (data.start_ma, data.next_ma); } while(0)
#endif

template<TokenType> void
x86_translate(x86::parser_data &DEFAULT_DATA)
{
  DEFAULT_BEHAVIOR();
}

#define X86_TRANSLATE_0_OP(_tok) \
  template<> void \
  x86_translate<X86_TOKEN(_tok)> (x86::parser_data &data)

/* --------------- */

template<TokenType> void
x86_translate(x86::parser_data &DEFAULT_DATA, Expr *op1)
{
  try { DEFAULT_BEHAVIOR(); } catch(...) { op1->deref (); throw; }
}

#define X86_TRANSLATE_1_OP(_tok) \
  template<> void \
  x86_translate<X86_TOKEN(_tok)> (x86::parser_data &data, Expr *op1)


/* --------------- */

template<TokenType> void
x86_translate(x86::parser_data &DEFAULT_DATA, Expr *op1, Expr *op2)
{
  try { DEFAULT_BEHAVIOR(); } 
  catch(...) {
    op1->deref ();
    op2->deref ();
    throw;
  }
}

#define X86_TRANSLATE_2_OP(_tok) \
  template<> void \
  x86_translate<X86_TOKEN(_tok)> (x86::parser_data &data, Expr *op1, \
					Expr *op2)

/* --------------- */

template<TokenType> void
x86_translate(x86::parser_data &DEFAULT_DATA, Expr *op1, Expr *op2, 
		 Expr *op3)
{
  try { DEFAULT_BEHAVIOR(); }
  catch (...) {
    op1->deref ();
    op2->deref ();
    op3->deref ();
    throw;
  }
}

#define X86_TRANSLATE_3_OP(_tok) \
  template<> void \
  x86_translate<X86_TOKEN(_tok)> (x86::parser_data &data, Expr *op1, \
					Expr *op2, Expr *op3)

/* --------------- */

template<TokenType> void
x86_translate(x86::parser_data &DEFAULT_DATA, Expr *op1, Expr *op2, 
		 Expr *op3, Expr *op4)
{
  try {  DEFAULT_BEHAVIOR(); }
  catch(...) {
    op1->deref ();
    op2->deref ();
    op3->deref ();
    op4->deref ();
    throw;
  }
}

#define X86_TRANSLATE_4_OP(_tok) \
  template<> void \
  x86_translate<X86_TOKEN(_tok)> (x86::parser_data &data, Expr *op1, \
					Expr *op2, Expr *op3, Expr *op4)

/* --------------- */

LValue *x86_translate_esp(x86::parser_data &data);

			/* --------------- */

void 
x86_skip (x86::parser_data &data);


void 
x86_set_operands_size (Expr *&dst, Expr *&src);


typedef void 
x86_compute_flag_proc (MicrocodeAddress &, x86::parser_data &, 
			  const Expr *value, MicrocodeAddress *);

void 
x86_assign_flag (MicrocodeAddress &from, x86::parser_data &data, 
		    const char *flag, bool value, MicrocodeAddress *to = NULL);

			/* --------------- */

void 
x86_set_flag (MicrocodeAddress &from, x86::parser_data &data, 
		 const char *flag, MicrocodeAddress *to = NULL);

void 
x86_reset_flag (MicrocodeAddress &from, x86::parser_data &data, 
		   const char *flag, MicrocodeAddress *to = NULL);

			/* --------------- */

void 
x86_reset_flags (MicrocodeAddress &from, x86::parser_data &data, 
		    const char **flags, MicrocodeAddress *to = NULL);

void 
x86_assign_AF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
x86_compute_AF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
x86_reset_AF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
x86_compute_CF (MicrocodeAddress &from, x86::parser_data &data, 
		   Expr *dst, Expr *value, MicrocodeAddress *to = NULL);

void 
x86_assign_CF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
x86_reset_CF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
x86_compute_OF (MicrocodeAddress &from, x86::parser_data &data, 
		   Expr *dst, Expr *value, MicrocodeAddress *to = NULL);

void 
x86_assign_OF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
x86_reset_OF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
x86_assign_PF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
x86_compute_PF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
x86_reset_PF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
x86_assign_SF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
x86_compute_SF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
x86_reset_SF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
x86_assign_ZF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
x86_compute_ZF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
x86_reset_ZF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void
x86_push (MicrocodeAddress &start, x86::parser_data &data, Expr *op,
	     MicrocodeAddress *end = NULL);

void
x86_pop (MicrocodeAddress &start, x86::parser_data &data, LValue *op,
	    MicrocodeAddress *end = NULL);


void
x86_translate_with_size (x86::parser_data &data,
			    Expr *op1, Expr *op2, int size,
			    void (*tr) (x86::parser_data &,Expr *, Expr *));

void
x86_translate_with_size (x86::parser_data &data,
			    Expr *op1, int size,
			    void (*tr) (x86::parser_data &, Expr *));

void 
x86_if_then_else (MicrocodeAddress start, x86::parser_data &data,
		     Expr *cond,
		     MicrocodeAddress ifaddr, MicrocodeAddress elseaddr);

void
x86_cmpgen (MicrocodeAddress &from, x86::parser_data &data, 
	       Expr *op1, Expr *op2, MicrocodeAddress *to);

#include "x86_translation_functions.hh"

#endif /* ! X86_TRANSLATE_HH */

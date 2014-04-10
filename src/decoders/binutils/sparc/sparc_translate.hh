/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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

#ifndef SPARC_TRANSLATE_HH
#define SPARC_TRANSLATE_HH

#include <string>
#include <vector>
#include <stdexcept>

#include <decoders/Decoder.hh>
#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>

#include "decoders/binutils/sparc/sparc_parser.hh"

typedef sparc::parser::token_type TokenType;

#define TMPREG(_i) ("tmpr" #_i)

#define SPARC_TOKEN(tok) sparc::parser::token:: TOK_ ## tok

typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;

/* --------------- */

template<TokenType> void
sparc_translate(sparc::parser_data &data, bool)
{
  throw Decoder::UnknownMnemonic (data.instruction);
}

#define SPARC_TRANSLATE_PREFIX(_tok) \
  template<> void \
  sparc_translate<SPARC_TOKEN(_tok)> (sparc::parser_data &data, bool start)

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
sparc_translate(sparc::parser_data &DEFAULT_DATA)
{
  DEFAULT_BEHAVIOR();
}

#define SPARC_TRANSLATE_0_OP(_tok) \
  template<> void \
  sparc_translate<SPARC_TOKEN(_tok)> (sparc::parser_data &data)

/* --------------- */

template<TokenType> void
sparc_translate(sparc::parser_data &DEFAULT_DATA, Expr *op1)
{
  try { DEFAULT_BEHAVIOR(); } catch(...) { op1->deref (); throw; }
}

#define SPARC_TRANSLATE_1_OP(_tok) \
  template<> void \
  sparc_translate<SPARC_TOKEN(_tok)> (sparc::parser_data &data, Expr *op1)


/* --------------- */

template<TokenType> void
sparc_translate(sparc::parser_data &DEFAULT_DATA, Expr *op1, Expr *op2)
{
  try { DEFAULT_BEHAVIOR(); } 
  catch(...) {
    op1->deref ();
    op2->deref ();
    throw;
  }
}

#define SPARC_TRANSLATE_2_OP(_tok) \
  template<> void \
  sparc_translate<SPARC_TOKEN(_tok)> (sparc::parser_data &data, Expr *op1, \
					Expr *op2)

/* --------------- */

template<TokenType> void
sparc_translate(sparc::parser_data &DEFAULT_DATA, Expr *op1, Expr *op2, 
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

#define SPARC_TRANSLATE_3_OP(_tok) \
  template<> void \
  sparc_translate<SPARC_TOKEN(_tok)> (sparc::parser_data &data, Expr *op1, \
					Expr *op2, Expr *op3)

/* --------------- */

template<TokenType> void
sparc_translate(sparc::parser_data &DEFAULT_DATA, Expr *op1, Expr *op2, 
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

#define SPARC_TRANSLATE_4_OP(_tok) \
  template<> void \
  sparc_translate<SPARC_TOKEN(_tok)> (sparc::parser_data &data, Expr *op1, \
					Expr *op2, Expr *op3, Expr *op4)

/* --------------- */

LValue *sparc_translate_esp(sparc::parser_data &data);

			/* --------------- */

void 
sparc_skip (sparc::parser_data &data);


void 
sparc_set_operands_size (Expr *&dst, Expr *&src);


typedef void 
sparc_compute_flag_proc (MicrocodeAddress &, sparc::parser_data &, 
			  const Expr *value, MicrocodeAddress *);

void 
sparc_assign_flag (MicrocodeAddress &from, sparc::parser_data &data, 
		    const char *flag, bool value, MicrocodeAddress *to = NULL);

			/* --------------- */

void 
sparc_set_flag (MicrocodeAddress &from, sparc::parser_data &data, 
		 const char *flag, MicrocodeAddress *to = NULL);

void 
sparc_reset_flag (MicrocodeAddress &from, sparc::parser_data &data, 
		   const char *flag, MicrocodeAddress *to = NULL);

			/* --------------- */

void 
sparc_reset_flags (MicrocodeAddress &from, sparc::parser_data &data, 
		    const char **flags, MicrocodeAddress *to = NULL);

void 
sparc_assign_AF (MicrocodeAddress &from, sparc::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
sparc_compute_AF (MicrocodeAddress &from, sparc::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
sparc_reset_AF (MicrocodeAddress &from, sparc::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
sparc_compute_CF (MicrocodeAddress &from, sparc::parser_data &data, 
		   Expr *dst, Expr *value, MicrocodeAddress *to = NULL);

void 
sparc_assign_CF (MicrocodeAddress &from, sparc::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
sparc_reset_CF (MicrocodeAddress &from, sparc::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
sparc_compute_OF (MicrocodeAddress &from, sparc::parser_data &data, 
		   Expr *dst, Expr *value, MicrocodeAddress *to = NULL);

void 
sparc_assign_OF (MicrocodeAddress &from, sparc::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
sparc_reset_OF (MicrocodeAddress &from, sparc::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
sparc_assign_PF (MicrocodeAddress &from, sparc::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
sparc_compute_PF (MicrocodeAddress &from, sparc::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
sparc_reset_PF (MicrocodeAddress &from, sparc::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
sparc_assign_SF (MicrocodeAddress &from, sparc::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
sparc_compute_SF (MicrocodeAddress &from, sparc::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
sparc_reset_SF (MicrocodeAddress &from, sparc::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void 
sparc_assign_ZF (MicrocodeAddress &from, sparc::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to = NULL);

void 
sparc_compute_ZF (MicrocodeAddress &from, sparc::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to = NULL);

void 
sparc_reset_ZF (MicrocodeAddress &from, sparc::parser_data &data, 
		 const Expr * = NULL, MicrocodeAddress *to = NULL);

void
sparc_push (MicrocodeAddress &start, sparc::parser_data &data, Expr *op,
	     MicrocodeAddress *end = NULL);

void
sparc_pop (MicrocodeAddress &start, sparc::parser_data &data, LValue *op,
	    MicrocodeAddress *end = NULL);


void
sparc_translate_with_size (sparc::parser_data &data,
			    Expr *op1, Expr *op2, int size,
			    void (*tr) (sparc::parser_data &,Expr *, Expr *));

void
sparc_translate_with_size (sparc::parser_data &data,
			    Expr *op1, int size,
			    void (*tr) (sparc::parser_data &, Expr *));

void 
sparc_if_then_else (MicrocodeAddress start, sparc::parser_data &data,
		     Expr *cond,
		     MicrocodeAddress ifaddr, MicrocodeAddress elseaddr);

void
sparc_cmpgen (MicrocodeAddress &from, sparc::parser_data &data, 
	       Expr *op1, Expr *op2, MicrocodeAddress *to);

#include "sparc_translation_functions.hh"

#endif /* ! SPARC_TRANSLATE_HH */

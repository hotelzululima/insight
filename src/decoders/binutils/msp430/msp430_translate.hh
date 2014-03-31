/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
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

#ifndef MSP430_TRANSLATE_HH
#define MSP430_TRANSLATE_HH

#include <string>
#include <vector>
#include <stdexcept>

#include <decoders/Decoder.hh>
#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>

#include "decoders/binutils/msp430/msp430_parser.hh"

typedef msp430::parser::token_type TokenType;

#define MSP430_TOKEN(tok) msp430::parser::token:: TOK_ ## tok

#define MSP430_SIZE_B	8
#define MSP430_SIZE_W	16
#define MSP430_SIZE_A	20

#define MSP430_REG_SP	"r1"
#define MSP430_REG_SR	"r2"

#define MSP430_FLAG_C		0
#define MSP430_FLAG_Z		1
#define MSP430_FLAG_N		2
#define MSP430_FLAG_GIE		3
#define MSP430_FLAG_CPUOFF	4
#define MSP430_FLAG_OSCOFF	5
#define MSP430_FLAG_SCG0	6
#define MSP430_FLAG_SCG1	7
#define MSP430_FLAG_V		8

typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;

/* --------------- */

template<TokenType> void
msp430_translate(msp430::parser_data &data, bool)
{
  throw Decoder::UnknownMnemonic (data.instruction);
}

/* --------------- */

#define DEFAULT_DATA data
#define DEFAULT_BEHAVIOR() \
  do { throw Decoder::UnknownMnemonic (data.instruction); } while(0)

template<TokenType> void
msp430_translate(msp430::parser_data &DEFAULT_DATA)
{
  DEFAULT_BEHAVIOR();
}

#define MSP430_TRANSLATE_0_OP(_tok) \
  template<> void \
  msp430_translate<MSP430_TOKEN(_tok)> (msp430::parser_data &data)

/* --------------- */

template<TokenType> void
msp430_translate(msp430::parser_data &DEFAULT_DATA, Expr *op1)
{
  try { DEFAULT_BEHAVIOR(); } catch(...) { op1->deref (); throw; }
}

#define MSP430_TRANSLATE_1_OP(_tok) \
  template<> void \
  msp430_translate<MSP430_TOKEN(_tok)> (msp430::parser_data &data, Expr *op1)


/* --------------- */

template<TokenType> void
msp430_translate(msp430::parser_data &DEFAULT_DATA, Expr *op1, Expr *op2)
{
  try { DEFAULT_BEHAVIOR(); }
  catch(...) {
    op1->deref ();
    op2->deref ();
    throw;
  }
}

#define MSP430_TRANSLATE_2_OP(_tok) \
  template<> void \
  msp430_translate<MSP430_TOKEN(_tok)> (msp430::parser_data &data, Expr *op1, \
					Expr *op2)

/* --------------- */

void msp430_skip (msp430::parser_data &data);

Expr *msp430_trim_source_operand(msp430::parser_data &data, Expr *source);
Expr *msp430_stretch_expr_to_dest_size(Expr *dest, Expr *expr);

#endif /* ! MSP430_TRANSLATE_HH */

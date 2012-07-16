/*-
 * Copyright (C) 2010-2012, Centre National de la Recherche Scientifique,
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

#ifndef ARM_TRANSLATE_HH
#define ARM_TRANSLATE_HH

#include <string>
#include <vector>
#include <stdexcept>

#include <decoders/Decoder.hh>
#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>

#include "decoders/binutils/arm/arm_parser.hh"


typedef arm::parser::token_type TokenType;

#define ARM_TOKEN(tok) arm::parser::token:: TOK_ ## tok

typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;


#define N_FLAG 1
#define Z_FLAG 2
#define C_FLAG 4
#define V_FLAG 8

#define N_FLAG_BIT_POSITION 1
#define Z_FLAG_BIT_POSITION 2
#define C_FLAG_BIT_POSITION 3
#define V_FLAG_BIT_POSITION 4

enum UPDATE_FLAGS_FOR_INSTRUCTIONS {
  ADD_INS = N_FLAG + Z_FLAG + C_FLAG + V_FLAG,
  SUB_INS = N_FLAG + Z_FLAG + C_FLAG + V_FLAG,
  RSB_INS = N_FLAG + Z_FLAG + C_FLAG + V_FLAG,
  MOV_INS = N_FLAG + Z_FLAG + C_FLAG + V_FLAG,
  MVN_INS = N_FLAG + Z_FLAG + C_FLAG + V_FLAG,

  MUL_INS = N_FLAG + Z_FLAG,
  MLA_INS = N_FLAG + Z_FLAG,

  ASR_INS = N_FLAG + Z_FLAG + C_FLAG ,
  LSR_INS = N_FLAG + Z_FLAG + C_FLAG ,
  LSL_INS = N_FLAG + Z_FLAG + C_FLAG ,
  ROR_INS = N_FLAG + Z_FLAG + C_FLAG ,
  RRX_INS = N_FLAG + Z_FLAG + C_FLAG ,

  AND_INS = N_FLAG + Z_FLAG + C_FLAG ,
  EOR_INS = N_FLAG + Z_FLAG + C_FLAG ,
  ORR_INS = N_FLAG + Z_FLAG + C_FLAG ,
  BIC_INS = N_FLAG + Z_FLAG + C_FLAG,

  PUSH_INS = 0,
  POP_INS = 0,

  CMP_INS = N_FLAG + Z_FLAG + C_FLAG + V_FLAG,
  CMN_INS = N_FLAG + Z_FLAG + C_FLAG + V_FLAG,
};

/* --------------- */

template<TokenType> void
arm_translate(arm::parser_data &data, arm::MicrocodeNodeVector *)
{
  throw new UnknownMnemonic(data.instruction);
}

#define ARM_TRANSLATE_PREFIX(_tok) \
  template<> void \
  arm_translate<ARM_TOKEN(_tok)> (arm::parser_data &data)

/* --------------- */

#if 1
#define DEFAULT_DATA data
#define DEFAULT_BEHAVIOR() \
  do { throw new UnknownMnemonic(data.instruction); } while(0)
#else
#define DEFAULT_DATA
#define DEFAULT_BEHAVIOR() \
  do { (void)0; } while(0)
//do { cout << data.start_ma << '\t' << data.instruction << endl; } while(0)

#endif


/*---------------1_OP-------------------------------------------------------- */

//PUSH, POP
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA, std::list<RegisterExpr *> *)
{
  DEFAULT_BEHAVIOR();
}

/*---------------2_OP-------------------------------------------------------- */

//B, BL
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA, std::string*, int )
{
  DEFAULT_BEHAVIOR();
}

//BX
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA, std::string*, Expr * )
{
  DEFAULT_BEHAVIOR();
}

/*---------------3_OP-------------------------------------------------------- */
//UDIV, SDIV
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA, Expr *, Expr *, Expr *)
{
  DEFAULT_BEHAVIOR();
}

//STRD, CMP, CMN
template<TokenType> void
arm_translate(arm::parser_data &data, std::string*, Expr*, Expr*)
{
  DEFAULT_BEHAVIOR();
}


/*---------------4_OP-------------------------------------------------------- */

//MOV, MVN
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA, bool,
    std::string*, Expr *, Expr *)
{
  DEFAULT_BEHAVIOR();
}

//ADD8, ADD16, SUB8, SUB16
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA,
    std::string*, std::string*, Expr *, Expr *, Expr*)
{
  DEFAULT_BEHAVIOR();
}

//SUB, ADD, RSB
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA, bool,
    std::string*, Expr*, Expr *, Expr *)
{
  DEFAULT_BEHAVIOR();
}

/*---------------6_OP-------------------------------------------------------- */

//MLA
template<TokenType> void
arm_translate(arm::parser_data &DEFAULT_DATA, bool,
    std::string*, Expr*, Expr *, Expr *, Expr*)
{
  DEFAULT_BEHAVIOR();
}

/*---------------7_OP-------------------------------------------------------- */
//STR, LDR (1st)
template<TokenType> void arm_translate(arm::parser_data &DEFAULT_DATA, bool,
    bool, bool, bool, std::string*, Expr*, Expr*) {
  DEFAULT_BEHAVIOR();
}


/*---------------8_OP-------------------------------------------------------- */

//STR, LDR (2nd)
template<TokenType> void arm_translate(arm::parser_data &DEFAULT_DATA, bool,
    bool, bool, bool, std::string*, Expr*, Expr *, bool) {
  DEFAULT_BEHAVIOR();
}

//STR, LDR (3rd)
template<TokenType> void arm_translate(arm::parser_data &DEFAULT_DATA, bool,
    bool, bool, bool, std::string*, Expr*, Expr *, Expr *) {
  DEFAULT_BEHAVIOR();
}


LValue *arm_translate_register(arm::parser_data &data,
    const std::string &regname);

LValue *arm_translate_flags(arm::parser_data &data, const std::string &regname);

void arm_assign(arm::parser_data &data, const LValue *lval, const Expr *e);

void arm_inc(arm::parser_data &data, const LValue *lval, int val);

void arm_dec(arm::parser_data &data, const LValue *lval, int val);

Expr *arm_address(arm::parser_data &data, const Expr *segment, int offset,
    const Expr *base, const Expr *index, int scale);

MemCell *arm_memory_access(arm::parser_data &data, const Tag &tag,
    const Expr *segment, int offset, const Expr *base, const Expr *index,
    int scale);

void update_flags(arm::parser_data &data, Expr* guard, Expr* run_time_result,
    UPDATE_FLAGS_FOR_INSTRUCTIONS ins);

LValue *arm_translate_sp (arm::parser_data &data);

#include "arm_translation_functions.hh"

#endif /* ! arm_TRANSLATE_HH */

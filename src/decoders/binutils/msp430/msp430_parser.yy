%code requires {		  /*  -*- C++ -*- */
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

#include <map>
#include <string>
#include <stack>

#include <kernel/Architecture.hh>
#include <kernel/Microcode.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>

namespace msp430 {
  typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;
  struct parser_data
  {
    parser_data(MicrocodeArchitecture *arch, Microcode *out,
		 const std::string &inst, address_t start,
		 address_t next);
    ~parser_data();

    RegisterExpr *get_tmp_register(int size);
    RegisterExpr *get_register(const char *regname) const;

    Expr *get_memory_reference(int disp, Expr *bis, bool may_truncate);

    void add_postincrement(RegisterExpr *);
    bool has_postincrements() const;
    void finalize_postincrements(bool);

    std::string instruction;
    MicrocodeAddress start_ma;
    MicrocodeAddress next_ma;
    Microcode *mc;
    MicrocodeArchitecture *arch;

    int current_tmp_register;

    int operand_size;			/* in bits */
    int is_extended;			/* current instruction is an X one */

    RegisterExpr *post_increment_registers[2];
  };
}
}

 /* Bison specific options */
%skeleton "lalr1.cc"
%language "c++"
%require "2.4"
%defines
%define namespace "msp430"

 /* Initial rule is named 'start' */
%start start

 /* Parsing context */
%parse-param { parser_data &data }
/*%lex-param   { parser_data &data }*/

%locations
%initial-action
{
  /* Initialize the initial location */
  @$.begin.filename = @$.end.filename = &data.instruction;
};

%debug
%error-verbose

 /* Symbols */
%union
{
  constant_t   intValue;
  std::string *stringValue;
  class Expr  *expr;
  class RegisterExpr *reg;
};

%code {
using namespace std;
using namespace msp430;

#include "decoders/binutils/msp430/msp430_translate.hh"

#undef yylex
#define yylex msp430_lex

#define YY_DECL					\
 msp430::parser::token_type			\
   yylex(msp430::parser::semantic_type* yylval,	\
	 msp430::parser::location_type* yylloc)

 YY_DECL;

#include "msp430_scanner.hh"

#define push_mc(data) do { (data).mc.push (new Microcode ()); } while (0)

}

%token TOK_LPAR TOK_RPAR
%token TOK_COMMA TOK_COLON
%token TOK_PLUS TOK_MINUS
%token TOK_AMPAND TOK_SHARP TOK_AT
%token TOK_DOLLAR
%token TOK_ADDRSUFFIX TOK_BYTESUFFIX

%token <stringValue>  TOK_INVALID
%token                TOK_EOF      0 "end of buffer (EOF)"
%token                TOK_EOL        "end of line (EOL)"

%token <stringValue>  TOK_REGISTER   "register (REGISTER)"

%token <intValue>     TOK_INTEGER    "integer value (INTEGER)"

%token TOK_BAD		"BAD"
%token TOK_ADC		"ADC"
%token TOK_ADCX		"ADCX"
%token TOK_ADD		"ADD"
%token TOK_ADDA		"ADDA"
%token TOK_ADDX		"ADDX"
%token TOK_ADDC		"ADDC"
%token TOK_ADDCX	"ADDCX"
%token TOK_AND		"AND"
%token TOK_ANDX		"ANDX"
%token TOK_BIC		"BIC"
%token TOK_BICX		"BICX"
%token TOK_BIS		"BIS"
%token TOK_BISX		"BISX"
%token TOK_BIT		"BIT"
%token TOK_BITX		"BITX"
%token TOK_BR		"BR"
%token TOK_BRA		"BRA"
%token TOK_CALL		"CALL"
%token TOK_CALLA	"CALLA"
%token TOK_CLR		"CLR"
%token TOK_CLRA		"CLRA"
%token TOK_CLRX		"CLRX"
%token TOK_CLRC		"CLRC"
%token TOK_CLRN		"CLRN"
%token TOK_CLRZ		"CLRZ"
%token TOK_CMP		"CMP"
%token TOK_CMPA		"CMPA"
%token TOK_CMPX		"CMPX"
%token TOK_DADC		"DADC"
%token TOK_DADCX	"DADCX"
%token TOK_DADD		"DADD"
%token TOK_DADDX	"DADDX"
%token TOK_DEC		"DEC"
%token TOK_DECX		"DECX"
%token TOK_DECD		"DECD"
%token TOK_DECDA	"DECDA"
%token TOK_DECDX	"DECDX"
%token TOK_DINT		"DINT"
%token TOK_EINT		"EINT"
%token TOK_INC		"INC"
%token TOK_INCX		"INCX"
%token TOK_INCD		"INCD"
%token TOK_INCDA	"INCDA"
%token TOK_INCDX	"INCDX"
%token TOK_INV		"INV"
%token TOK_INVX		"INVX"
%token TOK_JC		"JC"
%token TOK_JZ		"JZ"
%token TOK_JGE		"JGE"
%token TOK_JL		"JL"
%token TOK_JMP		"JMP"
%token TOK_JN		"JN"
%token TOK_JNC		"JNC"
%token TOK_JNZ		"JNZ"
%token TOK_MOV		"MOV"
%token TOK_MOVA		"MOVA"
%token TOK_MOVX		"MOVX"
%token TOK_NOP		"NOP"
%token TOK_POP		"POP"
%token TOK_POPM		"POPM"
%token TOK_POPX		"POPX"
%token TOK_PUSH		"PUSH"
%token TOK_PUSHM	"PUSHM"
%token TOK_PUSHX	"PUSHX"
%token TOK_RET		"RET"
%token TOK_RETA		"RETA"
%token TOK_RETI		"RETI"
%token TOK_RLA		"RLA"
%token TOK_RLAM		"RLAM"
%token TOK_RLAX		"RLAX"
%token TOK_RLC		"RLC"
%token TOK_RLCX		"RLCX"
%token TOK_RRA		"RRA"
%token TOK_RRAM		"RRAM"
%token TOK_RRAX		"RRAX"
%token TOK_RRC		"RRC"
%token TOK_RRCM		"RRCM"
%token TOK_RRCX		"RRCX"
%token TOK_RRU		"RRU"
%token TOK_RRUM		"RRUM"
%token TOK_RRUX		"RRUX"
%token TOK_SBC		"SBC"
%token TOK_SBCX		"SBCX"
%token TOK_SETC		"SETC"
%token TOK_SETN		"SETN"
%token TOK_SETZ		"SETZ"
%token TOK_SUB		"SUB"
%token TOK_SUBA		"SUBA"
%token TOK_SUBX		"SUBX"
%token TOK_SUBC		"SUBC"
%token TOK_SUBCX	"SUBCX"
%token TOK_SWPB		"SWPB"
%token TOK_SWPBX	"SWPBX"
%token TOK_SXT		"SXT"
%token TOK_SXTX		"SXTX"
%token TOK_TST		"TST"
%token TOK_TSTA		"TSTA"
%token TOK_TSTX		"TSTX"
%token TOK_XOR		"XOR"
%token TOK_XORX		"XORX"

%type <expr> operand memory_reference
%type <reg> register trimmed_register

%type <intValue> integer immediate

%printer    { debug_stream() << $$; } <intValue>

%printer    { debug_stream() << *$$; } TOK_REGISTER
%destructor { delete $$; } TOK_REGISTER

%% /***** Parser rules *****/

start: instruction
;

operand:
  immediate { $$ = Constant::create ($1, 0, data.operand_size); }
| trimmed_register { $$ = $1; }
| memory_reference { $$ = $1; }
;

trimmed_register:
  register {
    Expr *tmp = $$;
    $$ =
     dynamic_cast<RegisterExpr*>(tmp->extract_bit_vector(0, data.operand_size));
    tmp->deref();
  }
;

register:
TOK_REGISTER
{
  $$ = data.get_register ($1->c_str ());
  if ($$ == NULL)
    {
      error (@1, ": error: unknown register " + *$1);
      delete $1;
      YYERROR;
    }
  else
    {
      delete $1;
    }
}
;

memory_reference:
  integer TOK_LPAR register TOK_RPAR {
    $$ = data.get_memory_reference($1, $3, true);
  }
| TOK_AT register { $$ = data.get_memory_reference(0, $2, false); }
| TOK_AT register TOK_PLUS {
  $$ = data.get_memory_reference(0, $2, false);
  data.add_postincrement($2);
  }
| TOK_DOLLAR integer {
  $$ = data.get_memory_reference(data.start_ma.getGlobal() + 2 + $2,
				 NULL, false);
  }
| TOK_AMPAND integer {
  $$ = data.get_memory_reference($2, NULL, false);
  }
;

immediate:
  TOK_SHARP integer { $$ = $2; }
;

integer:
  TOK_PLUS  TOK_INTEGER { $$ = $2; }
| TOK_MINUS TOK_INTEGER { $$ = -$2; }
| TOK_INTEGER           { $$ = $1; }
;

suffix:
  TOK_BYTESUFFIX { data.operand_size = 8; }
|
;

instruction:
  TOK_BAD { msp430_translate<MSP430_TOKEN(BAD)> (data); }
| call operand
  { msp430_translate<MSP430_TOKEN(CALL)> (data, $2); }
| clear suffix operand
  { msp430_translate<MSP430_TOKEN(CLR)> (data, $3); }
| move suffix operand TOK_COMMA operand
  { msp430_translate<MSP430_TOKEN(MOV)> (data, $3, $5); }
;

call:
  TOK_CALL
| TOK_CALLA { data.operand_size = MSP430_SIZE_A; data.is_extended = 1;}
;

clear:
  TOK_CLR
| TOK_CLRA { data.operand_size = MSP430_SIZE_A; data.is_extended = 1;}
| TOK_CLRX { data.is_extended = 1; }
;

move:
  TOK_MOV
| TOK_MOVA { data.operand_size = MSP430_SIZE_A; data.is_extended = 1;}
| TOK_MOVX { data.is_extended = 1; }
;

%% /***** Parser subroutines *****/

void
parser::error(const parser::location_type &loc,
	      const string &msg)
{
  cerr << loc << ":" << msg << endl;
}

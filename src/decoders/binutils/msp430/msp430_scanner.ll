%{                      /* -*- C++ -*- */
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


#include <cerrno>
#include <climits>
#include <cstdlib>
#include <sstream>
#include <string>
#include <unistd.h>

#include "msp430_parser.hh"

#define YY_DECL					 \
  msp430::parser::token_type			 \
    yylex(msp430::parser::semantic_type *yylval, \
	  msp430::parser::location_type *yylloc)

/* Work around an incompatibility in flex (at least versions 2.5.31
 * through 2.5.33): it generates code that does not conform to C89. */
/* FIXME: Is this needed when the option 'noyywrap' has been set ? */
#undef yywrap
#define yywrap() 1

/* By default yylex returns int, we use token_type. Unfortunately
 * yyterminate by default returns 0, which is not of token_type. */
#define yyterminate() return token::TOK_EOF

/* This disables inclusion of unistd.h, which is not available under
 * Visual C++ on Win32. The C++ scanner uses STL streams instead. */
#define YY_NO_UNISTD_H

/* This suffices to track locations accurately. Each time yylex is
 * invoked, the begin position is moved onto the end position. */
#define YY_USER_ACTION yylloc->columns(yyleng);

using namespace std;
using namespace msp430;

typedef parser::token token;


%}

 /* Flex efficiency tuning */
%option 7bit noyywrap nounput batch full align
%option prefix="msp430_"

 /* Getting the scanner to share with other architectures */
 // %option reentrant
 // %option bison-bridge
 // %option prefix="msp430_"

 /* Custom macros */
hexvalue  [0-9a-f]+
varname   [a-z][a-z0-9]+

%% /***** Lexer rules *****/

%{
  /* Reset location at the beginning of yylex() */
  yylloc->step();
%}

".a"		{ return token::TOK_ADDRSUFFIX; }
".b"		{ return token::TOK_BYTESUFFIX; }
"(bad)"		{ return token::TOK_BAD; }
"adc"		{ return token::TOK_ADC; }
"adcx"		{ return token::TOK_ADCX; }
"add"		{ return token::TOK_ADD; }
"adda"		{ return token::TOK_ADDA; }
"addx"		{ return token::TOK_ADDX; }
"addc"		{ return token::TOK_ADDC; }
"addcx"		{ return token::TOK_ADDCX; }
"and"		{ return token::TOK_AND; }
"andx"		{ return token::TOK_ANDX; }
"bic"		{ return token::TOK_BIC; }
"bicx"		{ return token::TOK_BICX; }
"bis"		{ return token::TOK_BIS; }
"bisx"		{ return token::TOK_BISX; }
"bit"		{ return token::TOK_BIT; }
"bitx"		{ return token::TOK_BITX; }
"br"		{ return token::TOK_BR; }
"bra"		{ return token::TOK_BRA; }
"call"		{ return token::TOK_CALL; }
"calla"		{ return token::TOK_CALLA; }
"clr"		{ return token::TOK_CLR; }
"clra"		{ return token::TOK_CLRA; }
"clrx"		{ return token::TOK_CLRX; }
"clrc"		{ return token::TOK_CLRC; }
"clrn"		{ return token::TOK_CLRN; }
"clrz"		{ return token::TOK_CLRZ; }
"cmp"		{ return token::TOK_CMP; }
"cmpa"		{ return token::TOK_CMPA; }
"cmpx"		{ return token::TOK_CMPX; }
"dadc"		{ return token::TOK_DADC; }
"dadcx"		{ return token::TOK_DADCX; }
"dadd"		{ return token::TOK_DADD; }
"daddx"		{ return token::TOK_DADDX; }
"dec"		{ return token::TOK_DEC; }
"decx"		{ return token::TOK_DECX; }
"decd"		{ return token::TOK_DECD; }
"decda"		{ return token::TOK_DECDA; }
"decdx"		{ return token::TOK_DECDX; }
"dint"		{ return token::TOK_DINT; }
"eint"		{ return token::TOK_EINT; }
"inc"		{ return token::TOK_INC; }
"incx"		{ return token::TOK_INCX; }
"incd"		{ return token::TOK_INCD; }
"incda"		{ return token::TOK_INCDA; }
"incdx"		{ return token::TOK_INCDX; }
"inv"		{ return token::TOK_INV; }
"invx"		{ return token::TOK_INVX; }
"jc"		{ return token::TOK_JC; }
"jz"		{ return token::TOK_JZ; }
"jge"		{ return token::TOK_JGE; }
"jl"		{ return token::TOK_JL; }
"jmp"		{ return token::TOK_JMP; }
"jn"		{ return token::TOK_JN; }
"jnc"		{ return token::TOK_JNC; }
"jnz"		{ return token::TOK_JNZ; }
"mov"		{ return token::TOK_MOV; }
"mova"		{ return token::TOK_MOVA; }
"movx"		{ return token::TOK_MOVX; }
"nop"		{ return token::TOK_NOP; }
"pop"		{ return token::TOK_POP; }
"popm"		{ return token::TOK_POPM; }
"popx"		{ return token::TOK_POPX; }
"push"		{ return token::TOK_PUSH; }
"pushm"		{ return token::TOK_PUSHM; }
"pushx"		{ return token::TOK_PUSHX; }
"ret"		{ return token::TOK_RET; }
"reta"		{ return token::TOK_RETA; }
"reti"		{ return token::TOK_RETI; }
"rla"		{ return token::TOK_RLA; }
"rlam"		{ return token::TOK_RLAM; }
"rlax"		{ return token::TOK_RLAX; }
"rlc"		{ return token::TOK_RLC; }
"rlcx"		{ return token::TOK_RLCX; }
"rra"		{ return token::TOK_RRA; }
"rram"		{ return token::TOK_RRAM; }
"rrax"		{ return token::TOK_RRAX; }
"rrc"		{ return token::TOK_RRC; }
"rrcm"		{ return token::TOK_RRCM; }
"rrcx"		{ return token::TOK_RRCX; }
"rrum"		{ return token::TOK_RRUM; }
"rrux"		{ return token::TOK_RRUX; }
"sbc"		{ return token::TOK_SBC; }
"sbcx"		{ return token::TOK_SBCX; }
"setc"		{ return token::TOK_SETC; }
"setn"		{ return token::TOK_SETN; }
"setz"		{ return token::TOK_SETZ; }
"sub"		{ return token::TOK_SUB; }
"suba"		{ return token::TOK_SUBA; }
"subx"		{ return token::TOK_SUBX; }
"subc"		{ return token::TOK_SUBC; }
"subcx"		{ return token::TOK_SUBCX; }
"swpb"		{ return token::TOK_SWPB; }
"swpbx"		{ return token::TOK_SWPBX; }
"sxt"		{ return token::TOK_SXT; }
"sxtx"		{ return token::TOK_SXTX; }
"tst"		{ return token::TOK_TST; }
"tsta"		{ return token::TOK_TSTA; }
"tstx"		{ return token::TOK_TSTX; }
"xor"		{ return token::TOK_XOR; }
"xorx"		{ return token::TOK_XORX; }


"," { return token::TOK_COMMA; }
"(" { return token::TOK_LPAR; }
")" { return token::TOK_RPAR; }
"+" { return token::TOK_PLUS; }
"-" { return token::TOK_MINUS; }
"#" { return token::TOK_SHARP; }
"&" { return token::TOK_AMPAND; }
"@" { return token::TOK_AT; }
"$" { return token::TOK_DOLLAR; }

 /* Comments */
";".*

 /* Spaces and end of lines */
[ \t]+ { yylloc->lines(yyleng); yylloc->step(); }
[\n]+  { yylloc->lines(yyleng); yylloc->step(); return token::TOK_EOL; }

 /* Integer values */
"0x"?{hexvalue} {
                   if (yytext[1] != 'x')
		     yylval->intValue = (constant_t) strtoll (yytext, NULL, 10);
		   else
		     {
		       char *s = yytext+2;
		       yylval->intValue = 0;
		       for (; *s; s++)
			 {
			   yylval->intValue *= 16;
			   if ('A' <= *s && *s <= 'F')
			     yylval->intValue += 10 + (*s - 'A');
			   else if ('a' <= *s && *s <= 'f')
			     yylval->intValue += 10 + (*s - 'a');
			   else
			     yylval->intValue += (*s - '0');
			 }
		     }
		   return token::TOK_INTEGER;
                }

"r"[0-9]|"r1"[0-5]	{
                yylval->stringValue = new string (yytext);
	        return token::TOK_REGISTER;
             }

 /* Anything else is probably an error */
.  {
     char tmp[2] = { yytext[0], 0 };
     yylval->stringValue = new string (tmp);
     return token::TOK_INVALID;
   }

%% /***** Lexer subroutines *****/


bool msp430_scanner_open(const string &instr)
{
  return yy_scan_string (instr.c_str ());
}

void msp430_scanner_close()
{
  yy_delete_buffer (YY_CURRENT_BUFFER);
}

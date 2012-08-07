%{
/* -*- C++ -*- */
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

#include <cerrno>
#include <climits>
#include <cstdlib>
#include <sstream>
#include <string>
#include <unistd.h>

#include <kernel/expressions/ExprParser.hh>
#include <kernel/expressions/ExprLexer.hh>

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
using namespace ExprParser;

typedef Parser::token token;


%}

 /* Flex efficiency tuning */
%option 7bit noyywrap nounput batch full align 
%option prefix="ExprParser_"


 /* Custom macros */
hexvalue  [0-9a-fA-F]+
varname   [a-z][a-z0-9]+
optype    [bswlqt]

 /* NOTE: optype immediately follows the operator/mnemonic and gives
  * the type of the handled data-size:
  * b = byte (8 bit)
  * s = short (16 bit integer) or single (32-bit floating point)
  * w = word (16 bit)
  * l = long (32 bit integer or 64-bit floating point)
  * q = quad (64 bit)
  * t = ten bytes (80-bit floating point)
  * _ = default (no postfix given) a word size in the current architecture.
  */


%% /***** Lexer rules *****/

%{
  /* Reset location at the beginning of yylex() */
  yylloc->step();
  (void) data;
%}

"ADD"     { yylval->bOp = BV_OP_ADD; return token::TOK_BINARY_OP; }
"AND"     { yylval->bOp = BV_OP_AND; return token::TOK_BINARY_OP; }
"CONCAT"     { yylval->bOp = BV_OP_CONCAT; return token::TOK_BINARY_OP; }
"DIV_S"   { yylval->bOp = BV_OP_DIV_S; return token::TOK_BINARY_OP; }
"DIV_U"   { yylval->bOp = BV_OP_DIV_U; return token::TOK_BINARY_OP; }
"EXTEND_S"   { yylval->bOp = BV_OP_EXTEND_S; return token::TOK_BINARY_OP; }
"EXTERN_U"   { yylval->bOp = BV_OP_EXTEND_U; return token::TOK_BINARY_OP; }
"LSH"     { yylval->bOp = BV_OP_LSH; return token::TOK_BINARY_OP; }
"MODULO"  { yylval->bOp = BV_OP_MODULO; return token::TOK_BINARY_OP; }
"MUL_S"   { yylval->bOp = BV_OP_MUL_S; return token::TOK_BINARY_OP; }
"MUL_U"   { yylval->bOp = BV_OP_MUL_U; return token::TOK_BINARY_OP; }
"OR"      { yylval->bOp = BV_OP_OR; return token::TOK_BINARY_OP; }
"POW"     { yylval->bOp = BV_OP_POW; return token::TOK_BINARY_OP; }
"ROL"     { yylval->bOp = BV_OP_ROL; return token::TOK_BINARY_OP; }
"ROR"     { yylval->bOp = BV_OP_ROR; return token::TOK_BINARY_OP; }
"RSH_S"   { yylval->bOp = BV_OP_RSH_S; return token::TOK_BINARY_OP; }
"RSH_U"   { yylval->bOp = BV_OP_RSH_U; return token::TOK_BINARY_OP; }
"SUB"     { yylval->bOp = BV_OP_SUB; return token::TOK_BINARY_OP; }
"XOR"     { yylval->bOp = BV_OP_XOR; return token::TOK_BINARY_OP; }

"EQ"      { yylval->bOp = BV_OP_EQ; return token::TOK_COMPARE_OP; }
"NEQ"     { yylval->bOp = BV_OP_NEQ; return token::TOK_COMPARE_OP; }
"GEQ_S"   { yylval->bOp = BV_OP_GEQ_S; return token::TOK_COMPARE_OP; }
"GEQ_U"   { yylval->bOp = BV_OP_GEQ_U; return token::TOK_COMPARE_OP; }
"GT_S"    { yylval->bOp = BV_OP_GT_S; return token::TOK_COMPARE_OP; }
"GT_U"    { yylval->bOp = BV_OP_GT_U; return token::TOK_COMPARE_OP; }
"LEQ_S"   { yylval->bOp = BV_OP_LEQ_S; return token::TOK_COMPARE_OP; }
"LEQ_U"   { yylval->bOp = BV_OP_LEQ_U; return token::TOK_COMPARE_OP; }
"LT_S"    { yylval->bOp = BV_OP_LT_S; return token::TOK_COMPARE_OP; }
"LT_U"    { yylval->bOp = BV_OP_LT_U; return token::TOK_COMPARE_OP; }

"FORALL"  { return token::TOK_FORALL; }
"EXIST"   { return token::TOK_EXIST; }

"NEG"     { yylval->uOp = BV_OP_NEG; return token::TOK_UNARY_OP; }
"NOT"     { yylval->uOp = BV_OP_NOT; return token::TOK_UNARY_OP; }

"EXTRACT" { yylval->tOp = BV_OP_EXTRACT; return token::TOK_TERNARY_OP; }

";" { return token::TOK_SEMICOLON; }
"(" { return token::TOK_LPAR; }
")" { return token::TOK_RPAR; }
"{" { return token::TOK_LBRACE; }
"}" { return token::TOK_RBRACE; }
"[" { return token::TOK_LBRACKET; }
"]" { return token::TOK_RBRACKET; }
"%" { return token::TOK_PERCENT; }

[A-Za-z][A-Za-z0-9_,.-]* {
    yylval->stringValue = new std::string (yytext, yyleng);

    return token::TOK_STRING;
}


 /* Spaces and end of lines */
[ \t]+ { yylloc->lines(yyleng); yylloc->step(); }
[\n]+  { yylloc->lines(yyleng); yylloc->step(); }

 /* Integer values */
"0x"?{hexvalue} {
                   if (yytext[1] != 'x')
		     yylval->intValue = strtol (yytext, NULL, 10);
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

 /* Anything else is probable an error */
.  { 
     char tmp[2] = { yytext[0], 0 };
     yylval->stringValue = new string (tmp);
     return token::TOK_INVALID;
   }

%% /***** Lexer subroutines *****/


bool 
ExprParser::init_lexer (const string &input)
{
  return yy_scan_string (input.c_str ());
}

void 
ExprParser::terminate_lexer ()
{
  yy_delete_buffer (YY_CURRENT_BUFFER);
}

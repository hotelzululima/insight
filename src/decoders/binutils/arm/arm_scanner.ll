%{                      /* -*- C++ -*- */
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

#include "arm_parser.hh"

#define YY_DECL				      \
  arm::parser::token_type		      \
    yylex(arm::parser::semantic_type* yylval, \
          arm::parser::location_type* yylloc)

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
using namespace arm;

typedef parser::token token;

static long xtoi(char* xstr);

%}

 /* Flex efficiency tuning */
%option 7bit noyywrap nounput batch full align
%option prefix="arm_"

 /* Custom macros */
decvalue  [0-9]+	
hexvalue  [0-9a-f]+
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
  */


%% /***** Lexer rules *****/

%{
  /* Reset location at the beginning of yylex() */
  yylloc->step();
%}

"t"	{return token::TOK_PROCESSOR_MODE_SUFFIX;}
"s"	{return token::TOK_S_UPDATE_COND_FLAG_SUFFIX_OR_PREFIX;}
"d"	{return token::TOK_DOUBLE_WORD_SUFFIX;}
"h"	{return token::TOK_HALF_WORD_SUFFIX;}

"q"	{return token::TOK_PREFIX_FOR_PARALLEL_INS_Q;}
"sh"	{return token::TOK_PREFIX_FOR_PARALLEL_INS_SH;}
"u"	{return token::TOK_PREFIX_FOR_PARALLEL_INS_U;}
"uq"	{return token::TOK_PREFIX_FOR_PARALLEL_INS_UQ;}
"uh"	{return token::TOK_PREFIX_FOR_PARALLEL_INS_UH;}

"," { return token::TOK_COMMA;     }
":" { return token::TOK_SEMICOLON; }
"(" { return token::TOK_LPAR;      }
")" { return token::TOK_RPAR;      }
"+" { return token::TOK_PLUS;      }
"-" { return token::TOK_MINUS;     }
"*" { return token::TOK_STAR;      }
"$" { return token::TOK_DOLLAR;    }
"#"	{ return token::TOK_SHARP;	}
"!"	{ return token::TOK_NOT;	}
"{"	{ return token::TOK_LEFT_CURLY_BRACKET;	}
"}"	{ return token::TOK_RIGHT_CURLY_BRACKET;	}

"["	{ return token::TOK_LVUONG;	}
"]"	{ return token::TOK_RVUONG;	}

"mov"	{ return token::TOK_MOV; }
"mvn"	{ return token::TOK_MVN; }
"and"	{ return token::TOK_AND; }
"orr"	{ return token::TOK_ORR; }
"eor"	{ return token::TOK_EOR; }
"bic"	{ return token::TOK_BIC; }

"mul"	{ return token::TOK_MUL; }
"mla"	{ return token::TOK_MLA; }
"add"	{ return token::TOK_ADD;}
"add8"	{ return token::TOK_ADD8;}
"add16"	{ return token::TOK_ADD16;}
"sub"	{ return token::TOK_SUB;}
"rsb"	{ return token::TOK_RSB;}
"sub8"	{ return token::TOK_SUB8;}
"sub16"	{ return token::TOK_SUB16;}

"sdiv"	{ return token::TOK_SDIV; }
"udiv"	{ return token::TOK_UDIV; }

"push"  { return token::TOK_PUSH; }
"pop"  { return token::TOK_POP; }

"cmp"  { return token::TOK_CMP; }
"cmn"  { return token::TOK_CMN; }

"asr"	{return token::TOK_ASR;}
"lsl"	{return token::TOK_LSL;}
"lsr"	{return token::TOK_LSR;}
"ror"	{return token::TOK_ROR;}
"rrx"	{return token::TOK_RRX;}


"ldr"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_LDR;
		}
		
"str"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_STR;
		}

"eq"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_EQ;
		}
"ne"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_NE;
		}
"cs"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_CS;
		}
"hs"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_HS;
		}
"cc"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_CC;}
"lo"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_LO;}
"mi"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_MI;
		}
"pl"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_PL;
		}
"vs"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_VS;
		}
"vc"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_VC;
		}
"hi"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_HI;
		}
"ls"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_LS;
		}
"ge"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_GE;
		}
"lt"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_LT;
		}
"gt"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_GT;
		}
"le"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_LE;
		}
"al"	{
			yylval->stringValue = new string (yytext);
			return token:: TOK_AL;
		}
    
    
    
    
"sl"	{//r10
			yylval->stringValue = new string ("r10");
			return token:: TOK_REGISTER;
		}
    
"fp"	{//r11
			yylval->stringValue = new string ("r11");
			return token:: TOK_REGISTER;
		}
 
"ip"	{//r12
			yylval->stringValue = new string ("r12");
			return token:: TOK_REGISTER;
		}
    
"sp"	{//r13
			yylval->stringValue = new string ("r13");
			return token:: TOK_REGISTER;
		}
    
"lr"	{//r14
			yylval->stringValue = new string ("r14");
			return token:: TOK_REGISTER;
		}
   
"pc"	{//r15
			yylval->stringValue = new string ("r15");
			return token:: TOK_REGISTER;
		}

"b"	{return token::TOK_B_OR_BYTE_SUFFIX;}
"bl"	{return token::TOK_BL;}
"bx"	{return token::TOK_BX;}

[\ ]*";"[^\n]*  { return token::TOK_COMMENT; }
 
   
 /*	{return token::* Spaces and end of lines */
[ \t]+ { yylloc->lines(yyleng); yylloc->step(); }
[\n]+  { yylloc->lines(yyleng); yylloc->step(); return token::TOK_EOL; }

 /* Integer values */
{decvalue} {              
		    yylval->intValue = atoi(yytext);
			return token::TOK_INTEGER;
            }

"0x"{hexvalue}  {              
		    yylval->intValue = xtoi(yytext);
			return token::TOK_INTEGER;
            }            
         

 /* Registers */
 


"r"[0-9]+ {
			yylval->stringValue = new string (yytext) ;
			return token::TOK_REGISTER;
	 }
 	 
	 
	 
"%"{varname} {
                yylval->stringValue = new string (yytext + 1);
	        return token::TOK_REGISTER;
             }

 /* Anything else is probable an error */
.  {
     char tmp[2] = { yytext[0], 0 };
     yylval->stringValue = new string (tmp);
     return token::TOK_INVALID;
   }

%% /***** Lexer subroutines *****/

/* Convert a string coded in hexadecimal into a 'long' */
static long xtoi(char *xstr)
{
  long result;
  std::stringstream ss;

  ss << std::hex << xstr;
  ss >> result;

  return result;
}

bool arm_scanner_open(const string &instr)
{
  return yy_scan_string (instr.c_str ());
}

void
arm_scanner_close()
{
  yy_delete_buffer (YY_CURRENT_BUFFER);
}

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

#include "sparc_parser.hh"

#define YY_DECL					 \
  sparc::parser::token_type			 \
    yylex(sparc::parser::semantic_type *yylval, \
	  sparc::parser::location_type *yylloc)

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
using namespace sparc;

typedef parser::token token;


%}

 /* Flex efficiency tuning */
%option 7bit noyywrap nounput batch full align
%option prefix="sparc_"

 /* Getting the scanner to share with other architectures */
 // %option reentrant
 // %option bison-bridge
 // %option prefix="sparc_"

 /* Custom macros */
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
  * _ = default (no postfix given) a word size in the current architecture.
  */


%% /***** Lexer rules *****/

%{
  /* Reset location at the beginning of yylex() */
  yylloc->step();
%}

"(bad)"            { return token::TOK_BAD; }

"," { return token::TOK_COMMA;     }
":" { return token::TOK_COLON; }
"(" { return token::TOK_LPAR;      }
")" { return token::TOK_RPAR;      }
"+" { return token::TOK_PLUS;      }
"-" { return token::TOK_MINUS;     }
"*" { return token::TOK_STAR;      }
"$" { return token::TOK_DOLLAR;    }

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

 /* Registers */
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

bool sparc_scanner_open(const string &instr)
{
  return yy_scan_string (instr.c_str ());
}

void sparc_scanner_close()
{
  yy_delete_buffer (YY_CURRENT_BUFFER);
}

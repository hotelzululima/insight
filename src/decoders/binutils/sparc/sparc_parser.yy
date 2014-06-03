%code requires {		  /*  -*- C++ -*- */
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

#include <map>
#include <string>
#include <stack>

#include <kernel/Architecture.hh>
#include <kernel/Microcode.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>

/* TODO: Parser state should be defined once for all at a higher
 * level. Not here. Indeed, every architecture parser will have the
 * same kind of internal state anyway, so its definition should be
 * shared by all the parsers. */
namespace sparc {
  typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;
  struct parser_data
  {
    typedef enum {
#define SPARC_CC(id,f) SPARC_CC_ ## id,
#include "decoders/binutils/sparc/sparc_cc.def"
#undef SPARC_CC
      NB_CC
    } condition_code_t;

    parser_data (MicrocodeArchitecture *arch, Microcode *out,
		 const std::string &inst, address_t start,
		 address_t next);
    ~parser_data();

    LValue *get_flag (const char *flagname) const;
    LValue *get_tmp_register (const char *id, int size) const;
    LValue *get_register (const char *regname) const;
    bool is_segment_register (const Expr *expr);

    Expr *get_memory_reference (Expr *section, int disp, Expr *bis) const;

    bool has_prefix;
    std::string instruction;
    MicrocodeAddress start_ma;
    MicrocodeAddress next_ma;
    Microcode *mc;
    bool lock;
    bool data16;
    bool data_size;
    bool addr16;
    bool addr_size;
    const char *data_segment;
    const char *code_segment;
    const char *stack_segment;
    MicrocodeArchitecture *arch;
    Expr *condition_codes[NB_CC];
    std::unordered_set<const RegisterDesc *,
			    RegisterDesc::Hash> segment_registers;
  };
}
}

 /* Bison specific options */
%skeleton "lalr1.cc"
%language "c++"
%require "2.4"
%defines
%define namespace "sparc"

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
};

%code {
using namespace std;
using namespace sparc;

#include "decoders/binutils/sparc/sparc_translate.hh"

#undef yylex
#define yylex sparc_lex

#define YY_DECL					\
 sparc::parser::token_type			\
   yylex(sparc::parser::semantic_type* yylval,	\
	 sparc::parser::location_type* yylloc)

 YY_DECL;

#include "sparc_scanner.hh"

#define push_mc(data) do { (data).mc.push (new Microcode ()); } while (0)

}

%token TOK_LPAR TOK_RPAR
%token TOK_COMMA TOK_COLON
%token TOK_PLUS TOK_MINUS TOK_STAR TOK_DOLLAR
%token <stringValue>  TOK_INVALID
%token                TOK_EOF      0 "end of buffer (EOF)"
%token                TOK_EOL        "end of line (EOL)"

%token <stringValue>  TOK_REGISTER   "register (REGISTER)"

%token <intValue>     TOK_INTEGER    "integer value (INTEGER)"

%token  TOK_BAD              "(bad)"

%type <expr> operand register section memory_reference base_index_scale

%type <intValue> integer immediate

%printer    { debug_stream() << $$; } <intValue>

%printer    { debug_stream() << *$$; } TOK_REGISTER
%destructor { delete $$; } TOK_REGISTER

%% /***** Parser rules *****/

start: instruction;

operand:
  immediate { $$ = Constant::create ($1, 0, 32); }
| register { $$ = $1; }
| register TOK_LPAR integer TOK_RPAR
  { throw std::runtime_error ("unsupported register"); }
| memory_reference { $$ = $1; }
| TOK_STAR memory_reference {
  $$ = MemCell::create ($2, 0, data.arch->get_word_size ());
}
| TOK_STAR register {
  $$ = MemCell::create ($2, 0, data.arch->get_word_size ());
  }
;

memory_reference:
  section integer base_index_scale
{ $$ = data.get_memory_reference ($1, $2, $3); }
| section integer
{ $$ = data.get_memory_reference ($1, $2, NULL); }
| section base_index_scale
{ $$ = data.get_memory_reference ($1, 0, $2); }

section :
  register TOK_COLON { $$ = $1; }
| /* empty */        { $$ = NULL; }
;

base_index_scale :
  TOK_LPAR register TOK_COMMA register TOK_COMMA TOK_INTEGER TOK_RPAR
{ $$ = BinaryApp::create (BV_OP_ADD, $2,
			  BinaryApp::create (BV_OP_MUL_U, $4, $6)); }
| TOK_LPAR register TOK_COMMA register TOK_RPAR
{ $$ = BinaryApp::create (BV_OP_ADD, $2, $4); }
| TOK_LPAR register TOK_RPAR
{ $$ = $2; }
| TOK_LPAR TOK_COMMA register TOK_COMMA TOK_INTEGER TOK_RPAR
{ $$ = BinaryApp::create (BV_OP_MUL_U, $3, $5); }

| TOK_LPAR TOK_COMMA TOK_INTEGER TOK_RPAR
{ $$ = NULL; }
;

register :
TOK_REGISTER
{
  $$ = data.get_register ($1->c_str ());
  if ($$ == NULL)
    {
      error (yylloc, ": error: unknown register " + *$1);
      delete $1;
      YYERROR;
    }
  else
    {
      delete $1;
    }
}
 ;

immediate:
  TOK_DOLLAR integer { $$ = $2; }
;

integer :
  TOK_PLUS  TOK_INTEGER { $$ = $2; }
| TOK_MINUS TOK_INTEGER { $$ = -$2; }
| TOK_INTEGER           { $$ = $1; }
;

instruction:
TOK_BAD { }
;

%% /***** Parser subroutines *****/

void parser::error(const parser::location_type &loc,
		   const string &msg)
{
  cerr << loc << ":" << msg << endl;
}


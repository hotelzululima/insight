%code requires {
/*  -*- C++ -*- */
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

#include <map>
#include <string>
#include <stack>
#include <kernel/Expressions.hh>

namespace ExprParser {
  struct ClientData;
 };
};

%code provides {
  namespace ExprParser {
    extern Expr *
    parse_Expr (const MicrocodeArchitecture *arch, const std::string &input);
  };
 }

%define namespace "ExprParser"
%define parser_class_name "Parser"
%language "c++"
%defines
%start start

 /* Parsing context */
%parse-param { ClientData &data }
%lex-param   { ClientData &data }

%locations
%initial-action
{
  /* Initialize the initial location */
  @$.begin.filename = @$.end.filename = &data.input;
};

%debug
%error-verbose

 /* Symbols */
%union
{
  struct { int offset; int size; } bvSpec;
  long      intValue;
  std::string   *stringValue;
  Expr     *expr;
  Variable     *var;
  UnaryOp   uOp;
  BinaryOp  bOp;
  BinaryOp  cmpOp;
  TernaryOp tOp;
};

%code {
#include "ExprParser.hh"
#include <kernel/expressions/ExprLexer.hh>

using namespace std;
using namespace ExprParser;

#undef yylex
#define yylex ExprParser_lex
}

%token TOK_LPAR TOK_RPAR
%token TOK_LBRACE TOK_RBRACE
%token TOK_LBRACKET TOK_RBRACKET
%token TOK_SEMICOLON TOK_PERCENT
%token TOK_EXIST TOK_FORALL

%token <uOp> TOK_UNARY_OP
%token <bOp> TOK_BINARY_OP
%token <cmpOp> TOK_COMPARE_OP
%token <tOp> TOK_TERNARY_OP
%token <stringValue>  TOK_STRING
%token <stringValue>  TOK_INVALID
%token                TOK_EOF      0 "end of buffer (EOF)"
%token <intValue>     TOK_INTEGER    "integer value (INTEGER)"

%type <expr> start constant expr atom lvalue
%type <var> variable 
%type <bvSpec> bitvector_spec

%% /***** Parser rules *****/

start : 
  expr 
  { data.result = $1; }
;

bitvector_spec :
 TOK_LBRACE TOK_INTEGER TOK_SEMICOLON TOK_INTEGER TOK_RBRACE 
 { $$.offset = $2; $$.size = $4; }
;

expr :
  TOK_LPAR TOK_UNARY_OP expr TOK_RPAR 
  { $$ = UnaryApp::create ($2, $3, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_UNARY_OP expr TOK_RPAR bitvector_spec
  { $$ = UnaryApp::create ($2, $3, $5.offset, $5.size); }
| TOK_LPAR TOK_BINARY_OP expr expr TOK_RPAR bitvector_spec
  { $$ = BinaryApp::create ($2, $3, $4, $6.offset, $6.size); }
| TOK_LPAR TOK_COMPARE_OP expr expr TOK_RPAR 
  { $$ = BinaryApp::create ($2, $3, $4, 0, 1); }
| TOK_LPAR TOK_COMPARE_OP expr expr TOK_RPAR bitvector_spec
  { $$ = BinaryApp::create ($2, $3, $4, $6.offset, $6.size); }
| TOK_LPAR TOK_TERNARY_OP expr expr expr TOK_RPAR bitvector_spec
  { $$ = TernaryApp::create ($2, $3, $4, $5, $7.offset, $7.size); }
| TOK_LPAR TOK_EXIST variable expr TOK_RPAR
  { $$ = QuantifiedExpr::createExist ($3, $4); }
| TOK_LPAR TOK_FORALL variable expr TOK_RPAR
  { $$ = QuantifiedExpr::createForall ($3, $4); }
| TOK_LPAR expr TOK_RPAR bitvector_spec
  { $$ = $2->extract_bit_vector ($4.offset, $4.size); $2->deref (); }
| atom bitvector_spec
  { $$ = $1->extract_bit_vector ($2.offset, $2.size); $1->deref ();}
| atom
  { $$ = $1; }
;

atom :
  constant
  { $$ = $1; }
| variable
  { $$ = $1; }
| lvalue
  { $$ = $1; }
;

constant :
  TOK_INTEGER  
  { $$ = Constant::create ($1, 0, BV_DEFAULT_SIZE); }
;

variable : 
  TOK_STRING 
  { $$ = Variable::create (*($1)); delete $1; }
;

lvalue:
  TOK_LBRACKET expr TOK_RBRACKET 
  { $$ = MemCell::create ($2, 0, BV_DEFAULT_SIZE); }
| TOK_PERCENT TOK_STRING 
  { 
    try {
      const RegisterDesc *reg = data.arch->get_register (*$2); 
      int offset = reg->get_window_offset ();
      int size = reg->get_window_size ();
      if (reg->is_alias ())
	reg = data.arch->get_register (reg->get_label ());
      $$ = RegisterExpr::create (reg, offset, size);
    } catch(RegisterDescNotFound &) {
      Log::errorln ("unknown register '" + *$2 + "'"); 
      YYERROR;      
    }
    delete $2;
  }
;

%% /***** Parser subroutines *****/

# include <cassert>

void 
Parser::error(const Parser::location_type &loc, const string &msg)
{
  ostringstream oss;

  oss << loc << ":" << msg;
  Log::errorln (oss.str ());
}

Expr *
Expr::parse (MicrocodeArchitecture *arch, const std::string &input)
{
  ExprParser::ClientData data;

  ExprParser::init_lexer (input);
  data.result = NULL;
  data.arch = arch;
  data.input = input;

  Parser parser (data);
  if (parser.parse () == 0)
    assert (data.result != NULL);
  ExprParser::terminate_lexer ();

  return data.result;
}


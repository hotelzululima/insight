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
  long      intValue;
  std::string   *stringValue;
  Expr     *expr;
  Variable *variable;
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
%token TOK_COMMA TOK_COLON TOK_SEMICOLON TOK_PERCENT
%token TOK_L_AND TOK_L_OR TOK_L_NOT 
%token TOK_EXISTS TOK_FORALL

%token TOK_PLUS TOK_MINUS TOK_STAR TOK_DOLLAR TOK_MUL_S TOK_MUL_U
%token TOK_ADD TOK_SUB TOK_AND TOK_OR  TOK_XOR TOK_LSH 
%token TOK_RSH_S TOK_RSH_U TOK_ROR TOK_ROL TOK_NEG TOK_NOT TOK_EQ TOK_POW 
%token TOK_DIV_S TOK_DIV_U 
%token TOK_LT_U TOK_GT_U TOK_LEQ_U TOK_GEQ_U
%token TOK_LT_S TOK_GT_S TOK_LEQ_S TOK_GEQ_S

%token <stringValue>  TOK_STRING
%token <stringValue>  TOK_INVALID
%token                TOK_EOF      0 "end of buffer (EOF)"
%token <intValue>     TOK_INTEGER    "integer value (INTEGER)"

%type <expr> start formula
%type <expr> constant expr addexpr mulexpr unaryexpr veryatomexpr atomexpr lval
%type <expr> opexpr 
%type <variable> variable 

%% /***** Parser rules *****/

start : 
  formula 
  { data.result = $1; }
;

formula :
  expr 
  { $$ = $1; }
| TOK_LPAR formula TOK_RPAR
  { $$ = $2; }
| formula TOK_L_AND formula 
  { $$ = Expr::createAnd ($1, $3); }
| formula TOK_L_OR formula 
  { $$ = Expr::createOr ($1, $3); }
| TOK_L_NOT formula 
  { $$ = Expr::createNot ((Expr *) $2); }
| TOK_FORALL variable formula 
  { $$ = QuantifiedExpr::createForall ($2, $3); }
| TOK_EXISTS variable formula 
  { $$ = QuantifiedExpr::createExist ($2, $3); }
;

constant :
  TOK_INTEGER  
  { $$ = Constant::create ($1); }
;

variable : 
  TOK_STRING 
  { $$ = Variable::create (*($1)); delete $1; }
;

expr : 
  addexpr 
  { $$ = $1; }
;

addexpr : 
  mulexpr                   
  { $$ = $1; }
| addexpr TOK_PLUS mulexpr 
  { $$ = BinaryApp::create (BV_OP_ADD,$1,$3); }
| addexpr TOK_MINUS mulexpr 
  { $$ = BinaryApp::create (BV_OP_SUB,$1,$3); }
;

mulexpr : 
  unaryexpr
  { $$ = $1; }
| mulexpr TOK_MUL_S unaryexpr
  { $$ = BinaryApp::create (BV_OP_MUL_S,$1,$3); }

| mulexpr TOK_MUL_U unaryexpr
  { $$ = BinaryApp::create (BV_OP_MUL_U,$1,$3); }
;

unaryexpr : 
  atomexpr 
  { $$ = $1; }
| TOK_PLUS atomexpr 
  { $$ = $2; }
| TOK_MINUS atomexpr
  { $$ = UnaryApp::create (BV_OP_NEG, $2); }
;

veryatomexpr :
  constant
  { $$ = $1; }
| variable 
  { $$ = $1; }
| TOK_LPAR expr TOK_RPAR 
  { $$ = $2; }
| lval 
  { $$ = $1; }
| opexpr
  { $$ = $1; }
;

atomexpr : 
  veryatomexpr
  { $$ = $1; }
| veryatomexpr TOK_LBRACE TOK_INTEGER TOK_SEMICOLON TOK_INTEGER TOK_RBRACE 
  {
    $$ = $1->extract_bit_vector ($3, $5);
    $1->deref ();
  }

;

opexpr:
  TOK_LPAR TOK_ADD atomexpr atomexpr TOK_RPAR
  { $$ = BinaryApp::create (BV_OP_ADD,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_SUB atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_SUB,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_MUL_S atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_MUL_S,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_MUL_U atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_MUL_U,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_AND atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_AND,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_OR  atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_OR,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_XOR atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_XOR,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_LSH atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_LSH,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_RSH_U atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_RSH_U,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_RSH_S atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_RSH_S,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_ROR atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_ROR,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_ROL atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_ROL,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_NEG atomexpr TOK_RPAR 
  { $$ = UnaryApp::create (BV_OP_NEG,$3, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_NOT atomexpr TOK_RPAR 
  { $$ = UnaryApp::create (BV_OP_NOT,$3, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_EQ atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_EQ,$3,$4, 0, 1); }

| TOK_LPAR TOK_LEQ_S atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_LEQ_S,$3,$4, 0, 1); }
| TOK_LPAR TOK_GEQ_S atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_GEQ_S,$3,$4, 0, 1); }
| TOK_LPAR TOK_GT_S atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_GT_S,$3,$4, 0, 1); }
| TOK_LPAR TOK_LT_S atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_LT_S,$3,$4, 0, 1); }

| TOK_LPAR TOK_LEQ_U atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_LEQ_U,$3,$4, 0, 1); }
| TOK_LPAR TOK_GEQ_U atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_GEQ_U,$3,$4, 0, 1); }
| TOK_LPAR TOK_GT_U atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_GT_U,$3,$4, 0, 1); }
| TOK_LPAR TOK_LT_U atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_LT_U,$3,$4, 0, 1); }

| TOK_LPAR TOK_POW atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_POW,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_DIV_S atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_DIV_S,$3,$4, 0, $3->get_bv_size ()); }
| TOK_LPAR TOK_DIV_U atomexpr atomexpr TOK_RPAR 
  { $$ = BinaryApp::create (BV_OP_DIV_U,$3,$4, 0, $3->get_bv_size ()); }
;

lval:
  TOK_LBRACKET expr TOK_RBRACKET 
  { $$ = MemCell::create ($2); }
| TOK_LBRACKET TOK_STRING TOK_COLON expr TOK_RBRACKET 
  { $$ = MemCell::create ($4, *$2 ); delete $2; }
/*| TOK_PERCENT TOK_INTEGER
  { $$ = RegisterExpr::create ($2); }*/
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
/*| lval TOK_LBRACE TOK_INTEGER TOK_SEMICOLON TOK_INTEGER TOK_RBRACE
  {
    $$ = (LValue *) $1->extract_bit_vector ($3,$5);
    $1->deref ();
  }*/
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


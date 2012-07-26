%code requires {		  /*  -*- C++ -*- */
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

#include <kernel/Microcode.hh>

namespace arm {
  typedef std::vector<MicrocodeNode *> MicrocodeNodeVector;
  struct parser_data
  {
    parser_data ();

    LValue *get_flag (const char *flagname) const;
    LValue *get_register (const char *regname) const;
    LValue *get_adjacent_register (const Expr *reg) const;
    Expr* arm_compute_cond_expr(std::string cond_code);

    std::map<std::string, std::string> register_pairs;
    MicrocodeArchitecture *arch;
    std::string instruction;
    Microcode *mc;
    MicrocodeAddress start_ma;
    MicrocodeAddress next_ma;
    mutable std::map<std::string, LValue *> registers;
  };
}
}

 /* Bison specific options */
%skeleton "lalr1.cc"
%language "c++"
%require "2.4"
%defines
%define namespace "arm"

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
  long         intValue;
  std::string *stringValue;
  bool 		   boolValue;
  class Expr  *expr;
  std::list<RegisterExpr*> *reg_list;
};

%code {
using namespace std;
using namespace arm;

#include "decoders/binutils/arm/arm_translate.hh"

#undef yylex
#define yylex arm_lex

#define YY_DECL				      \
  arm::parser::token_type		      \
    yylex(arm::parser::semantic_type* yylval, \
          arm::parser::location_type* yylloc)

YY_DECL;

#include "arm_scanner.hh"
}

%token  TOK_BL  "BL"
%token  TOK_BX  "BX"

%token TOK_ADD "ADD"
%token TOK_ADD8 "ADD8"
%token TOK_ADD16 "ADD16"
%token TOK_SUB "SUB"
%token TOK_RSB "RSB"
%token TOK_SUB8 "SUB8"
%token TOK_SUB16 "SUB16"
%token TOK_MOV "MOV"
%token TOK_MVN "MVN"
%token TOK_AND "AND"
%token TOK_ORR "ORR"
%token TOK_EOR "EOR"
%token TOK_BIC "BIC"

%token TOK_COMMENT "COMMENT TOKEN"

%token TOK_MUL "MUL"
%token TOK_MLA "MLA"
%token TOK_PLUS "+"
%token TOK_MINUS "-"

%token TOK_SDIV "SDIV"
%token TOK_UDIV "UDIV"

%token TOK_PUSH "PUSH"
%token TOK_POP "POP"
%token TOK_CMP "CMP"
%token TOK_CMN "CMN"

%token TOK_COMMA
%token TOK_COLON
%token TOK_SEMICOLON
%token TOK_LPAR
%token TOK_RPAR
%token TOK_STAR
%token TOK_DOLLAR

%token TOK_LVUONG
%token TOK_RVUONG

%token TOK_ASR
%token TOK_LSL
%token TOK_LSR
%token TOK_ROR
%token TOK_RRX


%token <stringValue> TOK_EQ
%token <stringValue> TOK_NE
%token <stringValue>  TOK_CS
%token <stringValue>  TOK_HS
%token <stringValue>  TOK_CC
%token <stringValue>  TOK_LO
%token <stringValue>  TOK_MI
%token <stringValue>  TOK_PL
%token <stringValue>  TOK_VS
%token <stringValue>  TOK_VC
%token <stringValue>  TOK_HI
%token <stringValue>  TOK_LS
%token <stringValue>  TOK_GE
%token <stringValue>  TOK_LT
%token <stringValue>  TOK_GT
%token <stringValue>  TOK_LE
%token <stringValue>  TOK_AL

%token <boolValue> TOK_B_OR_BYTE_SUFFIX
%token <boolValue> TOK_PROCESSOR_MODE_SUFFIX
%token <boolValue> TOK_S_UPDATE_COND_FLAG_SUFFIX_OR_PREFIX
%token <boolValue> TOK_DOUBLE_WORD_SUFFIX
%token <boolValue> TOK_HALF_WORD_SUFFIX


%token <stringValue> TOK_PREFIX_FOR_PARALLEL_INS_Q
%token <stringValue> TOK_PREFIX_FOR_PARALLEL_INS_SH
%token <stringValue> TOK_PREFIX_FOR_PARALLEL_INS_U
%token <stringValue> TOK_PREFIX_FOR_PARALLEL_INS_UQ
%token <stringValue> TOK_PREFIX_FOR_PARALLEL_INS_UH

%token TOK_LDR
%token TOK_STR

%token <stringValue>  TOK_INVALID
%token                TOK_EOF      0 "end of buffer (EOF)"
%token                TOK_EOL        "end of line (EOL)"


%token<intValue> TOK_INTEGER  "INTEGER "
%token<stringValue> TOK_REGISTER
%token TOK_SHARP TOK_LEFT_CURLY_BRACKET TOK_RIGHT_CURLY_BRACKET
%token TOK_NOT

 /*%type <expr> memory_reference postIndexed_offset */
%type <expr> register  zero_offset preIndexed_offset   flexOffset operand2 shifted_register multiplyInstr immediate
%type <reg_list> register_list

%type <intValue> integer  
%type <stringValue> cond prefix

%type <boolValue> B_suffix T_suffix D_suffix H_suffix S_suffix NOT_suffix 

%printer    { debug_stream() << $$; } <intValue>

%printer    { debug_stream() << *$$; } TOK_REGISTER
%destructor { delete $$; } TOK_REGISTER

%% /***** Parser rules *****/

start: 
  instruction{
  }
|
  instruction TOK_COMMENT{
    }
|
  TOK_COMMENT
;

 
instruction: 
	accessMemoryInstr{
	}

|
	generalDataProcessInstr{
	}
	
|
	multiplyInstr
  
|
	branchesInstr
;


accessMemoryInstr:

  TOK_LDR D_suffix H_suffix B_suffix T_suffix cond register TOK_COMMA zero_offset{
		arm_translate<ARM_TOKEN(LDR)> (data, $2, $3, $4, $5, $6, $7, $9);	//bool, bool, bool, bool, string, expr, expr
	}  
|
	TOK_LDR D_suffix H_suffix B_suffix T_suffix cond register TOK_COMMA preIndexed_offset NOT_suffix{//T_suffix to resolve conflicts
    arm_translate<ARM_TOKEN(LDR)> (data, $2, $3, $4, $5, $6, $7, $9, $10);	//bool,bool, bool, bool, string, expr, expr, bool
    
	}  
|
	TOK_LDR D_suffix H_suffix B_suffix T_suffix cond register TOK_COMMA zero_offset TOK_COMMA flexOffset{
  	arm_translate<ARM_TOKEN(LDR)> (data, $2, $3, $4, $5, $6, $7, $9, $11);	//bool,bool, bool, bool, string, expr, expr, expr
  }
|
	TOK_STR D_suffix H_suffix B_suffix T_suffix cond register TOK_COMMA zero_offset{
		arm_translate<ARM_TOKEN(STR)> (data, $2, $3, $4, $5, $6, $7, $9);	//bool, bool, bool, bool, string, expr, expr
	}  
|
	TOK_STR D_suffix H_suffix B_suffix T_suffix cond register TOK_COMMA preIndexed_offset NOT_suffix{//T_suffix to resolve conflicts
    arm_translate<ARM_TOKEN(STR)> (data, $2, $3, $4, $5, $6, $7, $9, $10);	//bool,bool, bool, bool, string, expr, expr, bool
    
	}  
|
	TOK_STR D_suffix H_suffix B_suffix T_suffix cond register TOK_COMMA zero_offset TOK_COMMA flexOffset{
		arm_translate<ARM_TOKEN(STR)> (data, $2, $3, $4, $5, $6, $7, $9, $11);	//bool,bool, bool, bool, string, expr, expr, expr
	}	
;


cond:
	{
		$$ = new string ("");
	}
|
	TOK_EQ{
		$$ = $1;
	}
|
	TOK_NE{
		$$ = $1;
	}
|
	TOK_CS{
		$$ = $1;
	}
|
	TOK_HS{
		$$ = $1;
	}
|
	TOK_CC{
		$$ = $1;
	}
|
	TOK_LO{
		$$ = $1;
	}
|
	TOK_MI{
		$$ = $1;
	}
|
	TOK_PL{
		$$ = $1;
	}
|
	TOK_VS{
		$$ = $1;
	}
|
	TOK_VC{
		$$ = $1;
	}
|
	TOK_HI{
		$$ = $1;
	}
|
	TOK_LS{
		$$ = $1;
	}
|
	TOK_GE{
		$$ = $1;
	}
|
	TOK_LT{
		$$ = $1;
	}
|
	TOK_GT{
		$$ = $1;
	}
|
	TOK_LE{
		$$ = $1;
	}
|
	TOK_AL{
		$$ = $1;
	}
;	

T_suffix:
	{
		$$ = false;
	}
|
	TOK_PROCESSOR_MODE_SUFFIX{
		$$ = true;
	}
;	

D_suffix:
	{
		$$ = false;
	}
|
	TOK_DOUBLE_WORD_SUFFIX{
		$$ = true;
	}
;	

H_suffix:
  {
    $$ = false;
  }
|
  TOK_HALF_WORD_SUFFIX{
    $$ = true;
  }
;  

B_suffix:
	{
		$$ = false;
	}
|
	TOK_B_OR_BYTE_SUFFIX{
		$$ = true;
	}
;

NOT_suffix:
	{
		$$ = false;
	}
|
	TOK_NOT{
		$$ = true;
	}
;

/*
memory_reference:
	zero_offset {
  $$ = $1;
  }
|
	preIndexed_offset{
    $$ = $1;
  }
|
	postIndexed_offset{
    $$ = $1;
  }
;
*/

zero_offset:
  TOK_LVUONG register TOK_RVUONG{
		$$ = MemCell::create($2);
	}
;

preIndexed_offset:
  TOK_LVUONG register TOK_COMMA flexOffset TOK_RVUONG{
		$$ = MemCell::create( BinaryApp::create (ADD, $2, $4));
	} 
;  

/*
postIndexed_offset:
  TOK_LVUONG register TOK_RVUONG TOK_COMMA flexOffset {
		$$ = MemCell::create( BinaryApp::create (ADD, $2, $5));
	} 
;  
*/

shifted_register:
	register{
		$$ = $1;
	}
|
	register TOK_COMMA TOK_ASR immediate{
		//XXX: need to distinguish between ASR and LSR
		$$ = BinaryApp::create(RSH_S, $1, $4);
	}
|
	register TOK_COMMA TOK_LSL immediate{
		$$ = BinaryApp::create(LSH, $1, $4);
	}
|
	register TOK_COMMA TOK_LSR immediate{
		$$ = BinaryApp::create(RSH_S, $1, $4);
	}	
|
	register TOK_COMMA TOK_ROR immediate{
		$$ = BinaryApp::create(ROR, $1, $4);
	}	
|
	register TOK_COMMA TOK_RRX{
		//XXX: change this -> RRX
		$$ = BinaryApp::create(ROR, $1, Constant::create(1));
	}	
  
|
	register TOK_COMMA TOK_ASR register{
		//XXX: need to distinguish between ASR and LSR
		$$ = BinaryApp::create(RSH_S, $1, $4);
	}
|
	register TOK_COMMA TOK_LSL register{
		$$ = BinaryApp::create(LSH, $1, $4);
	}
|
	register TOK_COMMA TOK_LSR register{
		$$ = BinaryApp::create(RSH_S, $1, $4);
	}	
|
	register TOK_COMMA TOK_ROR register{
		$$ = BinaryApp::create(ROR, $1, $4);
	}	  
;	
	

flexOffset:
	TOK_SHARP integer{
		$$ = Constant::create($2);
	}
|
	shifted_register{
		$$ = $1;
	}
|	
	TOK_MINUS shifted_register{
		$$ = UnaryApp::create(NEG, $2);
	}
;	

generalDataProcessInstr:
			
	TOK_ADD S_suffix cond  register TOK_COMMA register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(ADD)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
|
	prefix TOK_ADD8 cond register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(ADD8)> (data, $1, $3, $4, $6, $8);	//string, string,expr, expr, expr
	}
|
	prefix TOK_ADD16 cond register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(ADD16)> (data, $1, $3, $4, $6, $8);	//string, string, expr, expr, expr
	}
|
	
	TOK_SUB S_suffix cond register TOK_COMMA register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(SUB)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
  
|
	
	TOK_RSB S_suffix cond register TOK_COMMA register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(RSB)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
|
	prefix TOK_SUB8 cond register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(SUB8)> (data, $1, $3, $4, $6, $8);	//string, string,expr, expr, expr
	}
|
	prefix TOK_SUB16 cond register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(SUB16)> (data, $1, $3, $4, $6, $8);	//string, string,expr, expr, expr
	}
	
|
	TOK_MOV S_suffix cond register  TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(MOV)> (data, $2, $3, $4, $6);	//bool, string, expr, expr
	}
|
	TOK_MVN S_suffix cond register  TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(MVN)> (data, $2, $3, $4, $6);	//bool, string, expr, expr
	}
|
	TOK_AND S_suffix cond register TOK_COMMA register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(AND)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
|
	TOK_ORR S_suffix cond register TOK_COMMA register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(ORR)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
|
	TOK_EOR S_suffix cond register TOK_COMMA register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(EOR)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
|
	TOK_BIC S_suffix cond register TOK_COMMA register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(BIC)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
|
	TOK_PUSH TOK_LEFT_CURLY_BRACKET register_list TOK_RIGHT_CURLY_BRACKET{
		arm_translate<ARM_TOKEN(PUSH)> (data, $3);	//std::list
	}
|
	TOK_POP TOK_LEFT_CURLY_BRACKET register_list TOK_RIGHT_CURLY_BRACKET{
		arm_translate<ARM_TOKEN(POP)> (data, $3);	//std::list
	}  
|
	TOK_CMP cond register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(CMP)> (data, $2, $3, $5);	//string, expr, expr
	}
|
	TOK_CMN cond register TOK_COMMA operand2{
		arm_translate<ARM_TOKEN(CMN)> (data, $2, $3, $5);	//string, expr, expr
	}  
;

S_suffix:
	{
		$$ = false;
	}
|
	TOK_S_UPDATE_COND_FLAG_SUFFIX_OR_PREFIX{
		$$ = true;
	}
;

prefix:
	{
		//XXX: not supported yet
		$$ = new string ("");
	}
|
	TOK_S_UPDATE_COND_FLAG_SUFFIX_OR_PREFIX
	{
		//XXX: not supported yet
		$$ = new string ("");
	}
|
	TOK_PREFIX_FOR_PARALLEL_INS_Q
	{
		//XXX: not supported yet
		$$ = new string ("");
	}
|
	TOK_PREFIX_FOR_PARALLEL_INS_SH
	{
		//XXX: not supported yet
		$$ = new string ("");
	}
|
	TOK_PREFIX_FOR_PARALLEL_INS_U
	{
		//XXX: not supported yet
		$$ = new string ("");
	}
|
	TOK_PREFIX_FOR_PARALLEL_INS_UQ
	{
		//XXX: not supported yet
		$$ = new string ("");
	}
|
	TOK_PREFIX_FOR_PARALLEL_INS_UH
	{
		//XXX: not supported yet
		$$ = new string ("");
	}
;



operand2:
	immediate{
		$$ = $1;
	}
|
	shifted_register{
		$$ = $1;
	}
;



multiplyInstr:
	TOK_MUL S_suffix cond register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(MUL)> (data, $2, $3, $4, $6, $8);	//bool, string, expr, expr, expr
	}
|
	TOK_MLA S_suffix cond register TOK_COMMA register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(MUL)> (data, $2, $3, $4, $6, $8, $10);	//bool, string, expr, expr, expr, expr
  }
|
	TOK_UDIV register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(UDIV)> (data, $2, $4, $6);	//expr, expr, expr
  }
|
	TOK_SDIV register TOK_COMMA register TOK_COMMA register{
		arm_translate<ARM_TOKEN(SDIV)> (data, $2, $4, $6);	//expr, expr, expr    
  }
;
	
branchesInstr:

  TOK_B_OR_BYTE_SUFFIX cond TOK_INTEGER{
    arm_translate<ARM_TOKEN(B_OR_BYTE_SUFFIX)> (data, $2, $3);	//string, int
  }
|
  TOK_BL cond TOK_INTEGER{
    arm_translate<ARM_TOKEN(BL)> (data, $2, $3);	//string, int
  }
|
  TOK_BX cond register{
    arm_translate<ARM_TOKEN(BX)> (data, $2, $3);	//string, int
  }  
;

integer:
	TOK_PLUS TOK_INTEGER {$$ = $2; }
|
	TOK_MINUS TOK_INTEGER {$$ = -$2;}
|
	TOK_INTEGER 	{$$ = $1;}
;	

register:
	TOK_REGISTER {
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
 
register_list:
  register{
    std::list<RegisterExpr *> *tmp = new list<RegisterExpr *>();
    tmp->push_front((RegisterExpr *) $1);
    $$ = tmp;
  }
|
  register TOK_COMMA register_list{
    $3->push_front((RegisterExpr *) $1);
    $$ = $3;
  }
;

immediate:
  TOK_SHARP integer { $$ = Constant::create($2); }
;


%% /***** Parser subroutines *****/

void parser::error(const parser::location_type &loc,
		   const string &msg)
{
  cerr << loc << ":" << msg << endl;
}

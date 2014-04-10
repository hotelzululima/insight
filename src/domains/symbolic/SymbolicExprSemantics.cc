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

#include <kernel/expressions/exprutils.hh>
#include <domains/symbolic/SymbolicExprSemantics.hh>

#define TER_OP_DEF(op)							\
  template<> SymbolicValue						\
  SymbolicExprSemantics::						\
  op ## _eval (SymbolicValue v1, SymbolicValue v2, SymbolicValue v3,	\
	       int offset, int size) {					\
    Expr *tmp = TernaryApp::create (op,					\
				    v1.get_Expr ()->ref (),		\
				    v2.get_Expr ()->ref (),		\
				    v3.get_Expr ()->ref (),		\
				    offset,				\
				    size);				\
    exprutils::simplify (&tmp);						\
    SymbolicValue result (tmp);						\
    tmp->deref ();							\
    return result;							\
  } 

#define BIN_OP_DEF(op)							\
  template<> SymbolicValue						\
  SymbolicExprSemantics::						\
  op ## _eval (SymbolicValue v1, SymbolicValue v2, int offset, int size) { \
    Expr *tmp = BinaryApp::create (op,					\
				   v1.get_Expr ()->ref (),		\
				   v2.get_Expr ()->ref (),		\
				   offset, size);			\
    exprutils::simplify (&tmp);						\
    SymbolicValue result (tmp);						\
    tmp->deref ();							\
    return result;							\
  } 

#define UN_OP_DEF(op)							\
  template<> SymbolicValue						\
  SymbolicExprSemantics::						\
  op ## _eval (SymbolicValue v, int offset, int size) {			\
    Expr *tmp = UnaryApp::create (op, v.get_Expr ()->ref (),		\
				  offset, size);			\
    exprutils::simplify (&tmp);						\
    SymbolicValue result (tmp);						\
    tmp->deref ();							\
    return result;							\
  } 

/*****************************************************************************/

BIN_OP_DEF(BV_OP_ADD)
BIN_OP_DEF(BV_OP_SUB)
BIN_OP_DEF(BV_OP_AND)
BIN_OP_DEF(BV_OP_OR)
BIN_OP_DEF(BV_OP_XOR)
BIN_OP_DEF(BV_OP_LSH)
BIN_OP_DEF(BV_OP_NEQ)
BIN_OP_DEF(BV_OP_EQ)
BIN_OP_DEF(BV_OP_MODULO)
BIN_OP_DEF(BV_OP_MUL_S)
BIN_OP_DEF(BV_OP_MUL_U)
BIN_OP_DEF(BV_OP_RSH_S)
BIN_OP_DEF(BV_OP_RSH_U)
BIN_OP_DEF(BV_OP_LT_S)
BIN_OP_DEF(BV_OP_LT_U)
BIN_OP_DEF(BV_OP_LEQ_S)
BIN_OP_DEF(BV_OP_LEQ_U)
BIN_OP_DEF(BV_OP_GT_S)
BIN_OP_DEF(BV_OP_GT_U)
BIN_OP_DEF(BV_OP_GEQ_S)
BIN_OP_DEF(BV_OP_GEQ_U)
BIN_OP_DEF(BV_OP_POW)
BIN_OP_DEF(BV_OP_DIV_U)
BIN_OP_DEF(BV_OP_DIV_S)
BIN_OP_DEF(BV_OP_ROL)
BIN_OP_DEF(BV_OP_ROR)
BIN_OP_DEF(BV_OP_CONCAT)
BIN_OP_DEF(BV_OP_EXTEND_S)
BIN_OP_DEF(BV_OP_EXTEND_U)

UN_OP_DEF(BV_OP_NEG)
UN_OP_DEF(BV_OP_NOT)

template<> SymbolicValue						
SymbolicExprSemantics::BV_OP_EXTRACT_eval (SymbolicValue v1, SymbolicValue v2, 
					   SymbolicValue v3, 
					   int offset, int size) 
{ 
  const Constant *off = dynamic_cast<const Constant *> (v2.get_Expr ());
  const Constant *sz = dynamic_cast<const Constant *> (v3.get_Expr ());

  assert (off != NULL && sz != NULL);

  Expr *tmp = Expr::createExtract (v1.get_Expr ()->ref (), off->get_val (),
				   sz->get_val ());
  if (offset != 0 || size != sz->get_val ())
    tmp = Expr::createExtract (tmp, offset, size);

  exprutils::simplify (&tmp); 				
  SymbolicValue result (tmp); 
  tmp->deref (); 

  return result; 
} 

template<> SymbolicValue
SymbolicExprSemantics::extract_eval(SymbolicValue v,  int off, int size) 
{
  return expr_semantics_extract_eval<SymbolicValue, 
				     SymbolicExprSemantics>(v,off, size);
}
template<> SymbolicValue
SymbolicExprSemantics::embed_eval(SymbolicValue v1, SymbolicValue v2, int off) {
  return expr_semantics_embed_eval<SymbolicValue, SymbolicExprSemantics>(v1,
									 v2,
									 off);
}

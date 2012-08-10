/*
 * Copyright (c) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * 
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#include "smtlib-writer.hh"

#include <cassert>
#include <kernel/expressions/ExprVisitor.hh>

using namespace std;

class SMTLibVisitor : public ConstExprVisitor 
{
  ostream &out;
public:


  SMTLibVisitor (ostream &o) : ConstExprVisitor(), out (o) {}

  ~SMTLibVisitor () { }

  virtual void visit (const Constant *c) {
    out << "#x" << hex << c->get_val ();
  }

  virtual void visit (const Variable *) {
  }

  virtual void visit (const UnaryApp *e) {
    out << "(";
    if (e->get_op () == BV_OP_NOT)
      {
	out << "bvnot ";
      }
    else
      {
	assert (e->get_op () == BV_OP_NEG);
	out << "bvneg ";
      }
    out << ")";
  }

  virtual void visit (const BinaryApp *e) {
    out << "(";
    switch (e->get_op ())
      {
      case BV_OP_ADD: 
	break;

      case BV_OP_SUB:
	break;

      case BV_OP_MUL_S:
	break;

      case BV_OP_MUL_U:
	break;

      case BV_OP_DIV_S:
	break;

      case BV_OP_DIV_U:
	break;

      case BV_OP_MODULO:
	break;

      case BV_OP_CONCAT:
	break;

      case BV_OP_AND:
	break;

      case BV_OP_OR:
	break;

      case BV_OP_XOR:
	break;

      case BV_OP_LSH:
	break;

      case BV_OP_RSH_U:
	break;

      case BV_OP_RSH_S:
	break;

      case BV_OP_ROR:
	break;

      case BV_OP_ROL:
	break;

      case BV_OP_EQ:
	break;

      case BV_OP_NEQ:
	break;

      case BV_OP_LT_S:
	break;

      case BV_OP_LT_U:
	break;

      case BV_OP_LEQ_S:
	break;

      case BV_OP_LEQ_U:
	break;


      case BV_OP_GT_S:
	break;

      case BV_OP_GT_U:
	break;

      case BV_OP_GEQ_S:
	break;

      case BV_OP_GEQ_U:
	break;



      case BV_OP_EXTEND_S:
	break;

      case BV_OP_EXTEND_U:
	break;

      default:
	assert (e->get_op () == BV_OP_POW);
	break;      
      }
    out << ")";
  }

  virtual void visit (const TernaryApp *e) {
    assert (e->get_op () == BV_OP_EXTRACT);
  }

  virtual void visit (const MemCell *e) {
    throw SMTLibUnsupportedExpression (e->to_string ());
  }

  virtual void visit (const RegisterExpr *e) {
    throw SMTLibUnsupportedExpression (e->to_string ());
  }

  virtual void visit (const QuantifiedExpr *e) {
    throw SMTLibUnsupportedExpression (e->to_string ());
  }
};

void 
smtlib_writer (std::ostream &out, const Expr *e)
  throw (SMTLibUnsupportedExpression)
{
  SMTLibVisitor writer (out);

  e->acceptVisitor (writer);
  out.flush ();
}

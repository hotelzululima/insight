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
#include "expr-writer.hh"

#include <kernel/expressions/ExprVisitor.hh>
#include <kernel/expressions/Operators.hh>

class ExprWriter : public ConstExprVisitor 
{
  std::ostream &out;

public:

  ExprWriter (std::ostream &o) : ConstExprVisitor(), out (o) {}

  virtual ~ExprWriter () { }

  void output_bv_window (const Expr *e) {
    int bv_offset = e->get_bv_offset ();
    int bv_size = e->get_bv_size ();

    out << std::dec << "{" << bv_offset << ";" << bv_size << "}";
  }

  virtual void visit (const RandomValue *c) {
    out << "RND";
  }

  virtual void visit (const Constant *c) {
    out << "0x" << std::hex << c->get_val ()
	<< std::dec << "{0;" << c->get_bv_size () << "}";
  }

  virtual void visit (const Variable *v) {
    out << "{" << v->get_id () << "}";
    output_bv_window (v);
  }

  virtual void visit (const UnaryApp *e) {
    out << "(" << unary_op_to_string (e->get_op ()) << " ";
    e->get_arg1 ()->acceptVisitor (this);
    out << ")";
    output_bv_window (e);
  }

  virtual void visit (const BinaryApp *e) {
    out << "(" << binary_op_to_string (e->get_op ()) << " ";
    e->get_arg1 ()->acceptVisitor (this);
    out << " ";
    e->get_arg2 ()->acceptVisitor (this);
    out << ")";
    output_bv_window (e);
  }

  virtual void visit (const TernaryApp *e) {
    out << "(" << ternary_op_to_string (e->get_op ()) << " ";
    e->get_arg1 ()->acceptVisitor (this);
    out << " ";
    e->get_arg2 ()->acceptVisitor (this);
    out << " ";
    e->get_arg3 ()->acceptVisitor (this);
    out << ")";
    output_bv_window (e);
  }

  virtual void visit (const MemCell *e) {
    out << "[";
    if (e->get_tag () != DEFAULT_TAG)
      out << e->get_tag () << ":";
    e->get_addr ()->acceptVisitor (this);
    out << "]";
    output_bv_window (e);
  }

  virtual void visit (const RegisterExpr *e) {
    out << "%" << e->get_name ();
    output_bv_window (e);
  }

  virtual void visit (const QuantifiedExpr *e) {
    const char *qop = e->is_exists () ? "<>" : "[]";
    out << qop[0] << e->get_variable ()->get_id () << qop[1] << "(";
    e->get_body ()->acceptVisitor (this);
    out << ")";
  }
};

void
expr_writer (std::ostream &out, const Expr *e)
{
  ExprWriter w (out);

  e->acceptVisitor (w);
}

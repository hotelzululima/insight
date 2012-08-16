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

#include <iomanip>
#include <cassert>
#include <kernel/expressions/ExprVisitor.hh>
#include <kernel/expressions/ExprUtils.hh>
#include <tr1/unordered_set>

using namespace std;
using namespace std::tr1;
using namespace exprutils;


typedef unordered_set<const Expr *> ExprSet;

class SMTLibVisitor : public ConstExprVisitor 
{
  ostream &out;
public:


  SMTLibVisitor (ostream &o) : ConstExprVisitor(), out (o) {}

  ~SMTLibVisitor () { }

  virtual void visit (const Constant *c) {
    word_t val = c->get_val ();
    int bv_size = c->get_bv_size () ;

    if (c->get_bv_size () % 8 == 0)
      out << "#x" << setw (bv_size / 4) << setfill ('0') << hex << val;
    else
      {
	out << "#b";
	while (bv_size--)
	  out << dec << (0x1 & (val >> bv_size));
      }
  }

  virtual void visit (const Variable *v) {
    out << v->get_id ();
  }

  void extract_bv_window (const Expr *e) {
    out << "(_ extract " 
	<< dec << (e->get_bv_offset () + e->get_bv_size () - 1)
	<< " "
	<< dec << e->get_bv_offset () << " "
	<< ") ";

  }

  bool has_boolean_bv (const Expr *e) {
    return e->get_bv_offset () == 0 && e->get_bv_size () == 1;
  }

  bool is_boolean (const Expr *e) {
    bool result = false;

    if (e->is_UnaryApp () && ((UnaryApp *)e)->get_op ())
      {
	UnaryApp *ua = (UnaryApp *) e;
	result = (ua->get_op () == BV_OP_NOT &&
		  has_boolean_bv (ua) && 
		  has_boolean_bv (ua->get_arg1 ()));
		  
      } 
    else if (e->is_BinaryApp ())
      {
	BinaryApp *ba = (BinaryApp *) e;
	BinaryOp op = ba->get_op ();
	switch (op) 
	  {
	  case BV_OP_AND: case BV_OP_OR:
	    result = (has_boolean_bv (ba) && 
		      has_boolean_bv (ba->get_arg1 ()) && 
		      has_boolean_bv (ba->get_arg2 ()));
	    break;
	  case BV_OP_EQ: case BV_OP_NEQ: case BV_OP_LT_S: case BV_OP_LT_U:
	  case BV_OP_LEQ_S: case BV_OP_LEQ_U: case BV_OP_GT_S: 
	  case BV_OP_GT_U: case BV_OP_GEQ_S: case BV_OP_GEQ_U:
	    result = true;
	    break;
	  default:
	    break;
	  }
      }

    return result;
  }

  void output_boolean (const Expr *e) {
    bool is_boolean = has_boolean_bv (e);
    if (! is_boolean)
      out << "(not (= ";
    e->acceptVisitor (this);
    if (! is_boolean)
      {
	out << " ";
	if (e->get_bv_size () % 8 == 0)
	  out << "#x" << string (e->get_bv_size () / 4, '0');
	else 
	  out << "#b" << string (e->get_bv_size (), '0');	 
	out << "))";
      }
  }

  virtual void visit (const UnaryApp *e) {
    const char *op;
    bool is_bool = is_boolean (e);

    if (e->get_op () == BV_OP_NOT)
      op = is_bool ? "not" : "bvnot";
    else
      {
	assert (e->get_op () == BV_OP_NEG);
	op = "bvneg";
      }

    out << "(" << op << " ";
    if (is_bool)
      output_boolean (e->get_arg1 ());
    else
      e->get_arg1 ()->acceptVisitor (this);
    out << ")";
  }

  void lt_s (const BinaryApp *) {
    
  }

  void lt_u (const BinaryApp *e) {
    out << "(bvult ";
    e->get_arg1 ()->acceptVisitor (this);
    out << " ";
    e->get_arg2 ()->acceptVisitor (this);
    out << ")";
  }

  void eq (const BinaryApp *e) {
    out << "(= ";
    e->get_arg1 ()->acceptVisitor (this);
    out << " ";
    e->get_arg2 ()->acceptVisitor (this);
    out << ")";
  }

  virtual void visit (const BinaryApp *e) {
    bool is_bool = is_boolean (e);
    BinaryOp op = e->get_op ();

    switch (op)
      {
      case BV_OP_AND: case BV_OP_OR:
	out << "(";
	if (is_bool)
	  {
	    out << (op == BV_OP_AND ? "and " : "or ");
	    output_boolean (e->get_arg1 ());
	    out << " ";
	    output_boolean (e->get_arg2 ());
	  }
	else
	  {
	    out << (op == BV_OP_AND ? "bvand " : "bvor ");
	    e->get_arg1 ()->acceptVisitor (this);
	    out << " ";
	    e->get_arg2 ()->acceptVisitor (this);
	  }
	out << ")";
	break;

      case BV_OP_NEQ:
	out << "(not ";

      case BV_OP_EQ: 
	eq (e);
	if (op == BV_OP_NEQ)
	  out << ")";
	break;

      case BV_OP_GEQ_U: case BV_OP_GEQ_S:
	out << "(not ";

      case BV_OP_LT_U: case BV_OP_LT_S:
	if (op == BV_OP_LT_U || op == BV_OP_GEQ_U)
	  lt_u (e);
	else 
	  lt_s (e);
	if (op == BV_OP_GEQ_U || op == BV_OP_GEQ_S)
	  out << ")";
	break;

      case BV_OP_GT_U: case BV_OP_GT_S:
	out << "(not ";

      case BV_OP_LEQ_U: case BV_OP_LEQ_S:
	out << "(or ";
	if (op == BV_OP_LEQ_U || BV_OP_GT_U)
	  lt_u (e);
	else
	  lt_s (e);
	out << " ";
	eq (e);
	out << ")";
	if (op == BV_OP_GT_U || op == BV_OP_GT_S)
	  out << ")";
	break;

      case BV_OP_XOR:
	out << "(bvor (bvand ";
	e->get_arg1 ()->acceptVisitor (this);
	out << " (bvnot ";
	e->get_arg2 ()->acceptVisitor (this);
	out << ")) (bvand (bvnot ";
	e->get_arg1 ()->acceptVisitor (this);
	out << ") ";
	e->get_arg2 ()->acceptVisitor (this);
	out << "))";
	break;

      case BV_OP_ADD: case BV_OP_SUB:
	{
	  bool extract = 	  
	    (e->get_bv_offset () != 0 ||
	     e->get_bv_size () != e->get_arg1 ()->get_bv_size ());
	
	  if (extract)
	    {
	      out << "(";
	      extract_bv_window (e);
	    }
	  out << "(" << (op == BV_OP_ADD ? "bvadd " : "bvsub ");
	  e->get_arg1 ()->acceptVisitor (this);
	  out << " ";
	  e->get_arg2 ()->acceptVisitor (this);
	  out << ")";
	  if (extract)
	    out << ")";
	}
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


      case BV_OP_LSH:
	break;

      case BV_OP_RSH_U:
	break;

      case BV_OP_RSH_S:
	break;


      case BV_OP_EXTEND_S:
	break;

      case BV_OP_EXTEND_U:
	break;

      case BV_OP_ROR:
      case BV_OP_ROL:
      case BV_OP_POW:
      default:
	throw SMTLibUnsupportedExpression (e->to_string ());
      }
  }

  virtual void visit (const TernaryApp *e) {
    assert (e->get_op () == BV_OP_EXTRACT);
  }

  virtual void visit (const MemCell *e) {
    // to be fixed !!!
    out << "(select memory ";
    e->get_addr ()->acceptVisitor (this);
    out << ")";
  }

  virtual void visit (const RegisterExpr *e) {
    const RegisterDesc *rd = e->get_descriptor ();
    bool extract =  (! (e->get_bv_offset () == 0 && 
			e->get_bv_size () == rd->get_register_size ()));
    if (extract)
      {
	out << "(";
	extract_bv_window (e);
      }
    out << rd->get_label ();
    if (extract)
      {
	out << ")";
      }
  }

  virtual void visit (const QuantifiedExpr *e) {
    throw SMTLibUnsupportedExpression (e->to_string ());
  }
};

static void
s_create_variables (std::ostream &out, const Expr *e, 
		   const MicrocodeArchitecture *mca) 
{
  const Architecture *arch = mca->get_reference_arch ();

  out << "(declare-fun memory () (Array "
      << "(_ BitVec " << (8 * arch->address_range) << " ) "
      << "(_ BitVec 8 ) "
      << ")) " << endl;

  ExprSet vars = collect_subterms_of_type<ExprSet, Variable> (e, true);

  for (ExprSet::const_iterator i = vars.begin (); i != vars.end (); i++)
    {
      const Variable *v = dynamic_cast<const Variable *>(*i);

      assert (v != NULL);
      out << "(declare-fun " << v->get_id () << " () "
	  << "(_ BitVec " << v->get_bv_size () << ") " 
	  << ") " << endl;	  
    }

  vars = collect_subterms_of_type<ExprSet, RegisterExpr> (e, true);
  unordered_set<const RegisterDesc *> cache;
  for (ExprSet::const_iterator i = vars.begin (); i != vars.end (); i++)
    {
      const RegisterExpr *reg = dynamic_cast<const RegisterExpr *>(*i);

      assert (reg != NULL);

      const RegisterDesc *regdesc = reg->get_descriptor ();
      
      if (! (cache.find (regdesc) == cache.end ()))
	continue;
      
      assert (! regdesc->is_alias ());
      
      out << "(declare-fun " << regdesc->get_label () << " () "
	  << "(_ BitVec " << regdesc->get_register_size () << ") " 
	  << ") " << endl;
      cache.insert (regdesc);
    }
}

void 
smtlib_writer (std::ostream &out, const Expr *e, 
	       const MicrocodeArchitecture *mca) 
  throw (SMTLibUnsupportedExpression)
{
  SMTLibVisitor writer (out);

  out << "(set-option :print-success false) " << endl
      << "(set-logic QF_AUFBV) " << endl;
  s_create_variables (out, e, mca);
  out << "(assert ";
  writer.output_boolean (e); 
  out << ") "<< endl
      << "(check-sat) " << endl
      << "(exit) " << endl
      << endl;

  out.flush ();
}

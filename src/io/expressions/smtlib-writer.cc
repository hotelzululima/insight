/*
 * Copyright (c) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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
#include <list>
#include "smtlib-writer.hh"

#include <stdlib.h>

#include <iomanip>
#include <cassert>

#include <kernel/expressions/ExprVisitor.hh>
#include <kernel/expressions/exprutils.hh>
#include <utils/logs.hh>
#include <utils/unordered11.hh>

using namespace std;

class SMTLibVisitor;

class CountSharedSubFormulas : public ConstExprVisitor
{
  struct DFScounters {
    int enter;
    int leave;
    int counter;
  };

  typedef std::unordered_map<const Expr *, DFScounters> Counters;
  typedef std::unordered_set<const Expr *> Done;

  int max;
  int date;
  Counters counters;
  list<const Expr *> shared;
  Done done;

public :

  CountSharedSubFormulas ()
    : ConstExprVisitor (), max (0), date (0), counters (), shared (), done () {
  }

  virtual ~CountSharedSubFormulas () {
  }


  bool operator () (const Expr *e1, const Expr *e2) {
    return  counters[e1].leave < counters[e2].leave;
  }

  const list<const Expr *> &get_shared () const {
    return shared;
  }

  void open_context (std::ostream &out, SMTLibVisitor &sw);

  void close_context (std::ostream &out) const {
    int nb_symbols = shared.size ();
    while (nb_symbols--)
      out << ")";
  }

  void output_shared_symbol (const DFScounters &c, std::ostream &out) const {
    out << "_$" << dec << c.enter;
  }

  bool output_shared_expr (const Expr *e, std::ostream &out) {
    if (done.find (e) == done.end ())
      return false;
    Counters::const_iterator i = counters.find (e);
    output_shared_symbol (i->second, out);

    return true;
  }

  int display_counters (std::ostream &out) const {
    if (max <= 1)
      return 0;

    int *distrib = new int[max + 1];

    for (int i = 0; i <= max; i++)
      distrib[i] = 0;
    for (Counters::const_iterator i = counters.begin (); i != counters.end ();
	 i++)
      distrib[i->second.counter]++;
    out << "Shared Formulas: " << endl;
    int result = 0;
    for (int i = 2; i <= max; i++)
      if (distrib[i] > 0)
	{
	  out << "shared " << i << " times : " << distrib[i] << endl;
	  result++;
	}
    delete[] distrib;
    return result;
  }

  virtual int update_counter (const Expr *e) {
    if (counters.find (e) == counters.end ())
      {
	date++;
	counters[e].enter = date;
	counters[e].counter = 1;
	counters[e].leave = date;
      }
    else
      {
	counters[e].counter++;
      }

    if (counters[e].counter > max)
      max = counters[e].counter;

    return counters[e].counter;
  }

  virtual void visit (const Constant *) { }

  virtual void visit (const RandomValue *) {
    logs::error << "RandomValue should not be sent to SMT solver." << endl;
    abort ();
  }

  virtual void visit (const Variable *) { }

  virtual void visit (const UnaryApp *e) {
    if (update_counter (e) > 1)
      return;
    e->get_arg1 ()->acceptVisitor (this);
    counters[e].leave = date + 1;
  }

  virtual void visit (const BinaryApp *e) {
    if (update_counter (e) > 1)
      return;
    e->get_arg1 ()->acceptVisitor (this);
    e->get_arg2 ()->acceptVisitor (this);
    counters[e].leave = date + 1;
  }
  virtual void visit (const TernaryApp *e) {
    if (update_counter (e) > 1)
      return;
    e->get_arg1 ()->acceptVisitor (this);
    e->get_arg2 ()->acceptVisitor (this);
    e->get_arg3 ()->acceptVisitor (this);
    counters[e].leave = date + 1;
  }

  virtual void visit (const MemCell *e) {
    if (update_counter (e) > 1)
      return;
    e->get_addr ()->acceptVisitor (this);
    counters[e].leave = date + 1;
  }

  virtual void visit (const RegisterExpr *) {
  }

  virtual void visit (const QuantifiedExpr *e) {
    throw SMTLibUnsupportedExpression (e->to_string ());
  }
};

class SMTLibVisitor : public ConstExprVisitor
{
  ostream &out;
  const string &memvar;
  int addrsize;
  Architecture::endianness_t endian;
  CountSharedSubFormulas *cssf;

public:


  SMTLibVisitor (ostream &o, const string &mv, int bpa,
		 Architecture::endianness_t e)
    : ConstExprVisitor (), out (o), memvar (mv), addrsize (bpa), endian (e),
      cssf (NULL) {}

  ~SMTLibVisitor () { }

  void set_cssf (CountSharedSubFormulas *cssf) {
    this->cssf = cssf;
  }

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

  virtual void visit (const RandomValue *) {
    logs::error << "RandomValue should not be sent to SMT solver." << endl;
    abort ();
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
    if (e->get_bv_size () > 1)
      out << "(not (= ";
    else
      out << "(= ";
    e->acceptVisitor (this);
    out << " ";
    if (e->get_bv_size () == 1)
      out << "#b1";
    else if (e->get_bv_size () % 8 == 0)
      out << "#x" << string (e->get_bv_size () / 4, '0') << ')';
    else
      out << "#b" << string (e->get_bv_size (), '0') << ')';
    out << ")";
  }

  virtual void visit (const UnaryApp *e) {
    if (cssf->output_shared_expr (e, out))
      return;
    const char *op;
    bool extract = (e->get_bv_offset () != 0 ||
		    e->get_bv_size () != e->get_arg1 ()->get_bv_size ());
    bool extend = false;

    if (e->get_op () == BV_OP_NOT)
      op = "bvnot";
    else
      {
	assert (e->get_op () == BV_OP_NEG);
	op = "bvneg";
	extend = true;
      }

    if (extract)
      {
	out << "(";
	extract_bv_window (e);
      }
    if (extend && e->get_bv_size () > e->get_arg1 ()->get_bv_size ())
      {
	int ext = (e->get_bv_size () - e->get_arg1 ()->get_bv_size ());
	out << "((_ sign_extend " << dec << ext << ") ";
      }
    out << "(" << op << " ";
    e->get_arg1 ()->acceptVisitor (this);
    out << ")";
    if (extend && e->get_bv_size () > e->get_arg1 ()->get_bv_size ())
      out << ")";
    if (extract)
      out << ")";
  }

  bool need_extract (const BinaryApp *e) {
    bool result = true;

    if (e->get_op () == BV_OP_CONCAT)
      {
	result = (e->get_bv_offset () != 0 ||
		  (e->get_bv_size () < e->get_arg1 ()->get_bv_size () +
		   e->get_arg2 ()->get_bv_size ()));
      }
    else if (e->get_op () != BV_OP_EXTEND_U && e->get_op () != BV_OP_EXTEND_S)
      result = (e->get_bv_offset () != 0 ||
		e->get_bv_size () != e->get_arg1 ()->get_bv_size ());
    return result;
  }

  virtual void visit (const BinaryApp *e) {
    if (cssf->output_shared_expr (e, out))
      return;

    BinaryOp op = e->get_op ();
    const char *op_str = NULL;
    bool extract = need_extract (e);
    bool extend = false;
    bool with_sign = false;
    bool ite = false;

    switch (op)
      {
      case BV_OP_AND: case BV_OP_OR:
	out << "(";
	if (extract)
	  {
	    extract_bv_window (e);
	    out << "(";
	  }

	out << (op == BV_OP_AND ? "bvand " : "bvor ");
	e->get_arg1 ()->acceptVisitor (this);
	out << " ";
	e->get_arg2 ()->acceptVisitor (this);
	if (extract)
	  {
	    out << ")";
	  }
	out << ")";
	break;

      case BV_OP_MUL_S: with_sign = true;
      case BV_OP_MUL_U: op_str = "bvmul"; extend = true; goto output_binary_1;
      case BV_OP_ADD: op_str = "bvadd"; extend = true; goto output_binary_1;
      case BV_OP_SUB: op_str = "bvsub"; extend = true; goto output_binary_1;

      case BV_OP_LSH: op_str = "bvshl"; goto output_binary_1;
      case BV_OP_RSH_U: op_str = "bvlshr"; goto output_binary_1;
      case BV_OP_RSH_S: op_str = "bvashr"; goto output_binary_1;
      case BV_OP_MODULO:
	op_str = "bvurem"; goto output_binary_1; // to be fix with signed mod.
      case BV_OP_DIV_S: op_str = "bvsdiv"; goto output_binary_1;
      case BV_OP_DIV_U: op_str = "bvudiv"; goto output_binary_1;
      case BV_OP_CONCAT: op_str = "concat"; goto output_binary_1;
      case BV_OP_XOR: op_str = "bvxor"; goto output_binary_1;


      case BV_OP_NEQ: op_str = "distinct";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_EQ: op_str = "=";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_GEQ_U: op_str = "bvuge";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_GEQ_S: op_str = "bvsge";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_LT_U: op_str = "bvult";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_LT_S: op_str = "bvslt";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_GT_U: op_str = "bvugt";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_GT_S: op_str = "bvsgt";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_LEQ_U: op_str = "bvule";
	extract = false; ite = true; goto output_binary_1;
      case BV_OP_LEQ_S: op_str = "bvsle";
	extract = false; ite = true; goto output_binary_1;

      output_binary_1:
	if (ite)
	  out << "(ite ";
	if (extract)
	  {
	    out << "(";
	    extract_bv_window (e);
	  }

	out << "(" << op_str << " ";
	if (extend && e->get_bv_size () > e->get_arg1 ()->get_bv_size ())
	  {
	    int ext = (e->get_bv_size () - e->get_arg1 ()->get_bv_size ());
	    if (with_sign)
	      out << "((_ sign_extend ";
	    else
	      out << "((_ zero_extend ";
	    out << dec << ext << ") ";
	  }
	e->get_arg1 ()->acceptVisitor (this);
	if (extend && e->get_bv_size () > e->get_arg1 ()->get_bv_size ())
	  out << ") ";
	out << " ";
	if (extend && e->get_bv_size () > e->get_arg2 ()->get_bv_size ())
	  {
	    int ext = (e->get_bv_size () - e->get_arg2 ()->get_bv_size ());
	    if (with_sign)
	      out << "((_ sign_extend ";
	    else
	      out << "((_ zero_extend ";
	    out << dec << ext << ") ";
	  }
	e->get_arg2 ()->acceptVisitor (this);
	if (extend && e->get_bv_size () > e->get_arg2 ()->get_bv_size ())
	  out << ")";
	out << ")";
	if (extract)
	  out << ")";
	if (ite)
	  out << " #b1 #b0)";
	break;

      case BV_OP_ROR: op_str = "rotate_right"; goto output_binary_2;
      case BV_OP_ROL: op_str = "rotate_left"; goto output_binary_2;
      case BV_OP_EXTEND_U: op_str = "zero_extend"; goto output_binary_2;
      case BV_OP_EXTEND_S: op_str = "sign_extend"; goto output_binary_2;
      output_binary_2:
	if (extract)
	  {
	    out << "(";
	    extract_bv_window (e);
	  }

	{
	  Constant *c = dynamic_cast <Constant *> (e->get_arg2 ());
	  if (c == NULL)
	    throw SMTLibUnsupportedExpression (e->to_string ());
	  word_t val = c->get_val ();
	  if (op == BV_OP_EXTEND_U || op == BV_OP_EXTEND_S)
	    val = c->get_val () - e->get_arg1 ()->get_bv_size ();
	  out << "((_ " << op_str << " " << dec << val << ") ";
	  e->get_arg1 ()->acceptVisitor (this);
	  out << ")";
	}

	if (extract)
	  out << ")";
	break;

      case BV_OP_POW:
      default:
	throw SMTLibUnsupportedExpression (e->to_string ());
      }
  }

  virtual void visit (const TernaryApp *e) {
    if (cssf->output_shared_expr (e, out))
      return;

    assert (e->get_op () == BV_OP_EXTRACT);
    Constant *expr_offset = dynamic_cast <Constant *> (e->get_arg2 ());
    Constant *expr_size = dynamic_cast <Constant *> (e->get_arg3 ());

    if (expr_offset == NULL || expr_size == NULL)
      throw SMTLibUnsupportedExpression (e->to_string ());

    constant_t offset = expr_offset->get_val ();
    constant_t size = expr_size->get_val ();
    if (offset != e->get_bv_offset () || size != e->get_bv_size ())
      {
	out << "((_ extract "
	    << dec << (e->get_bv_offset () + e->get_bv_size () - 1) << " "
	    << e->get_bv_offset () << ") ";
      }
    out << "((_ extract "
	<< dec << (offset + size - 1) << " " << offset << ") ";
    e->get_arg1 ()->acceptVisitor (this);
    out << ")";
    if (offset != e->get_bv_offset () || size != e->get_bv_size ())
      out << ")";
  }

  virtual void visit (const MemCell *e) {
    if (cssf->output_shared_expr (e, out))
      return;

    if (e->get_bv_size () == 8 && e->get_bv_offset () == 0)
      {
	// to be fixed !!!
	int extend = addrsize - e->get_addr ()->get_bv_size ();
	out << "(select " << memvar << " ";
	if (extend > 0)
	  out << "((_ zero_extend " << dec << extend << ") ";
	e->get_addr ()->acceptVisitor (this);
	if (extend > 0)
	  out << ")";
	out << ")";
      }
    else
      {
	int nb_bytes = (e->get_bv_offset () + e->get_bv_size ()) / 8;
	if (e->get_bv_size () % 8 != 0)
	  nb_bytes++;
	Expr *addr = e->get_addr ()->ref ();
	Expr *bv = MemCell::create (addr->ref (), 0, 8);

	for (int i = 1; i < nb_bytes; i++)
	  {
	    Expr *a = BinaryApp::create (BV_OP_ADD, addr->ref (), i);
	    Expr *byte = MemCell::create (a, 0, 8);
	    Expr *tmp;
	    Expr *aux[2];
	    if (endian == Architecture::LittleEndian)
	      {
		aux[0] = byte;
		aux[1] = bv;
	      }
	    else
	      {
		aux[0] = bv;
		aux[1] = byte;
	      }
	    tmp = BinaryApp::create (BV_OP_CONCAT, aux[0], aux[1],
				     0, 8 * (i + 1));
	    bv = tmp;
	  }
	addr->deref ();
	bv = Expr::createExtract (bv, e->get_bv_offset (), e->get_bv_size ());
	bv->acceptVisitor (this);
	bv->deref ();
      }
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


void
smtlib_writer (std::ostream &out, const Expr *ep, const std::string &memvar,
	       int addrsize, Architecture::endianness_t endian, bool as_boolean)
  throw (SMTLibUnsupportedExpression)
{

  CountSharedSubFormulas cssf;
  SMTLibVisitor writer (out, memvar, addrsize, endian);
  writer.set_cssf (&cssf);

  Expr *e = ep->ref ();
  exprutils::simplify (&e);

  e->acceptVisitor (cssf);
  //  if (cssf.display_counters (logs::debug) > 0) {
    //    ((void) 0);
    //exprutils::simplify (&e);
    //  logs::debug << *e << endl;
  //}
  cssf.open_context (out, writer);

  if (as_boolean)
    writer.output_boolean (e);
  else
    e->acceptVisitor (writer);
  cssf.close_context (out);

  out.flush ();
  e->deref ();
}

void
CountSharedSubFormulas::open_context (std::ostream &out,
				      SMTLibVisitor &sw)
{
  for (Counters::const_iterator i = counters.begin (); i != counters.end ();
       i++)
    {
      if (i->second.counter > 1)
	shared.push_back (i->first);
    }
  shared.sort (*this);
  for (list<const Expr *>::iterator i = shared.begin (); i != shared.end ();
       i++)
    {
      out << "(let ((";
      output_shared_symbol (counters[*i], out);
      out << " ";
      (*i)->acceptVisitor (sw);
      out << ")) ";
      done.insert (*i);
    }
}

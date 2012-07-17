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

#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <string>
#include <sstream>
#include <iostream>
#include <ext/hash_map>
#include <ext/hash_map>
#include <utils/tools.hh>
#include <utils/bv-manip.hh>
#include <utils/infrastructure.hh>
#include <kernel/expressions/Formula.hh>
#include <kernel/expressions/FormulaVisitor.hh>
#include "kernel/expressions/PatternMatching.hh"
#include "Expressions.hh"

using namespace std;

class IllegalFormulaToExprCast {};


unsigned long long debug_nb_expr_in_heap = 0;

unsigned long long get_debug_nb_expr_in_heap()
{
  return debug_nb_expr_in_heap;
};

/*****************************************************************************/

Expr::Expr(int bv_offset, int bv_size) 
  : AtomicFormula(), bv_offset(bv_offset), bv_size(bv_size)
{
  debug_nb_expr_in_heap++;
}

Expr::~Expr()
{
  debug_nb_expr_in_heap--;
};

/*****************************************************************************/

int Expr::get_bv_size() const
{
  return bv_size;
};

int Expr::get_bv_offset() const
{
  return bv_offset;
};

Expr *
Expr::extract_with_bit_vector_of (const Expr *e) const
{
  return extract_bit_vector (e->get_bv_offset (), e->get_bv_size ());
}

Expr *
Expr::extract_with_bit_vector_size_of (const Expr *e) const
{
  return extract_bit_vector (0, e->get_bv_size ());
}

void 
Expr::extract_bit_vector (Expr *&e, int new_bv_offset, int new_bv_size)
{
  if (new_bv_offset == 0 && e->get_bv_size () == new_bv_size)
    return;

  assert (1 <= new_bv_size && new_bv_size < e->get_bv_size ());

  int offset = e->get_bv_offset () + new_bv_offset;
  
  assert (0 <= offset && offset < e->get_bv_size ());
  assert (0 <= offset + new_bv_size - 1 && 
	  offset + new_bv_size - 1 < e->get_bv_size ());


  Expr *tmp = e->extract_bit_vector (offset, new_bv_size);
  e->deref ();
  e = tmp;
}

void 
Expr::extract_with_bit_vector_of (Expr *&e, const Expr *other)
{
  Expr *tmp = e->extract_with_bit_vector_of (other);
  e->deref ();
  e = tmp;
}

void
Expr::extract_with_bit_vector_size_of (Expr *&e, const Expr *other)
{
  Expr *tmp = e->extract_with_bit_vector_size_of (other);
  e->deref ();
  e = tmp;
}


/*****************************************************************************/

Variable::Variable(const std::string &id, int bv_offset, int bv_size) 
  : Expr (bv_offset, bv_size), id(id) 
{
}

Variable::~Variable() 
{
}

Variable * 
Variable::create (const std::string &id, int bv_offset, int bv_size)
{
  return find_or_add (new Variable (id, bv_offset, bv_size));
}

std::string 
Variable::get_id() const 
{ 
  return id; 
}

Expr * 
Variable::extract_bit_vector (int new_bv_offset, int new_bv_size) const 
{
  return Variable::create (id, new_bv_offset, new_bv_size);
}

/*****************************************************************************/

Constant::Constant (constant_t v, int bv_offset, int bv_size) 
  : Expr (bv_offset, bv_size) 
{ 
  val = (constant_t) v; 
}

Constant * 
Constant::create (constant_t v, int bv_offset, int bv_size)
{
  return find_or_add (new Constant (v, bv_offset, bv_size));
}

Constant::~Constant() 
{
}

constant_t 
Constant::get_val() const 
{ 
  return BitVectorManip::extract_from_word (val, get_bv_offset (), 
					    get_bv_size ()); 
};

Expr * 
Constant::extract_bit_vector (int new_bv_offset, int new_bv_size) const 
{
  return Constant::create (val, new_bv_offset, new_bv_size);
}

/*****************************************************************************/

UnaryApp::UnaryApp(UnaryOp op, Expr *arg1, int bv_offset, int bv_size) 
  : Expr (bv_offset, bv_size), op(op), arg1(arg1)
{
}

UnaryApp *
UnaryApp::create (UnaryOp op, Expr *arg1)
{
  return UnaryApp::create (op, arg1, 0, arg1->get_bv_size ());
}

UnaryApp *
UnaryApp::create (UnaryOp op, Expr *arg1, int bv_offset, int bv_size)
{
  UnaryApp *tmp = new UnaryApp (op, arg1, bv_offset, bv_size);

  tmp = find_or_add (tmp);

  return tmp;
}

UnaryApp::~UnaryApp() 
{ 
  arg1->deref (); 
}

UnaryOp 
UnaryApp::get_op() const 
{ 
  return op; 
}

Expr * 
UnaryApp::get_arg1() const 
{ 
  return arg1; 
}

Expr * 
UnaryApp::extract_bit_vector (int new_bv_offset, int new_bv_size) const 
{
  return UnaryApp::create (op, arg1->ref (), new_bv_offset, new_bv_size);
}

/*****************************************************************************/

BinaryApp::BinaryApp(BinaryOp op, Expr *arg1, Expr *arg2, int bv_offset, 
		     int bv_size) 
  : Expr (bv_offset, bv_size),  op(op), arg1(arg1), arg2(arg2) 
{
}

BinaryApp *
BinaryApp::create (BinaryOp op, Expr *arg1, Expr *arg2)
{
  return BinaryApp::create (op, arg1, arg2, 0);
}

BinaryApp *
BinaryApp::create (BinaryOp op, Expr *arg1, int arg2)
{
  return BinaryApp::create (op, arg1, Constant::create (arg2));
}

BinaryApp * 
BinaryApp::create (BinaryOp op, Expr *arg1, Expr *arg2, int bv_offset, 
		   int bv_size)
{
  return find_or_add (new BinaryApp (op, arg1, arg2, bv_offset, bv_size));
}

BinaryApp *
BinaryApp::create (BinaryOp op, Expr *arg1, int arg2, int bv_offset, 
		   int bv_size)
{
  return BinaryApp::create (op, arg1, 
			    Constant::create (arg2),
			    bv_offset, bv_size);
}

BinaryApp::~BinaryApp() 
{
  arg1->deref ();
  arg2->deref ();
}

BinaryOp 
BinaryApp::get_op() const 
{ 
  return op; 
}

Expr * 
BinaryApp::get_arg1() const 
{ 
  return arg1; 
}

Expr * 
BinaryApp::get_arg2() const 
{ 
  return arg2; 
}

Expr * 
BinaryApp::extract_bit_vector (int new_bv_offset, int new_bv_size) const 
{
  return BinaryApp::create (op, arg1->ref (), arg2->ref (), new_bv_offset, 
			    new_bv_size);
}

/*****************************************************************************/
TernaryApp::TernaryApp(TernaryOp op, Expr *arg1, Expr *arg2, Expr *arg3, int bv_offset,
		     int bv_size)
  : Expr (bv_offset, bv_size),  op(op), arg1(arg1), arg2(arg2), arg3(arg3)
{
}

TernaryApp *
TernaryApp::create (TernaryOp op, Expr *arg1, Expr *arg2, Expr* arg3)
{
  //XXX: need to check bitvectors size here
  return TernaryApp::create (op, arg1, arg2, arg3, 0, arg1->get_bv_size ());
}


TernaryApp *
TernaryApp::create (TernaryOp op, Expr *arg1, Expr *arg2, Expr *arg3, int bv_offset,
		   int bv_size)
{
  //XXX: need to check bitvectors size here
  return find_or_add (new TernaryApp (op, arg1, arg2, arg3, bv_offset, bv_size));
}

TernaryOp
TernaryApp::get_op() const
{
  return op;
}

Expr *
TernaryApp::get_arg1() const
{
  return arg1;
}

Expr *
TernaryApp::get_arg2() const
{
  return arg2;
}

Expr *
TernaryApp::get_arg3() const
{
  return arg3;
}


Expr *
TernaryApp::extract_bit_vector (int new_bv_offset, int new_bv_size) const
{
  //XXX: need to check bitvectors size here
  return TernaryApp::create (op, arg1->ref (), arg2->ref (), arg3->ref(), new_bv_offset,
			    new_bv_size);
}

TernaryApp::~TernaryApp()
{
  arg1->deref ();
  arg2->deref ();
  arg3->deref ();
}


/*****************************************************************************/

LValue::LValue(int bv_offset, int bv_size) 
  : Expr (bv_offset, bv_size) 
{
}

/*****************************************************************************/

MemCell::MemCell(Expr *addr, Tag tag, int bv_offset, int bv_size) 
  : LValue (bv_offset, bv_size), addr(addr), tag(tag) 
{
}

MemCell * 
MemCell::create (Expr *addr, Tag tag, int bv_offset, int bv_size)
{
  return find_or_add (new MemCell (addr, tag, bv_offset, bv_size));
}

MemCell *
MemCell::create (Expr *addr, int bv_offset, int bv_size)
{
  return create (addr, DEFAULT_TAG, bv_offset, bv_size);
}

MemCell::~MemCell() 
{ 
  addr->deref (); 
}

Tag 
MemCell::get_tag() const 
{ 
  return tag; 
}

Expr * 
MemCell::get_addr() const 
{ 
  return addr; 
}

Expr * 
MemCell::extract_bit_vector (int new_bv_offset, int new_bv_size) const 
{
  return MemCell::create (addr->ref (), tag, new_bv_offset, new_bv_size);
}

/*****************************************************************************/

RegisterExpr::RegisterExpr(const RegisterDesc *reg, int bv_offset, int bv_size)
  : LValue (bv_offset, bv_size), regdesc (reg)
{ 
  assert (! regdesc->is_alias ());
}

RegisterExpr::~RegisterExpr() 
{
}

RegisterExpr *
RegisterExpr::create (const RegisterDesc *reg) 
{
  return create (reg, 0, reg->get_register_size ());
}

RegisterExpr *
RegisterExpr::create (const RegisterDesc *reg, int bv_offset, int bv_size)
{
  RegisterExpr *tmp = new RegisterExpr (reg, bv_offset, bv_size);
 
  return find_or_add(tmp);
}

const RegisterDesc *
RegisterExpr::get_descriptor () const {
  return regdesc;
}

const std::string & 
RegisterExpr::get_name() const 
{ 
  return regdesc->get_label ();
}

Expr * 
RegisterExpr::extract_bit_vector (int new_bv_offset, int new_bv_size) const 
{
  return RegisterExpr::create (regdesc, new_bv_offset, new_bv_size);
}

/*****************************************************************************/

unsigned int Variable::get_depth() const
{
  return 1;
}

unsigned int Constant::get_depth() const
{
  return 1;
}

unsigned int UnaryApp::get_depth() const
{
  return arg1->get_depth() + 1;
}

unsigned int BinaryApp::get_depth() const
{
  int decal = 1;
  if (op == CONCAT)
    decal = 0;
  int a = arg1->get_depth() + decal;
  int b = arg2->get_depth() + decal;
  return a > b ? a : b;
}

unsigned int TernaryApp::get_depth() const
{
  //XXX: need to implement this func
  throw runtime_error("TernaryApp::get_depth()");
}

unsigned int MemCell::get_depth() const
{
  return addr->get_depth() + 1;
}

unsigned int RegisterExpr::get_depth() const
{
  return 1;
}

/*****************************************************************************/

bool Variable::contains(Expr *o) const
{
  return equal (o);
}

bool Constant::contains(Expr *o) const
{
  return equal (o);
}

bool UnaryApp::contains(Expr *o) const
{
  return equal (o) || arg1->contains(o);
}

bool BinaryApp::contains(Expr *o) const
{
  return equal (o) || arg1->contains(o) || arg2->contains(o);
}

bool TernaryApp::contains(Expr *o) const
{
  return equal(o) || arg1->contains(o) || arg2->contains(o)
      || arg3->contains(o);
}

bool MemCell::contains(Expr *o) const
{
  return equal (o) || addr->contains(o);
}

bool RegisterExpr::contains(Expr *o) const
{
  return equal (o);
}

/*****************************************************************************/
#include <interpreters/concrete/ConcreteExprSemantics.hh>
#include <interpreters/concrete/ConcreteValue.hh>

/* Constant computations */
class ConstantCompute: public TermReplacingRule
{
  Expr *f(const Expr *e, TopBottomInfo *, BottomUpInfo **) {
    int offset = e->get_bv_offset ();
    int size = e->get_bv_size ();
    if (e->is_UnaryApp()) {
      const UnaryApp * ua = (const UnaryApp *) e;
      Expr * arg = ua->get_arg1();
      if (arg->is_Constant()) {
	Constant * c;
	switch (ua->get_op())
	  {
#define UNARY_OP(_op,_pp)			\
	    case _op:							\
	      c = Constant::create (ConcreteExprSemantics::_op ## _eval (((Constant *) arg), offset, size).get(), offset, size); \
      break;
#include <kernel/expressions/Operators.def>
#undef UNARY_OP
	  default:
	    throw NotApplicable();
	  }
	return c;
      }
    }

    if (e->is_BinaryApp()) {
      const BinaryApp * ba = (BinaryApp *) e;
      Expr * arg1 = ba->get_arg1();
      Expr * arg2 = ba->get_arg2();
      if (arg1->is_Constant() && arg2->is_Constant()) {
	Constant * c;
	switch (ba->get_op())
	  {
#define BINARY_OP(_op,_pp,_commut,_assoc)				\
	    case _op: c = Constant::create (ConcreteExprSemantics::_op ## _eval (((Constant *) arg1),((Constant *) arg2), offset, size).get(), offset, size); \
	      break;
#include <kernel/expressions/Operators.def>
#undef BINARY_OP
	  default:
	    throw NotApplicable();
	  }
	return c;
      }
    }
    throw NotApplicable();
  }
};
ConstantCompute ExprSimplConstantComputeRule;


class VoidOperations: public TermReplacingRule
{
  Expr * f(const Expr *e, TopBottomInfo *, BottomUpInfo **) {
    if (e->is_BinaryApp()) {
      const BinaryApp *ba = (const BinaryApp*) e;
      BinaryOp op = ba->get_op();
      if ((op == SUB || op == XOR) && 
	  ba->get_arg1() == ba->get_arg2()) {
	Constant *c = Constant::create (0, e->get_bv_offset(), 
					e->get_bv_size());
	return c;
      }
    }
    throw NotApplicable();
  }
};
VoidOperations VoidOperationsRule;


class BitFieldComputation: public TermReplacingRule
{
  Expr * f(const Expr *e, TopBottomInfo *, BottomUpInfo **) {
    if (e->is_Constant()) {
      const Constant *c = (const Constant *)e;
      //Not -1 because it raises unsignedness error from time to time
      long long max = 1;
      max = (max << (c->get_bv_size() - c->get_bv_offset())) - 1;
      long long min = 0 - max - 1;
      constant_t val = c->get_val();
      if (c->get_bv_offset() > 0 || val > max || val < min)
	{
	  unsigned long long v = val;
	  unsigned long long mask = 1;
	  mask = (mask << (c->get_bv_size())) - 1;
	  v = v & mask;
	  v = v >> c->get_bv_offset();
	  Constant *r = Constant::create ((constant_t)v, 0,
					  c->get_bv_size() - 
					  c->get_bv_offset());
	  return r;
	}
    }
    throw NotApplicable();
  }
};
BitFieldComputation BitFieldComputationRule;


/* Binary operation simplification */
// TODO: No, patter replacement: bottom_up_rewrite_pattern
class Rule1: public TermReplacingRule
{
  Expr * f(const Expr *e, TopBottomInfo *, BottomUpInfo **) {
    if (e->is_BinaryApp()) {
      const BinaryApp *ba = (const BinaryApp *)e;
      Expr *arg1 = ba->get_arg1();
      Expr *arg2 = ba->get_arg2();
      BinaryOp op = ba->get_op();

      if (arg1->is_BinaryApp()) {
	BinaryApp *o = (BinaryApp*) arg1;
	//Nul element
	if (((o->get_op() == ADD && op == SUB) || 
	     (o->get_op() == SUB && op == ADD)) &&
	    o->get_arg2() == arg2)
	  {
	    Expr *res = 
	      (Expr *)o->get_arg1()->extract_with_bit_vector_of (ba);
	    return res;
	  }
	//Distributivity
	if (arg2->is_Constant() && o->get_arg2()->is_Constant()) // OL: ????
	  {
	    constant_t c1 = ((Constant *)arg2)->get_val();
	    constant_t c2 = ((Constant *)o->get_arg2())->get_val();
	    if ((op == ADD && o->get_op() == ADD) || 
		(op == SUB && o->get_op() == SUB))
	      {
		arg1 = (Expr *)o->get_arg1()->ref ();
		arg2 = Constant::create (c1 + c2);
		Expr *res = BinaryApp::create (op, arg1, arg2, ba->get_bv_offset(),
					  ba->get_bv_size());
		return res;
	      }
	    else if ((op == UDIV && o->get_op() == UDIV) || 
		     (op == MUL_U && o->get_op() == MUL_U))
	      {
		arg1 = (Expr *)o->get_arg1()->ref ();
		arg2 = Constant::create (c1 * c2);
		Expr *res = BinaryApp::create (op, arg1, arg2, 
					       ba->get_bv_offset(),
					       ba->get_bv_size());
		return res;
	      }
	    else if ((op == ADD && o->get_op() == SUB) || 
		     (op == SUB && o->get_op() == SUB))
	      {
		arg1 = (Expr *)o->get_arg1()->ref ();
		if (c1 - c2 < 0)
		  {
		    arg2 = Constant::create (c2 - c1);
		    op = SUB;
		  }
		else
		  arg2 = Constant::create (c1 - c2);
		Expr *res = BinaryApp::create (op, arg1, arg2, 
					       ba->get_bv_offset(),
					       ba->get_bv_size());
		return res;
	      }
	    else if ((op == SUB && o->get_op() == ADD) || 
		     (op == SUB && o->get_op() == SUB))
	      {
		arg1 = (Expr *)o->get_arg1()->ref ();
		if (c1 - c2 < 0)
		  {
		    arg2 = Constant::create (c2 - c1);
		    op = ADD;
		  }
		else
		  arg2 = Constant::create (c1 - c2);
		Expr *res = BinaryApp::create (op, arg1, arg2, 
					       ba->get_bv_offset(), 
					       ba->get_bv_size());
		return res;
	      }
	  }
      }
    }
    throw NotApplicable();
  };
};

Rule1 ExprSimplRule1Rule;

/*****************************************************************************/

bool Expr::simplify(Expr ** e)
{
  vector<TermReplacingRule*> rules;
  rules.push_back(&ExprSimplConstantComputeRule);
  rules.push_back(&VoidOperationsRule);
  // BUG ... rules.push_back(&BitFieldComputationRule);
  rules.push_back(&ExprSimplRule1Rule);
  return Expr::bottom_up_apply_in_place_closure(e, rules);
}

/*****************************************************************************/

bool Expr::is_Variable() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<Variable *>(non_const_this);
}

bool Expr::is_Constant() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<Constant *>(non_const_this);
}

bool Expr::is_UnaryApp() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<UnaryApp *>(non_const_this);
}

bool Expr::is_BinaryApp() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<BinaryApp *>(non_const_this);
}

bool Expr::is_TernaryApp() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<TernaryApp *>(non_const_this);
}

bool Expr::is_LValue() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<LValue *>(non_const_this);
}

bool Expr::is_MemCell() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<MemCell *>(non_const_this);
}

bool Expr::is_RegisterExpr() const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<RegisterExpr *>(non_const_this);
}

/*****************************************************************************/

bool 
Variable::has_type_of (const Formula *F) const
{
  return dynamic_cast<const Variable *>(F);
}

bool 
Constant::has_type_of (const Formula *F) const
{
  return dynamic_cast<const Constant *>(F);
}

bool 
UnaryApp::has_type_of (const Formula *F) const
{
  return dynamic_cast<const UnaryApp *>(F);
}

bool 
BinaryApp::has_type_of (const Formula *F) const
{
  return dynamic_cast<const BinaryApp *>(F);
}

bool
TernaryApp::has_type_of (const Formula *F) const
{
  return dynamic_cast<const TernaryApp *>(F);
}

bool 
MemCell::has_type_of (const Formula *F) const
{
  return dynamic_cast<const MemCell *>(F);
}

bool 
RegisterExpr::has_type_of (const Formula *F) const
{
  return dynamic_cast<const RegisterExpr *>(F);
}

/*****************************************************************************/
/* Pattern Matching                                                          */
/*****************************************************************************/

PatternMatching *
Variable::pattern_matching(const Formula *e, 
			  const std::list<const Variable *> &fv) const
{
  if (find(fv.begin(), fv.end(), this) != fv.end())
    {
      PatternMatching *matching = new PatternMatching();      
      matching->set (this, e->ref ());

      return matching;
    }

  if (this == e)
    return new PatternMatching ();

  throw PatternMatchingFailure();
}

PatternMatching *
Constant::pattern_matching(const Formula *e, 
			   const std::list<const Variable *> &) const
{
  const Constant *ce = dynamic_cast<const Constant *> (e);

  if (ce == NULL || 
      get_bv_offset() != ce->get_bv_offset() || 
      get_bv_size() != ce->get_bv_size() || 
      this != ce)
    throw PatternMatchingFailure();

  return new PatternMatching ();
}

PatternMatching *
UnaryApp::pattern_matching(const Formula *e, 
			   const std::list<const Variable *> &fv) const
{
  const UnaryApp *ce = dynamic_cast<const UnaryApp *> (e);

  if (ce != NULL && 
      get_bv_offset () == ce->get_bv_offset () &&
      get_bv_size () == ce->get_bv_size () &&
      get_op () == ce->get_op ())
    return get_arg1()->pattern_matching(ce->get_arg1 (), fv);

  throw PatternMatchingFailure();
}

PatternMatching *
BinaryApp::pattern_matching(const Formula *e, 
			    const std::list<const Variable *> &fv) const
{
  const BinaryApp *ce = dynamic_cast<const BinaryApp *> (e);

  if (ce != NULL && 
      get_bv_offset () == ce->get_bv_offset () &&
      get_bv_size () == ce->get_bv_size () &&
      get_op () == ce->get_op ())
    {
      PatternMatching *pm1 = get_arg1()->pattern_matching(ce->get_arg1(), fv);
      try
	{
	  PatternMatching *pm2 = 
	    get_arg2()->pattern_matching(ce->get_arg2(), fv);
	  pm1->merge (pm2);
	  delete pm2;

	  return pm1;
	}
      catch (PatternMatchingFailure &)
	{
	  delete pm1;
	}
    }

  throw PatternMatchingFailure ();
}

PatternMatching *
TernaryApp::pattern_matching(const Formula *,
			    const std::list<const Variable *> &) const
{
	 //XXX: need to implement this func
  throw PatternMatchingFailure ();
}


PatternMatching *
MemCell::pattern_matching(const Formula *e, 
			  const std::list<const Variable *> &fv) const
{
  const MemCell *ce = dynamic_cast<const MemCell *> (e);

  if (ce != NULL && 
      get_bv_offset() == ce->get_bv_offset() &&
      get_bv_size() == ce->get_bv_size())
    {
      Expr *addr1 = get_addr();
      Expr *addr2 = ce->get_addr();

      return addr1->pattern_matching (addr2, fv);
    }
  throw PatternMatchingFailure ();
}

PatternMatching *
RegisterExpr::pattern_matching(const Formula *e, 
			   const std::list<const Variable *> &) const
{
  const RegisterExpr *ce = dynamic_cast<const RegisterExpr *> (e);

  if (ce == NULL || 
      get_bv_offset() != ce->get_bv_offset() || 
      get_bv_size() != ce->get_bv_size() || 
      this != ce)
    throw PatternMatchingFailure();

  return new PatternMatching ();
}

/*****************************************************************************/
// Kernel of rewriting mechanism
/*****************************************************************************/

Expr *Variable::bottom_up_apply (TermReplacingRule *r, 
				 TopBottomInfo *top_bottom_info, 
				 BottomUpInfo **bottom_up_info) const
{
  if (top_bottom_info != NULL) top_bottom_info->push(this);
  return r->f(this, top_bottom_info, bottom_up_info);
}

Expr *Constant::bottom_up_apply (TermReplacingRule *r, 
				 TopBottomInfo *top_bottom_info, 
				 BottomUpInfo **bottom_up_info) const
{
  if (top_bottom_info != NULL) top_bottom_info->push(this);
  return r->f(this, top_bottom_info, bottom_up_info);
}

Expr *UnaryApp::bottom_up_apply (TermReplacingRule *r, 
				 TopBottomInfo *top_bottom_info, 
				 BottomUpInfo **bottom_up_info) const
{
  if (top_bottom_info != NULL) top_bottom_info->push(this);
  bool applied = false;
  Expr *f1 = NULL;
  TopBottomInfo *tbi = 
    (top_bottom_info == NULL) ? NULL : top_bottom_info->clone();

  try
    {
      f1 = arg1->bottom_up_apply (r, tbi, bottom_up_info);
      applied = true;
    }
  catch (NotApplicable &) 
    {
      f1 = (Expr *) arg1->ref ();
    }

  Expr *tmp = UnaryApp::create (op, f1, get_bv_offset (), get_bv_size ());
  Expr *result = NULL;

  try { result = r->f(tmp, top_bottom_info, bottom_up_info); }
  catch (NotApplicable &)
    {
      if (applied) 
	result = (Expr *) tmp->ref ();
    }
  catch (IllegalFormulaToExprCast &e)
    {
      if (tbi)
	delete tbi;
      tmp->deref ();
      throw e;
    }

  tmp->deref ();
  if (tbi)
    delete tbi;

  if (result == NULL)
    throw NotApplicable();
  return result;
}

Expr *BinaryApp::bottom_up_apply (TermReplacingRule *r, 
				  TopBottomInfo *top_bottom_info, 
				  BottomUpInfo **bottom_up_info) const
{
  if (top_bottom_info != NULL) 
    top_bottom_info->push(this);
  TopBottomInfo *tbi1 = 
    (top_bottom_info == NULL) ? NULL : top_bottom_info->clone();
  TopBottomInfo *tbi2 = 
    (top_bottom_info == NULL) ? NULL : top_bottom_info->clone();

  bool applied1 = false;
  Expr *f1;
  Expr *f2;

  try
    {
      f1 = arg1->bottom_up_apply (r, tbi1, bottom_up_info);
      applied1 = true;
    }
  catch (NotApplicable &) 
    {
      f1 = (Expr *) arg1->ref ();
    }

  BottomUpInfo **info2 = NULL;
  if (bottom_up_info != NULL)   /* one does use bottom-up info mechanism */
    {
      info2 = new BottomUpInfo*;
      *info2 = NULL;
    }

  bool applied2 = false;
  try
    {
      f2 = arg2->bottom_up_apply (r, tbi2, info2);
      applied2 = true;
    }
  catch (NotApplicable &) 
    {
      f2 = (Expr *) arg2->ref ();
    }

  if (bottom_up_info != NULL)
    if (*bottom_up_info != NULL)
      (*bottom_up_info)->group(*info2);

  Expr *tmp = BinaryApp::create (op, f1, f2, get_bv_offset (), get_bv_size ());
  Expr *result = NULL;

  try { result = r->f(tmp, top_bottom_info, bottom_up_info); }
  catch (NotApplicable &)
    {
      if (applied1 || applied2) 
	result = (Expr *) tmp->ref ();
    }
  catch (IllegalFormulaToExprCast &e)
    {
      if (tbi1) 
	delete tbi1;
      if (tbi2) 
	delete tbi2;
      tmp->deref ();
      throw e;
    }
  tmp->deref ();
  if (tbi1) 
    delete tbi1;
  if (tbi2) 
    delete tbi2;
  if (result == NULL)
    throw NotApplicable();

  return result;
}

Expr *TernaryApp::bottom_up_apply (TermReplacingRule *,
				  TopBottomInfo *,
				  BottomUpInfo **) const
{
  //XXX: need to implement this func
  throw NotApplicable();
}


Expr *MemCell::bottom_up_apply (TermReplacingRule *r, 
				TopBottomInfo *top_bottom_info, 
				BottomUpInfo **bottom_up_info) const
{
  if (top_bottom_info != NULL) top_bottom_info->push(this);

  TopBottomInfo *tbi = 
    (top_bottom_info == NULL) ? NULL : top_bottom_info->clone();

  bool applied = false;
  Expr *a1;

  try
    {
      a1 = addr->bottom_up_apply (r, tbi, bottom_up_info);
      applied = true;
    }
  catch (NotApplicable &) 
    {
      a1 = (Expr *) addr->ref ();
    }

  Expr *tmp = MemCell::create (a1, tag, get_bv_offset (), get_bv_size ());
  Expr *result = NULL;

  try { result = r->f(tmp, top_bottom_info, bottom_up_info); }
  catch (NotApplicable &)
    {
      if (applied) 
	result = (Expr *) tmp->ref ();
    }
  catch (IllegalFormulaToExprCast &e)
    {
      if (tbi)
	delete tbi;

      tmp->deref ();
      throw e;
    }

  tmp->deref ();
  if (tbi)
    delete tbi;

  if (result == NULL)
    throw NotApplicable();
  return result;
}

Expr *RegisterExpr::bottom_up_apply (TermReplacingRule *r, 
				 TopBottomInfo *top_bottom_info, 
				 BottomUpInfo **bottom_up_info) const
{
  if (top_bottom_info != NULL) top_bottom_info->push(this);
  return r->f(this, top_bottom_info, bottom_up_info);
}

/*****************************************************************************/

std::list<Expr *> Variable::bottom_up_apply_nd(TermReplacingRuleNd *r) const
{
  return r->f(this);
}

std::list<Expr *> Constant::bottom_up_apply_nd(TermReplacingRuleNd *r) const
{
  return r->f(this);
}

std::list<Expr *> UnaryApp::bottom_up_apply_nd(TermReplacingRuleNd *r) const
{
  std::list<Expr *> f1 = arg1->bottom_up_apply_nd(r);
  std::list<Expr *> res;
  for (std::list<Expr *>::iterator it = f1.begin(); it != f1.end(); it++)
    {
      UnaryApp tmp(op, *it, this->get_bv_offset(), this->get_bv_size());
      std::list<Expr *> a = r->f(&tmp);
      res.insert(res.end(), a.begin(), a.end());
      // *it delete because tmp is deleted;
    }
  return res;
}

std::list<Expr *> BinaryApp::bottom_up_apply_nd(TermReplacingRuleNd *r) const
{
  std::list<Expr *> f1 = arg1->bottom_up_apply_nd(r);
  std::list<Expr *> f2 = arg2->bottom_up_apply_nd(r);
  std::list<Expr *> res;
  for (std::list<Expr *>::iterator it = f1.begin(); it != f1.end(); it++)
    {
      for (std::list<Expr *>::iterator it2 = f2.begin(); it2 != f2.end(); it2++)
        {
          BinaryApp tmp(op, (Expr *)(*it)->ref (), (Expr *)(*it2)->ref (), 
			this->get_bv_offset(), this->get_bv_size());
          std::list<Expr *> a = r->f(&tmp);
          res.insert(res.end(), a.begin(), a.end());
        }
    }
  for (std::list<Expr *>::iterator it2 = f1.begin(); it2 != f1.end(); it2++)
    (*it2)->deref ();
  for (std::list<Expr *>::iterator it2 = f2.begin(); it2 != f2.end(); it2++)
    (*it2)->deref ();

  return res;
}

std::list<Expr *> TernaryApp::bottom_up_apply_nd(TermReplacingRuleNd *) const
{
  //XXX: need to implement this func
  throw runtime_error("TernaryApp::bottom_up_apply_nd");
}

std::list<Expr *> MemCell::bottom_up_apply_nd(TermReplacingRuleNd *r) const
{
  std::list<Expr *> f1 = addr->bottom_up_apply_nd(r);
  std::list<Expr *> res;
  for (std::list<Expr *>::iterator it = f1.begin(); it != f1.end(); it++)
    {
      MemCell *tmp = MemCell::create (*it, this->get_bv_offset(), 
				      this->get_bv_size());
      std::list<Expr *> a = r->f(tmp);
      tmp->deref ();
      res.insert(res.end(), a.begin(), a.end());
      // *it delete because tmp is deleted;
    }
  return res;
}

std::list<Expr *> RegisterExpr::bottom_up_apply_nd(TermReplacingRuleNd *r) const
{
  return r->f(this);
}

/*****************************************************************************/

class FormulaToExprReplaceVariableRule : public TermReplacingRule
{
public:
  FormulaReplacingRule *r;

  Expr *f(const Expr *t, TopBottomInfo *, BottomUpInfo **)
  {
    Formula *new_t = r->f((Formula *) t);
    if (dynamic_cast<Expr *>(new_t))
      return (Expr *) new_t;
    else 
      {
	new_t->deref ();
	throw IllegalFormulaToExprCast();
      }
  }
};

/*! \note this is deleted by the caller if needed */
Formula * 
Expr::bottom_up_apply (FormulaReplacingRule *r) const
  throw (NotApplicable)
{
  FormulaToExprReplaceVariableRule er;
  er.r = r;
  try { return this->bottom_up_apply (&er, NULL, NULL); }
  catch (IllegalFormulaToExprCast &)
    {
      Formula *new_this = r->f(this);
      return new_this;
    }
}

/*****************************************************************************/

bool Expr::bottom_up_apply_in_place(Expr ** e,
		                            TermReplacingRule *r,
		                            TopBottomInfo *top_bottom_info,
		                            BottomUpInfo **bottom_up_info) {
  try {
    Expr * new_e = (*e)->bottom_up_apply (r, top_bottom_info, bottom_up_info);
    (*e)->deref ();
    *e = new_e;

    return true;
  }
  catch (NotApplicable &) { return false; }
}

/*****************************************************************************/

bool Expr::bottom_up_apply_in_place_closure(Expr ** e, std::vector<TermReplacingRule *> rules, int max_pass_nb) {
  bool result = false, modified = false;
  do {
    modified = false;
    for (std::vector<TermReplacingRule *>::iterator r=rules.begin(); 
	 r != rules.end(); r++) {
      Expr * cpy = NULL;
      if (!modified) cpy = (Expr *) (*e)->ref (); 
      // optimization: if modified is true, no need to check 
      // for modification
      bool r_application = 
	Expr::bottom_up_apply_in_place(e, *r, NULL, NULL);
      if (r_application && !modified)
	modified = !(cpy == *e);
      if (cpy != NULL) { cpy->deref (); cpy = NULL; };
    }
    result |= modified;
  } while (modified && (max_pass_nb-- != 0));
  return result;
};

/*****************************************************************************/

class ReplaceVariableRule : public TermReplacingRule
{
public:
  const Variable *v;
  const Expr *value;

  Expr *f(const Expr *t, TopBottomInfo *, BottomUpInfo **)
  {
    if (t->is_Variable())
      {
        if (t == v)
	  return (Expr *) value->ref ();
      }
    return (Expr *) t->ref ();
  }
};

//! \brief \todo delete v and value ?
Expr * 
Expr::replace_variable (const Variable *v, const Expr *value) const
{
  ReplaceVariableRule r;
  r.v = v;
  r.value = value;
  return bottom_up_apply (&r, NULL, NULL);
}

Expr * 
Expr::replace_variable (string v_id, const Expr *value) const
{
  Variable *v = Variable::create (v_id);
  Expr *result = replace_variable (v, value);
  v->deref ();

  return result;
}

bool 
Expr::replace_variable_in_place(Expr **e, const Variable *v, const Expr *value)
{
  ReplaceVariableRule r;
  r.v = v;
  r.value = value;
  try
    {
      Expr *new_e = (*e)->bottom_up_apply (&r, NULL, NULL);
      (*e)->deref ();
      *e = new_e;

      return true;
    }
  catch (NotApplicable &)
    {
      return false;
    }
}

/*****************************************************************************/
/* Syntaxic equality of expressions                                          */
/*****************************************************************************/

/*****************************************************************************/

bool Variable::operator<(const Variable &other) const
{
  return (strcmp(this->id.c_str(), other.id.c_str()) < 0);
  // TODO: perform equality check directly on the strings.
}

/*****************************************************************************/

template <class T> const T *
s_check_bv (const T *t, const Formula *F)
{
  const T *e = dynamic_cast<const T *> (F);

  if (e != NULL &&
      t->get_bv_offset () == e->get_bv_offset () &&
      t->get_bv_size () == e->get_bv_size ())
    return e;

  return NULL;
}

bool Variable::equal (const Formula *F) const
{
  const Variable *e = s_check_bv<Variable> (this, F);

  return (e != NULL && id == e->id);
}

bool Constant::equal (const Formula *F) const
{
  const Constant *e = s_check_bv<Constant> (this, F);
  
  return (e != NULL && val == e->val);
}

bool UnaryApp::equal (const Formula *F) const
{
  const UnaryApp *e = s_check_bv<UnaryApp> (this, F);

  return (e != NULL && op == e->op && arg1 == e->arg1);
}

bool BinaryApp::equal (const Formula *F) const
{
  const BinaryApp *e = s_check_bv<BinaryApp> (this, F);

  return (e != NULL && op == e->op && arg1 == e->arg1 && arg2 == e->arg2);
}

bool TernaryApp::equal(const Formula *F) const
{
  const TernaryApp *e = s_check_bv<TernaryApp> (this, F);

  return (e != NULL && op == e->op && arg1 == e->arg1 && arg2 == e->arg2
      && arg3 == e->arg3);
}

bool MemCell::equal (const Formula *F) const
{
  const MemCell *e = s_check_bv<MemCell> (this, F);

  return (e != NULL && tag == e->tag && addr == e->addr);
}

bool RegisterExpr::equal (const Formula *F) const
{
  const RegisterExpr *e = s_check_bv<RegisterExpr> (this, F);

  return (e != NULL && e->regdesc == regdesc);
}

/*****************************************************************************/
size_t 
Expr::hash () const 
{
  return 23 * bv_offset + 47 * bv_size;
}

size_t 
Variable::hash () const 
{ 
  return 13 * this->Expr::hash() + 51 * __gnu_cxx::hash<string>()(id);
}

size_t 
Constant::hash () const 
{ 
  return 13 * this->Expr::hash() + 51 * val;
}

size_t 
UnaryApp::hash () const 
{ 
  return 13 * this->Expr::hash() + 51 * op + 73 * arg1->hash ();
}

size_t 
BinaryApp::hash () const 
{ 
  return (13 * this->Expr::hash() + 51 * op + 73 * arg1->hash () +
	  119 * arg2->hash ());
}

size_t
TernaryApp::hash () const
{
  //XXX: check here again
  return (13 * this->Expr::hash() + 51 * op + 73 * arg1->hash () +
	  119 * arg2->hash () +  227 * arg3->hash ());
}

size_t 
MemCell::hash () const 
{ 
  return (13 * this->Expr::hash() + 19 * __gnu_cxx::hash<string>()(tag) +
	  111 * addr->hash ());
}

size_t 
RegisterExpr::hash () const 
{   
  return 13 * this->Expr::hash() + regdesc->hashcode ();
}


/*****************************************************************************/

string Expr::bv_pp() const
{
  ostringstream oss;

  if ((bv_offset != 0 || bv_size != BV_DEFAULT_SIZE))
    oss << "{" << bv_offset << ";" << bv_size << "}";
  return oss.str();
}

string Variable::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix << "{" << id << "}" << bv_pp();
  return oss.str();
}

string Constant::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix << "0x" << hex << uppercase << val << bv_pp();
  return oss.str();
}

string UnaryApp::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix << "(" << unary_op_to_string(op) << " " << arg1->pp() << ")"
      << bv_pp();
  return oss.str();
}

string BinaryApp::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix
      << "(" << binary_op_to_string(op) << " "
      << arg1->pp() << " " << arg2->pp() << ')'
      << bv_pp();

  return oss.str();
}

string TernaryApp::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix
      << "(" << ternary_op_to_string(op) << " "
      << arg1->pp() << " " << arg2->pp() << " " << arg3->pp() << ')'
      << bv_pp();

  return oss.str();
}

string MemCell::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix << "[";
  if (tag != DEFAULT_TAG)
    {
      oss << tag << ":";
    }
  oss << addr->pp() << "]" << bv_pp();

  return oss.str();
}

string RegisterExpr::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix << "%" << get_name () << bv_pp();
  return oss.str();
}

/*****************************************************************************/

ExprIterator *Expr::begin_prefix()
{
  return new ExprIterator(this, ITERATE_PREFIX);
}

ExprIterator *Expr::begin_infix()
{
  return new ExprIterator(this, ITERATE_INFIX);
}

ExprIterator *Expr::begin_postfix()
{
  return new ExprIterator(this, ITERATE_POSTFIX);
}

ExprIterator *Expr::end()
{
  return new ExprIterator();
}

/*****************************************************************************/
/* Iterators on expr                                                         */
/*****************************************************************************/

ExprIterator::ExprIterator(): mode(ITERATE_INFIX), indice(0), ss(NULL), expr((Expr *)NULL), eof(true)
{}

ExprIterator::ExprIterator(Expr *expr, ExprIteratorMode mode): mode(mode), indice(0), ss(NULL), expr(expr), eof(false)
{
  if (expr->is_BinaryApp())
    {
      BinaryApp *ba = (BinaryApp *) expr;
      this->max_indice = 2;
      switch (mode)
        {
        case ITERATE_INFIX:
        case ITERATE_POSTFIX:
          this->ss = new ExprIterator(ba->get_arg1(), mode);
          break;
        case ITERATE_PREFIX:
          this->ss = NULL;
          break;
        }
    }
  else if (expr->is_UnaryApp() || expr->is_MemCell())
    {
      Expr *e;
      if (expr->is_UnaryApp())
        e = ((UnaryApp *) expr)->get_arg1();
      else
        e = ((MemCell *) expr)->get_addr();
      this->max_indice = 1;
      switch (mode)
        {
        case ITERATE_POSTFIX:
          this->ss = new ExprIterator(e, mode);
          break;
        case ITERATE_INFIX:
        case ITERATE_PREFIX:
          this->ss = NULL;
          break;
        }
    }
  else
    {
      this->max_indice = 0;
      this->ss = NULL;
    }

}

ExprIterator::~ExprIterator()
{
  if (this->ss != NULL)
    {
      delete this->ss;
    }
}

bool ExprIterator::operator==(const ExprIterator &o)
{
  return (this->eof && o.eof) || (false);
}

bool ExprIterator::operator!=(const ExprIterator &o)
{
  return !(*this == o);
}

Expr *ExprIterator::operator*()
{
  if (this->eof)
    {
      return NULL;
    }
  if (ss != NULL)
    {
      return **ss;
    }
  return this->expr;
}

ExprIterator &ExprIterator::operator++(int i)
{
  if (this->eof)
    {
      return *this;
    }

  for (int j = 0; j <= i; j++)
    {
      if (this->ss != NULL)
        {
          (*(this->ss))++;
          if (this->ss->eof)
            {
              delete this->ss;
              this->ss = NULL;
            }
        }
      if (this->ss == NULL)
        {
          this->indice++;
          if (this->indice > this->max_indice)
            {
              this->eof = true;
              return *this;
            }

          Expr *to = NULL;

          if (this->expr->is_BinaryApp())
            {
              assert(this->indice == 1 || this->indice == 2);
              BinaryApp *ba = (BinaryApp *) expr;
              switch (mode)
                {
                case ITERATE_INFIX:
                  to = this->indice == 1 ? NULL : ba->get_arg2();
                  break;
                case ITERATE_POSTFIX:
                  to = this->indice == 1 ? ba->get_arg2() : NULL;
                  break;
                case ITERATE_PREFIX:
                  to = this->indice == 1 ? ba->get_arg1() : ba->get_arg2();
                  break;
                }
            }
          else if (this->expr->is_UnaryApp() || this->expr->is_MemCell())
            {
              assert(this->indice == 1);
              Expr *e;
              if (expr->is_UnaryApp())
                e = ((UnaryApp *) expr)->get_arg1();
              else
                e = ((MemCell *) expr)->get_addr();
              switch (mode)
                {
                case ITERATE_POSTFIX:
                  to = NULL;
                  break;
                case ITERATE_INFIX:
                case ITERATE_PREFIX:
                  to = e;
                  break;
                }
            }
          else
            {
              assert(false);
            }
          if (to != NULL)
            {
              this->ss = new ExprIterator(to, this->mode);
            }
          else
            {
              this->ss = NULL;
            }
        }
    }
  return *this;
}

ostream &operator<< (ostream &o, Expr &e)
{
  o << e.pp();
  return o;
}
			/* --------------- */

void 
Constant::acceptVisitor (FormulaVisitor *visitor)
{
  visitor->visit (this); 
}
 
void 
Variable::acceptVisitor (FormulaVisitor *visitor)
{
  visitor->visit (this); 
}
 
void 
UnaryApp::acceptVisitor (FormulaVisitor *visitor)
{
  visitor->visit (this); 
}
 
void 
BinaryApp::acceptVisitor (FormulaVisitor *visitor)
{
  visitor->visit (this); 
}
 
void 
TernaryApp::acceptVisitor (FormulaVisitor *visitor)
{
  visitor->visit (this); 
}
 
void 
MemCell::acceptVisitor (FormulaVisitor *visitor)
{
  visitor->visit (this); 
}
 
void 
RegisterExpr::acceptVisitor (FormulaVisitor *visitor)
{
  visitor->visit (this); 
}
 
			/* --------------- */

void 
Constant::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this); 
}
 
void 
Variable::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this); 
}
 
void 
UnaryApp::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this); 
}
 
void 
BinaryApp::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this); 
}
 
void 
TernaryApp::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this); 
}
 
void 
MemCell::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this); 
}
 
void 
RegisterExpr::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this); 
}
 

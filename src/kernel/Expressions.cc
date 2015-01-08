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

#include <kernel/Expressions.hh>

#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>
#include <kernel/expressions/ExprVisitor.hh>
#include <kernel/expressions/ExprSolver.hh>
#include <io/expressions/expr-writer.hh>
#include <utils/tools.hh>
#include <utils/bv-manip.hh>
#include <utils/logs.hh>
#include <utils/unordered11.hh>

#include <cassert>
#include <cstdio>
#include <cstring>

using namespace std;

Expr::ExprStore *Expr::expr_store = NULL;
bool Expr::non_empty_store_abort = false;
const string Expr::NON_EMPTY_STORE_ABORT_PROP =
  "kernel.expr.non-empty-store-abort";


Expr::Expr(int bv_offset, int bv_size)
  : bv_offset(bv_offset), bv_size(bv_size), refcount(0)
{
}

Expr::~Expr()
{
}

Expr *
Expr::createLNot (Expr *arg1)
{
  return UnaryApp::create (BV_OP_NOT, (Expr *) arg1, 0, 1);
}


Expr *
Expr::createImplies (Expr *A, Expr *B)
{
  assert (A->get_bv_size () == B->get_bv_size ());

  return createLOr (createLNot (A), B);
}

Expr *
Expr::createIfThenElse (Expr *cond, Expr *A, Expr *B)
{
  assert (A->get_bv_size () == B->get_bv_size ());
  return createLOr (createLAnd (cond->ref (), A),
		    createLAnd (createLNot (cond), B));
}

Expr *
Expr::createEquality (Expr *A, Expr *B)
{
  assert (A->get_bv_size () == B->get_bv_size ());
  return BinaryApp::create (BV_OP_EQ, A, B, 0, 1);
}

Expr *
Expr::createDisequality (Expr *A, Expr *B)
{
  assert (A->get_bv_size () == B->get_bv_size ());
  return BinaryApp::create (BV_OP_NEQ, A, B, 0, 1);
}

Expr *
Expr::createLAnd (Expr *A, Expr *B)
{
  assert (A->get_bv_size () == B->get_bv_size ());
  return BinaryApp::create (BV_OP_AND, A, B, 0, 1);
}

Expr *
Expr::createLOr (Expr *A, Expr *B)
{
  assert (A->get_bv_size () == B->get_bv_size ());
  return BinaryApp::create (BV_OP_OR,  A, B, 0, 1);
}

Expr *
Expr::createExtend (BinaryOp op, Expr *A, int newsize)
{
  assert (A->get_bv_size () <= newsize);
  assert (op == BV_OP_EXTEND_S || op == BV_OP_EXTEND_U);
  return BinaryApp::create (op, A,
			    Constant::create (newsize, 0,
					      Expr::get_bv_default_size()),
			    0, newsize);
}

Expr *
Expr::createExtract (Expr *A, int offset, int size)
{
  assert (offset + size - 1 < A->get_bv_size ());
  return TernaryApp::create (BV_OP_EXTRACT, A,
			     Constant::create (offset, 0,
					       Expr::get_bv_default_size()),
			     Constant::create (size, 0,
					       Expr::get_bv_default_size()),
			     0, size);
}

Expr *
Expr::createConcat (Expr *A, Expr *B)
{
  return BinaryApp::create (BV_OP_CONCAT, A, B, 0,
			    A->get_bv_size () + B->get_bv_size ());
}

Option<bool>
Expr::try_eval_level0() const
{
  Option<bool> result;

  if (is_TrueFormula ())
    result = Option<bool> (true);
  if (is_FalseFormula ())
    result = Option<bool> (false);
  else if (is_Constant ())
    {
      if (((Constant *)this)->get_val() == 0)
	result = Option<bool>(false);
      else
	result = Option<bool>(true);
    }
  return result;
}

bool
Expr::eval_level0() const
{
  try { return try_eval_level0().getValue(); }
  catch (OptionNoValueExc &) { return false; }
}


/*****************************************************************************/

int Expr::bv_default_size = 32;

void Expr::set_bv_default_size(int bv_size)
{
  Expr::bv_default_size = bv_size;
}

int Expr::get_bv_default_size()
{
  return Expr::bv_default_size;
}

int Expr::get_bv_size() const
{
  return bv_size;
}

int Expr::get_bv_offset() const
{
  return bv_offset;
}

Expr *
Expr::extract_bit_vector (int new_bv_offset, int new_bv_size) const
{
  if (new_bv_offset == 0 && get_bv_size () == new_bv_size)
    return ref ();

  if (! is_Constant ()) {
    assert (0 <= new_bv_size && new_bv_size <= get_bv_size ());

    assert (0 <= new_bv_offset && new_bv_offset < get_bv_size ());
    assert (0 <= new_bv_offset + new_bv_size - 1 &&
	    new_bv_offset + new_bv_size - 1 < get_bv_size ());
  }

  Expr *result = change_bit_vector (get_bv_offset () + new_bv_offset,
				    new_bv_size);

  return result;
}

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
  Expr *tmp = e->extract_bit_vector (new_bv_offset, new_bv_size);
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

Variable::Variable(const std::string &id, size_in_bits_t size,
		   int bv_offset, int bv_size)
  : Expr (bv_offset, bv_size), id(id), size (size)
{
}

Variable::~Variable()
{
}

Variable *
Variable::create (const std::string &id, size_in_bits_t size)
{
  return find_or_add (new Variable (id, size, 0, size));
}

size_in_bits_t
Variable::get_size () const
{
  return size;
}

std::string
Variable::get_id() const
{
  return id;
}

Expr *
Variable::change_bit_vector (int new_bv_offset, int new_bv_size) const
{
  return Expr::createExtract (this->ref (), new_bv_offset, new_bv_size);
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
}

constant_t
Constant::get_not_truncated_value() const
{
  return val;
}

Expr *
Constant::change_bit_vector (int new_bv_offset, int new_bv_size) const
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
UnaryApp::change_bit_vector (int new_bv_offset, int new_bv_size) const
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
  assert (!(op == BV_OP_CONCAT || op == BV_OP_EXTEND_S ||
	    op == BV_OP_EXTEND_U || op == BV_OP_EQ  || op == BV_OP_NEQ ));
  assert (arg1->get_bv_size () == arg2->get_bv_size ());
  return BinaryApp::create (op, arg1, arg2, 0, arg1->get_bv_size ());
}

BinaryApp *
BinaryApp::create (BinaryOp op, Expr *arg1, int arg2)
{
  return BinaryApp::create (op, arg1,
			    Constant::create (arg2, 0, arg1->get_bv_size ()));
}

BinaryApp *
BinaryApp::create (BinaryOp op, Expr *arg1, Expr *arg2, int bv_offset,
		   int bv_size)
{
  assert ((op == BV_OP_CONCAT   || op == BV_OP_EXTEND_S ||
           op == BV_OP_EXTEND_U || op == BV_OP_EQ       ||
           op == BV_OP_NEQ )    ||
          arg1->get_bv_size () == arg2->get_bv_size ());

  return find_or_add (new BinaryApp (op, arg1, arg2, bv_offset, bv_size));
}

BinaryApp *
BinaryApp::create (BinaryOp op, Expr *arg1, int arg2,  int bv_offset,
		   int bv_size)
{
  return BinaryApp::create (op, arg1,
			    Constant::create (arg2, 0, arg1->get_bv_size ()),
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
BinaryApp::change_bit_vector (int new_bv_offset, int new_bv_size) const
{
  return BinaryApp::create (op, arg1->ref (), arg2->ref (), new_bv_offset,
			    new_bv_size);
}

/*****************************************************************************/
TernaryApp::TernaryApp(TernaryOp op, Expr *arg1, Expr *arg2, Expr *arg3,
		       int bv_offset, int bv_size)
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
TernaryApp::create (TernaryOp op, Expr *arg1, Expr *arg2, Expr *arg3,
		    int bv_offset, int bv_size)
{
  //XXX: need to check bitvectors size here
  return find_or_add (new TernaryApp (op, arg1, arg2, arg3, bv_offset,
				      bv_size));
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
TernaryApp::change_bit_vector (int new_bv_offset, int new_bv_size) const
{
  //XXX: need to check bitvectors size here
  return TernaryApp::create (op, arg1->ref (), arg2->ref (), arg3->ref(),
			     new_bv_offset, new_bv_size);
}

TernaryApp::~TernaryApp()
{
  arg1->deref ();
  arg2->deref ();
  arg3->deref ();
}

//
// QUANTIFIED EXPR METHODS
//
QuantifiedExpr::QuantifiedExpr (bool exists_, Variable *var_, Expr *body_)
  : Expr (0, 1), exists (exists_), var (var_), body (body_)
{
}

QuantifiedExpr::~QuantifiedExpr()
{
  var->deref ();
  body->deref ();
}

bool
QuantifiedExpr::is_exists () const
{
  return exists;
}

Variable *
QuantifiedExpr::get_variable () const
{
  return var;
}

Expr *
QuantifiedExpr::get_body () const
{
  return body;
}

Expr *
QuantifiedExpr::change_bit_vector (int new_bv_offset, int new_bv_size) const
{
  assert (new_bv_size == 1 && new_bv_offset == 0);

  return QuantifiedExpr::create (exists, (Variable *) var->ref (),
				 body->ref ());
}

QuantifiedExpr *
QuantifiedExpr::create (bool exists, Variable *var, Expr *body)
{
  return find_or_add (new QuantifiedExpr (exists, var, body));
}

QuantifiedExpr *
QuantifiedExpr::createExists (Variable *var, Expr *body)
{
  return create (true, var, body);
}

QuantifiedExpr *
QuantifiedExpr::createForall (Variable *var, Expr *body)
{
  return create (false, var, body);
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
MemCell::change_bit_vector (int new_bv_offset, int new_bv_size) const
{
  return MemCell::create (addr->ref (), tag, new_bv_offset, new_bv_size);
}

/*****************************************************************************/

RegisterExpr::RegisterExpr(RegisterDesc *reg, int bv_offset, int bv_size)
  : LValue (bv_offset, bv_size), regdesc (reg)
{
  assert (! regdesc->is_alias ());
  regdesc->ref();
}

RegisterExpr::~RegisterExpr()
{
  regdesc->deref();
}

RegisterExpr *
RegisterExpr::create (RegisterDesc *reg)
{
  return create (reg, 0, reg->get_register_size ());
}

RegisterExpr *
RegisterExpr::create (RegisterDesc *reg, int bv_offset, int bv_size)
{
  RegisterExpr *tmp = new RegisterExpr (reg, bv_offset, bv_size);

  return find_or_add(tmp);
}

RegisterDesc *
RegisterExpr::get_descriptor () const {
  return regdesc;
}

const std::string &
RegisterExpr::get_name() const
{
  return regdesc->get_label ();
}

Expr *
RegisterExpr::change_bit_vector (int new_bv_offset, int new_bv_size) const
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

unsigned int RandomValue::get_depth() const
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
  if (op == BV_OP_CONCAT)
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

unsigned int QuantifiedExpr::get_depth() const
{
  return 1 + body->get_depth ();
}

/*****************************************************************************/

bool Variable::contains(const Expr *o) const
{
  return equal (o);
}

bool Constant::contains(const Expr *o) const
{
  return equal (o);
}

bool RandomValue::contains(const Expr *o) const
{
  return equal (o);
}

bool UnaryApp::contains (const Expr *o) const
{
  return equal (o) || arg1->contains(o);
}

bool BinaryApp::contains (const Expr *o) const
{
  return equal (o) || arg1->contains(o) || arg2->contains(o);
}

bool TernaryApp::contains (const Expr *o) const
{
  return equal(o) || arg1->contains(o) || arg2->contains(o)
      || arg3->contains(o);
}

bool MemCell::contains (const Expr *o) const
{
  return equal (o) || addr->contains(o);
}

bool RegisterExpr::contains (const Expr *o) const
{
  return equal (o);
}

bool QuantifiedExpr::contains (const Expr *o) const
{
  return equal (o) || var->contains (o) || body->contains (o);
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

bool Expr::is_RandomValue () const
{
  Expr *non_const_this = const_cast<Expr *>(this);
  return dynamic_cast<RandomValue *>(non_const_this);
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

bool
Expr::is_DisjunctiveFormula () const
{
  const BinaryApp *ba = dynamic_cast<const BinaryApp *>(this);

  return ba != NULL && ba->get_op () == BV_OP_OR && ba->get_bv_size () == 1;
}

bool
Expr::is_ConjunctiveFormula () const
{
  const BinaryApp *ba = dynamic_cast<const BinaryApp *>(this);

  return ba != NULL && ba->get_op () == BV_OP_AND && ba->get_bv_size () == 1;
}

bool
Expr::is_NegationFormula () const
{
  const UnaryApp *ua = dynamic_cast<const UnaryApp *>(this);

  return ua != NULL && ua->get_op() == BV_OP_NOT && ua->get_bv_size () == 1;
}

bool
Expr::is_QuantifiedFormula () const
{
  const QuantifiedExpr *ua = dynamic_cast<const QuantifiedExpr *>(this);

  return ua != NULL;
}

bool
Expr::is_ExistentialFormula () const
{
  const QuantifiedExpr *qe = dynamic_cast<const QuantifiedExpr *>(this);

  return qe != NULL && qe->is_exists ();
}

bool
Expr::is_UniversalFormula () const
{
  const QuantifiedExpr *qe = dynamic_cast<const QuantifiedExpr *>(this);

  return qe != NULL && ! qe->is_exists ();
}

bool
Expr::is_TrueFormula () const
{
  const Constant *bcf = dynamic_cast<const Constant *>(this);

  return bcf != NULL && (bcf->get_bv_size () == 1) && bcf->get_val ();
}

bool
Expr::is_FalseFormula () const
{
  const Constant *bcf = dynamic_cast<const Constant *>(this);

  return bcf != NULL && (bcf->get_bv_size () == 1) && ! bcf->get_val ();
}

/*****************************************************************************/

bool
Variable::has_type_of (const Expr *F) const
{
  return dynamic_cast<const Variable *>(F);
}

bool
Constant::has_type_of (const Expr *F) const
{
  return dynamic_cast<const Constant *>(F);
}

bool
RandomValue::has_type_of (const Expr *F) const
{
  return dynamic_cast<const RandomValue *>(F);
}

bool
UnaryApp::has_type_of (const Expr *F) const
{
  return dynamic_cast<const UnaryApp *>(F);
}

bool
BinaryApp::has_type_of (const Expr *F) const
{
  return dynamic_cast<const BinaryApp *>(F);
}

bool
TernaryApp::has_type_of (const Expr *F) const
{
  return dynamic_cast<const TernaryApp *>(F);
}

bool
MemCell::has_type_of (const Expr *F) const
{
  return dynamic_cast<const MemCell *>(F);
}

bool
RegisterExpr::has_type_of (const Expr *F) const
{
  return dynamic_cast<const RegisterExpr *>(F);
}

bool
QuantifiedExpr::has_type_of (const Expr *F) const
{
  return dynamic_cast<const QuantifiedExpr *>(F);
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
s_check_bv (const T *t, const Expr *F)
{
  const T *e = dynamic_cast<const T *> (F);

  if (e != NULL &&
      t->get_bv_offset () == e->get_bv_offset () &&
      t->get_bv_size () == e->get_bv_size ())
    return e;

  return NULL;
}

bool Variable::equal (const Expr *F) const
{
  const Variable *e = s_check_bv<Variable> (this, F);

  return (e != NULL && id == e->id && size == e->size);
}

bool Constant::equal (const Expr *F) const
{
  const Constant *e = s_check_bv<Constant> (this, F);

  return (e != NULL && val == e->val);
}

bool
RandomValue::equal (const Expr *F) const
{
  const RandomValue *e = s_check_bv<RandomValue> (this, F);

  return (e != NULL && e == this);
}

bool UnaryApp::equal (const Expr *F) const
{
  const UnaryApp *e = s_check_bv<UnaryApp> (this, F);

  return (e != NULL && op == e->op && arg1 == e->arg1);
}

bool BinaryApp::equal (const Expr *F) const
{
  const BinaryApp *e = s_check_bv<BinaryApp> (this, F);

  return (e != NULL && op == e->op && arg1 == e->arg1 && arg2 == e->arg2);
}

bool TernaryApp::equal(const Expr *F) const
{
  const TernaryApp *e = s_check_bv<TernaryApp> (this, F);

  return (e != NULL && op == e->op && arg1 == e->arg1 && arg2 == e->arg2
      && arg3 == e->arg3);
}

bool MemCell::equal (const Expr *F) const
{
  const MemCell *e = s_check_bv<MemCell> (this, F);

  return (e != NULL && tag == e->tag && addr == e->addr);
}

bool RegisterExpr::equal (const Expr *F) const
{
  const RegisterExpr *e = s_check_bv<RegisterExpr> (this, F);

  return (e != NULL && e->regdesc == regdesc);
}

bool QuantifiedExpr::equal (const Expr *F) const
{
  const QuantifiedExpr *e = s_check_bv<QuantifiedExpr> (this, F);

  return (e != NULL && e->exists == exists && e->var == var && e->body == body);
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
  return (13 * this->Expr::hash() + 51 * std::hash<string>()(id) +
	  73 * size);
}

size_t
RandomValue::hash () const
{
  return this->Expr::hash ();
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
  return (13 * this->Expr::hash() + 19 * std::hash<string>()(tag) +
	  111 * addr->hash ());
}

size_t
RegisterExpr::hash () const
{
  return 13 * this->Expr::hash() + regdesc->hashcode ();
}

size_t
QuantifiedExpr::hash () const
{
  return (exists ? 111 :149) * var->hash () + body->hash ();
}


/*****************************************************************************/

void
Expr::output_text (std::ostream &out) const
{
  expr_writer (out, this);
}

/*****************************************************************************/


void
Expr::acceptVisitor (ExprVisitor &visitor)
{
  acceptVisitor (&visitor);
}

void
Expr::acceptVisitor (ConstExprVisitor &visitor) const
{
  acceptVisitor (&visitor);
}


void
Constant::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
RandomValue::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
Variable::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
UnaryApp::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
BinaryApp::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
TernaryApp::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
MemCell::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
RegisterExpr::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

void
QuantifiedExpr::acceptVisitor (ExprVisitor *visitor)
{
  visitor->visit (this);
}

			/* --------------- */

void
Constant::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
RandomValue::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
Variable::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
UnaryApp::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
BinaryApp::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
TernaryApp::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
MemCell::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
RegisterExpr::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
QuantifiedExpr::acceptVisitor (ConstExprVisitor *visitor) const
{
  visitor->visit (this);
}

void
Expr::init (const ConfigTable &cfg)
{
  non_empty_store_abort =
    cfg.get_boolean (NON_EMPTY_STORE_ABORT_PROP, false);

  expr_store = new ExprStore (100);
  ExprSolver::init (cfg);
}

void
Expr::terminate ()
{
  ExprSolver::terminate ();
  if (Expr::expr_store == NULL)
    return;
  bool abortion = (Expr::expr_store->size () > 0) && non_empty_store_abort;
  if (Expr::expr_store->size () > 0)
    {
      logs::error << "**** some exprs have not been deleted:" << endl;
      dumpStore ();
    }
  delete Expr::expr_store;
  Expr::expr_store = NULL;
  if (abortion)
    abort ();
}

void
Expr::dumpStore ()
{
  int nb = Expr::expr_store->size ();
  ExprStore::iterator i = Expr::expr_store->begin ();
  ExprStore::iterator end = Expr::expr_store->end ();
  for (; i != end; i++, nb--)
    {
      assert (nb > 0);
      logs::error << *i << ": "
		 << *(*i) << " [refcount =" << (*i)->refcount << "]" << endl;
    }
}

//
// EXPR SHARING
//

size_t
Expr::Hash::operator()(const Expr *const &F) const
{
  return F->hash ();
}

bool
Expr::Equal::operator()(const Expr *const &F1, const Expr * const &F2) const
{
  return F1->equal (F2);
}

Expr *
Expr::ref () const
{
  assert (refcount > 0);

  refcount++;
  return (Expr *) this;
}

void
Expr::deref ()
{
  assert (refcount > 0);
  refcount--;
  if (refcount == 0)
    {
      assert (expr_store->find (this) != expr_store->end ());
      expr_store->erase (this);

      delete this;
    }
}

Expr *
Expr::find_or_add_expr (Expr *F)
{
  ExprStore::iterator i = expr_store->find (F);
  assert (F->refcount == 0);

  if (i == expr_store->end ())
    {
      expr_store->insert (F);
      F->refcount = 1;
    }
  else
    {
      if (F != *i)
	delete F;
      F = *i;
      F->ref ();
    }

  return F;
}


RandomValue::RandomValue (int bv_size)
  : Expr (0, bv_size)
{
}

RandomValue::~RandomValue()
{
}

Expr *
RandomValue::change_bit_vector (int new_bv_offset, int new_bv_size) const
{
  assert (new_bv_offset == 0);

  return new RandomValue (new_bv_size);
}

RandomValue *
RandomValue::create (int bv_size)
{
  RandomValue *tmp = new RandomValue (bv_size);

  return find_or_add(tmp);

}





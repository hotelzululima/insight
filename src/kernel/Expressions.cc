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

#include <kernel/Expressions.hh>

#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>
#include <tr1/unordered_map>
#include <tr1/unordered_map>
#include <kernel/expressions/Formula.hh>
#include <kernel/expressions/FormulaVisitor.hh>
#include <utils/tools.hh>
#include <utils/bv-manip.hh>
#include <utils/infrastructure.hh>

#include <cassert>
#include <cstdio>
#include <cstring>

using namespace std;


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
Expr::extract_bit_vector (int new_bv_offset, int new_bv_size) const
{
  if (new_bv_offset == 0 && get_bv_size () == new_bv_size)
    return ref ();

  assert (0 <= new_bv_size && new_bv_size <= get_bv_size ());

  assert (0 <= new_bv_offset && new_bv_offset < get_bv_size ());
  assert (0 <= new_bv_offset + new_bv_size - 1 && 
	  new_bv_offset + new_bv_size - 1 < get_bv_size ());
  
  Expr *result = change_bit_vector (get_bv_offset () + new_bv_offset, new_bv_size);

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
Variable::change_bit_vector (int new_bv_offset, int new_bv_size) const 
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
  return BinaryApp::create (op, arg1, arg2, 0);
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
  return find_or_add (new BinaryApp (op, arg1, arg2, bv_offset, bv_size));
}

BinaryApp *
BinaryApp::create (BinaryOp op, Expr *arg1, int arg2, int bv_offset, 
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
TernaryApp::change_bit_vector (int new_bv_offset, int new_bv_size) const
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
MemCell::change_bit_vector (int new_bv_offset, int new_bv_size) const 
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
  return 13 * this->Expr::hash() + 51 * std::tr1::hash<string>()(id);
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
  return (13 * this->Expr::hash() + 19 * std::tr1::hash<string>()(tag) +
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
 

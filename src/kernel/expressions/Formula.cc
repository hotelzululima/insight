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
#include <kernel/expressions/Formula.hh>

#include <cassert>
#include <iostream>
#include <sstream>
#include <typeinfo>

#include <kernel/Expressions.hh>
#include <kernel/expressions/FormulaVisitor.hh>

using namespace std;

void 
Formula::init ()
{
  formula_store = new FormulaStore (100);
}

void 
Formula::terminate () 
{
  if (Formula::formula_store == NULL)
    return;
   
  if (Formula::formula_store->size () > 0)
    {      
      int nb = Formula::formula_store->size ();
      FormulaStore::iterator i = Formula::formula_store->begin ();
      FormulaStore::iterator end = Formula::formula_store->end ();
      cerr << "**** some formulas have not been deleted:" << endl;
      for (; i != end; i++, nb--)
	{
	  assert (nb > 0);
	  cerr << "**** refcount = " << (*i)->refcount 
	       << " formula = " << (*i)->pp () << endl;
	}
	  
    }
  delete Formula::formula_store;
  Formula::formula_store = NULL;
}

void 
Formula::dumpStore ()
{
  int nb = Formula::formula_store->size ();
  FormulaStore::iterator i = Formula::formula_store->begin ();
  FormulaStore::iterator end = Formula::formula_store->end ();
  for (; i != end; i++, nb--)
    {
      assert (nb > 0);
      cerr << (*i)->pp () << endl;
    }
}

/*****************************************************************************/
// Constructors
/*****************************************************************************/
Formula::Formula() : refcount(0) {}

NaryBooleanFormula::NaryBooleanFormula (Formula *op)
{
  ops.push_back (op);
}

NaryBooleanFormula::NaryBooleanFormula (Formula *op1, Formula *op2)
{
  ops.push_back (op1);
  ops.push_back (op2);
}

NaryBooleanFormula::NaryBooleanFormula (const Operands &args) 
  : Formula (), ops (args) 
{
}

ConjunctiveFormula::ConjunctiveFormula (Formula *op1, Formula *op2)
  : NaryBooleanFormula (op1, op2)
{
}

ConjunctiveFormula::ConjunctiveFormula (const Operands &args) 
  : NaryBooleanFormula (args) 
{
}

ConjunctiveFormula *
ConjunctiveFormula::create (Formula *A, Formula *B)
{
  Operands ops;
  ops.push_back (A);
  ops.push_back (B);

  return find_or_add (new ConjunctiveFormula (ops));
}

ConjunctiveFormula *
ConjunctiveFormula::create (const Operands &args)
{
  return find_or_add (new ConjunctiveFormula (args));
}

NaryBooleanFormula *
ConjunctiveFormula::create_from_operands (const Operands &ops) const
{
  return create (ops);
}

DisjunctiveFormula::DisjunctiveFormula (Formula *op1, Formula *op2)
  : NaryBooleanFormula (op1, op2)
{
}

DisjunctiveFormula::DisjunctiveFormula (const Operands &args) 
  : NaryBooleanFormula (args) 
{
}

DisjunctiveFormula *
DisjunctiveFormula::create (Formula *A, Formula *B)
{
  Operands ops;
  ops.push_back (A);
  ops.push_back (B);

  return find_or_add (new DisjunctiveFormula (ops));
}

DisjunctiveFormula * 
DisjunctiveFormula::create (const std::vector<Formula *> &args)
{
  return find_or_add (new DisjunctiveFormula (args));
}

NaryBooleanFormula *
DisjunctiveFormula::create_from_operands (const Operands &ops) const
{
  return create (ops);
}

NegationFormula::NegationFormula (Formula *phi)
  : NaryBooleanFormula (phi)
{
}

NegationFormula * 
NegationFormula::create (Formula *phi)
{
  return find_or_add (new NegationFormula (phi));
}

NaryBooleanFormula *
NegationFormula::create_from_operands (const Operands &ops) const
{
  return create (ops[0]);
}

QuantifiedFormula::QuantifiedFormula (bool exist, Variable *var, Formula *phi)
  : NaryBooleanFormula (var, phi), exist (exist)
{
}

QuantifiedFormula * 
QuantifiedFormula::create (bool exist, Variable *var, Formula *phi)
{
  return find_or_add (new QuantifiedFormula (exist, var, phi));
}

QuantifiedFormula * 
QuantifiedFormula::createE (Variable *var, Formula *phi)
{
  return create (true, var, phi);
}

QuantifiedFormula * 
QuantifiedFormula::createA (Variable *var, Formula *phi)
{
  return create (false, var, phi);
}

NaryBooleanFormula *
QuantifiedFormula::create_from_operands (const Operands &ops) const
{
  return create (exist, (Variable *) ops[0], ops[1]);
}

/*****************************************************************************/
/* Destructor                                                                */
/*****************************************************************************/

Formula::~Formula() {}

NaryBooleanFormula::~NaryBooleanFormula () 
{  
  for (OperandsIterator it = ops.begin(); it != ops.end(); it++)
    (*it)->deref ();
}

ConjunctiveFormula::~ConjunctiveFormula() 
{
}

DisjunctiveFormula::~DisjunctiveFormula() 
{
}

NegationFormula::~NegationFormula() 
{
}

QuantifiedFormula::~QuantifiedFormula ()
{
}

/*****************************************************************************/

bool Formula::is_Expr() const
{
  Formula *non_const_this = const_cast<Formula *>(this);
  return dynamic_cast<Expr *>(non_const_this);
}

bool Formula::is_AtomicFormula() const
{
  Formula *non_const_this = const_cast<Formula *>(this);
  return dynamic_cast<AtomicFormula *>(non_const_this);
}

bool Formula::is_ConjunctiveFormula() const
{
  Formula *non_const_this = const_cast<Formula *>(this);
  return dynamic_cast<ConjunctiveFormula *>(non_const_this);
}

bool Formula::is_DisjunctiveFormula() const
{
  Formula *non_const_this = const_cast<Formula *>(this);
  return dynamic_cast<DisjunctiveFormula *>(non_const_this);
}

bool Formula::is_NegationFormula() const
{
  Formula *non_const_this = const_cast<Formula *>(this);
  return dynamic_cast<NegationFormula *>(non_const_this);
}

bool Formula::is_QuantifiedFormula () const
{
  const QuantifiedFormula *bcf = 
    dynamic_cast<const QuantifiedFormula *>(this);
  return bcf != NULL;
}

bool Formula::is_ExistentialFormula() const
{
  const QuantifiedFormula *bcf = 
    dynamic_cast<const QuantifiedFormula *>(this);
  return bcf != NULL && bcf->is_exist ();
}

bool Formula::is_UniversalFormula() const
{
  const QuantifiedFormula *bcf = 
    dynamic_cast<const QuantifiedFormula *>(this);
  return bcf != NULL && ! bcf->is_exist ();
}

bool Formula::is_TrueFormula() const
{
  const Constant *bcf = 
    dynamic_cast<const Constant *>(this);
  return bcf != NULL && (bcf->get_bv_size () == 1) && bcf->get_val ();
}

bool Formula::is_FalseFormula() const
{
  const Constant *bcf = 
    dynamic_cast<const Constant *>(this);
  return bcf != NULL && (bcf->get_bv_size () == 1) && ! bcf->get_val ();
}

/*****************************************************************************/

bool ConjunctiveFormula::has_type_of(const Formula *F) const
{
  return dynamic_cast<const ConjunctiveFormula *>(F);
}

bool DisjunctiveFormula::has_type_of(const Formula *F) const
{
  return dynamic_cast<const DisjunctiveFormula *>(F);
}

bool NegationFormula::has_type_of(const Formula *F) const
{
  return dynamic_cast<const NegationFormula *>(F);
}

bool QuantifiedFormula::has_type_of(const Formula *F) const
{
  return dynamic_cast<const QuantifiedFormula *>(F);
}

/*****************************************************************************/
/* Accessors                                                                 */
/*****************************************************************************/

NaryBooleanFormula::Operands 
NaryBooleanFormula::get_operands_copy() const 
{
  Operands result;

  for (OperandsConstIterator it = ops.begin(); it != ops.end(); it++)
    result.push_back ((Formula *) (*it)->ref ());
  
  return result;
}

const NaryBooleanFormula::Operands &
NaryBooleanFormula::get_operands() const
{
  return ops;
}

const vector<Formula *> & ConjunctiveFormula::get_clauses() const
{
  return get_operands ();
}

vector<Formula *> ConjunctiveFormula::get_clauses_copy() const
{
  return get_operands_copy ();
}

const vector<Formula *> & DisjunctiveFormula::get_clauses() const
{
  return get_operands ();
}

vector<Formula *> DisjunctiveFormula::get_clauses_copy() const
{
  return get_operands_copy ();
}

const Formula *NegationFormula::get_neg() const
{
  return get_operands ().at (0);
}

bool 
QuantifiedFormula::is_exist () const 
{
  return exist;
}

const Variable *
QuantifiedFormula::get_variable() const
{
  return (const Variable *) get_operands().at (0);
}

const Formula *
QuantifiedFormula::get_body() const
{
  return get_operands().at (1);
}

/*****************************************************************************/
/* Syntactic Equality                                                        */
/*****************************************************************************/

bool 
NaryBooleanFormula::equal (const Formula *F) const 
{
  if (! has_type_of (F))
    return false;
  
  const NaryBooleanFormula *nbf = dynamic_cast<const NaryBooleanFormula *> (F);
  if (ops.size() != nbf->ops.size ())
    return false;
  
  OperandsConstIterator it1 = ops.begin();
  OperandsConstIterator it2 = nbf->ops.begin();
  for (; it1 != ops.end (); it1++, it2++)
    {
      if (! (*it1 == *it2))
	return false;
    }
  return true;
}

bool 
QuantifiedFormula::equal (const Formula *F) const 
{  
  return (this->NaryBooleanFormula::equal (F) && 
	  exist == ((QuantifiedFormula *) F)->exist);
}

/*****************************************************************************/
/* Hash                                                                      */
/*****************************************************************************/

size_t 
Formula::hash () const
{
  return std::tr1::hash<const char*>()(typeid(*this).name());
}

size_t 
NaryBooleanFormula::hash () const 
{
  size_t result = this->Formula::hash ();
  OperandsConstIterator f = ops.begin();
  for (; f != ops.end(); f++)
    result = (result << 3) + 111 * (*f)->hash ();
    
  return result;
}

size_t
QuantifiedFormula::hash () const
{
  size_t result = exist ? 111 : 113;

  result *= this->NaryBooleanFormula::hash ();

  return result;
}

/*****************************************************************************/

Option<bool> Formula::try_eval_level0() const
{
  if (this->is_TrueFormula()) return Option<bool>(true);
  if (this->is_FalseFormula()) return Option<bool>(false);

  if (!this->is_Expr()) return Option<bool>();
  if (!((Expr *) this)->is_Constant()) return Option<bool>();

  if (((Constant *)this)->get_val() == 0) return Option<bool>(false);
  else return Option<bool>(true);
}

bool Formula::eval_level0() const
{
  try { return try_eval_level0().getValue(); }
  catch (OptionNoValueExc &) { return false; }
}

/*****************************************************************************/
// Formula Construction
/*****************************************************************************/

Formula *Formula::implies(Formula *A, Formula *B)
{
  return DisjunctiveFormula::create (NegationFormula::create (A), B);
}

Formula *Formula::IfThenElse(Formula *cond, Formula *A, Formula *B)
{
  return 
    DisjunctiveFormula::create (ConjunctiveFormula::create (cond, A),
				ConjunctiveFormula::create (NegationFormula::create ((Formula *) cond->ref ()), B)
         );
}

Formula *Formula::Equality(Expr *A, Expr *B)
{
  return BinaryApp::create (EQ, A, B);
}

Formula *Formula::add_conjunctive_clause(Formula *c) const
{
  if (this->is_ConjunctiveFormula())
    {      
      vector<Formula *> clauses = 
	((ConjunctiveFormula *)this)->get_clauses_copy ();
      clauses.push_back (c);

      return ConjunctiveFormula::create (clauses);
    }
  else
    {
      return ConjunctiveFormula::create ((Formula *) this->ref (), c);
    }
}

/*! \brief add a new conjunctive clause to the current formula in place, caution c is not copied */
void Formula::add_conjunctive_clause(Formula **phi, Formula *c)
{
  Formula *new_phi = (*phi)->add_conjunctive_clause(c);
  (*phi)->deref ();
  *phi = new_phi;
}

Formula *Formula::add_disjunctive_clause(Formula *c) const
{
  if (this->is_DisjunctiveFormula())
    {
      vector<Formula *> clauses = 
	((DisjunctiveFormula *)this)->get_clauses_copy ();

      clauses.push_back (c);

      return DisjunctiveFormula::create (clauses);
    }
  else
    {
      return DisjunctiveFormula::create ((Formula *) this->ref (), c);
    }
}

/*! \brief add a new disjunctive clause to the current formula in place, caution c is not copied */
void Formula::add_disjunctive_clause(Formula **phi, Formula *c)
{
  Formula *new_phi = (*phi)->add_disjunctive_clause(c);
  (*phi)->deref ();
  *phi = new_phi;
}

/*****************************************************************************/
/* Pretty Printing                                                           */
/*****************************************************************************/

#define FORMULA_TAB "    "

string 
Formula::to_string () const 
{
  return pp ("");
}

static string 
pp_NaryBooleanFormula (std::string prefix, const char *opstr, const char *sep, 
		       const NaryBooleanFormula::Operands &operands)
{
  NaryBooleanFormula::OperandsConstIterator phi = operands.begin();
  NaryBooleanFormula::OperandsConstIterator end = operands.end();
  ostringstream oss;
  oss << prefix << "(" << opstr << " ";
  for (; phi != end; phi++)
    oss << sep << endl << (*phi)->pp (prefix + string(FORMULA_TAB));
  oss << ")";

  return oss.str();
}

string ConjunctiveFormula::pp(std::string prefix) const
{
  return pp_NaryBooleanFormula (prefix, "LAND", "", get_operands ());
}

string DisjunctiveFormula::pp(std::string prefix) const
{
  return pp_NaryBooleanFormula (prefix, "LOR", "", get_operands ());
}

string NegationFormula::pp(std::string prefix) const
{
  return pp_NaryBooleanFormula (prefix, "LNOT", "", get_operands ());
}

string QuantifiedFormula::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix;
  oss << "(FORALL " << get_variable ()->pp () << " . " << endl;
  oss << get_body () ->pp (prefix + string(FORMULA_TAB)) << ")";

  return oss.str();
}

//
// FORMULA SHARING
//

size_t 
Formula::Hash::operator()(const Formula *const &F) const 
{
  return F->hash ();
}

bool 
Formula::Equal::operator()(const Formula *const &F1, 
			   const Formula * const &F2) const
{  
  return F1->equal (F2);
}


Formula::FormulaStore *Formula::formula_store = NULL;

Formula *
Formula::ref () const
{ 
  assert (refcount > 0);

  refcount++; 
  return (Formula *) this;
}

void 
Formula::deref () 
{ 
  assert (refcount > 0);
  refcount--; 
  if (refcount == 0) 
    {
      assert (formula_store->find (this) != formula_store->end ());
      formula_store->erase (this);

      delete this; 
    }
}

Formula *
Formula::find_or_add_formula (Formula *F)
{
  FormulaStore::iterator i = formula_store->find (F);
  assert (F->refcount == 0);

  if (i == formula_store->end ())
    {
      formula_store->insert (F);
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

//
// VISITORS 
//

void 
Formula::acceptVisitor (FormulaVisitor &visitor)
{
  acceptVisitor (&visitor);
}

void 
Formula::acceptVisitor (ConstFormulaVisitor &visitor) const
{
  acceptVisitor (&visitor);
}

void 
ConjunctiveFormula::acceptVisitor (FormulaVisitor *visitor) 
{
  visitor->visit (this);
}

void 
QuantifiedFormula::acceptVisitor (FormulaVisitor *visitor) 
{
  visitor->visit (this);
}

void 
DisjunctiveFormula::acceptVisitor (FormulaVisitor *visitor) 
{
  visitor->visit (this);
}

void 
NegationFormula::acceptVisitor (FormulaVisitor *visitor) 
{
  visitor->visit (this);
}

			/* --------------- */

void 
ConjunctiveFormula::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this);
}

void 
QuantifiedFormula::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this);
}

void 
DisjunctiveFormula::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this);
}

void 
NegationFormula::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this);
}

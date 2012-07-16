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

#include <map>
#include <list>
#include <typeinfo>
#include <sstream>
#include <iostream>
#include <ext/hash_map>
#include <utils/infrastructure.hh>
#include <utils/tools.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/PatternMatching.hh>
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

BooleanConstantFormula::BooleanConstantFormula (bool val) : value (val)
{
}

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

BooleanConstantFormula *
BooleanConstantFormula::create (bool value)
{
  return find_or_add (new BooleanConstantFormula (value));
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

BooleanConstantFormula::~BooleanConstantFormula()
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

bool Formula::is_BooleanConstantFormula() const
{
  const BooleanConstantFormula *bcf = 
    dynamic_cast<const BooleanConstantFormula *>(this);
  return bcf != NULL;
}

bool Formula::is_TrueFormula() const
{
  const BooleanConstantFormula *bcf = 
    dynamic_cast<const BooleanConstantFormula *>(this);
  return bcf != NULL && bcf->get_value ();
}

bool Formula::is_FalseFormula() const
{
  const BooleanConstantFormula *bcf = 
    dynamic_cast<const BooleanConstantFormula *>(this);
  return bcf != NULL && ! bcf->get_value ();
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

bool BooleanConstantFormula::has_type_of(const Formula *F) const
{
  return dynamic_cast<const BooleanConstantFormula *>(F);
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
BooleanConstantFormula::get_value () const 
{
  return value;
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

bool BooleanConstantFormula::equal (const Formula *e) const
{
  const BooleanConstantFormula *bcf = 
    dynamic_cast<const BooleanConstantFormula *> (e);
  return bcf != NULL && value == bcf->get_value ();
}

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
  return __gnu_cxx::hash<const char*>()(typeid(*this).name());
}

size_t
BooleanConstantFormula::hash () const
{
  return this->Formula::hash () + value ? 113 : 77;
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
/* Bottom Up Replacing                                                       */
/*****************************************************************************/

Formula *
BooleanConstantFormula::bottom_up_apply (FormulaReplacingRule *r) const
  throw (NotApplicable)
{
  return r->f(this);
}

Formula *
NaryBooleanFormula::bottom_up_apply (FormulaReplacingRule *r) const
  throw (NotApplicable)
{
  bool applied = false;
  Operands new_ops;

  for (OperandsConstIterator it = ops.begin(); it != ops.end(); it++)
    {
      Formula *new_f;

      try
	{
	  new_f = (*it)->bottom_up_apply (r);
	  applied = true;
	}
      catch (NotApplicable &) 
	{
	  new_f = (Formula *) (*it)->ref ();
	}
      new_ops.push_back (new_f);
    }
  
  Formula *tmp = create_from_operands (new_ops);
  Formula *result = NULL;

  try
    {
      result = r->f (tmp);
    }
  catch (NotApplicable &)
    {
      if (applied) 
	result = (Formula *) tmp->ref ();
    }
  tmp->deref ();

  if (result == NULL)
    throw NotApplicable();

  return result;
}

/*****************************************************************************/

bool Formula::bottom_up_apply_in_place(Formula **phi, FormulaReplacingRule *r)
{
  try
    {
      Formula *new_phi = (*phi)->bottom_up_apply (r);
      (*phi)->deref ();
      *phi = new_phi;
      return true;
    }
  catch (NotApplicable &)
    {
      return false;
    }
}

/*****************************************************************************/

class FormulaReplaceSubtermRule : public FormulaReplacingRule
{

public:
  const Formula *pattern;
  const Formula *value;

  Formula *f(const Formula *phi)
  {
    if (phi->is_Expr())
      {
        if (phi == pattern) 
	  return (Formula *) value->ref ();
      }
    return (Formula *) phi->ref ();
  }
};

Formula * 
Formula::replace_subterm (const Formula *pattern, const Formula *value) const
{
  FormulaReplaceSubtermRule r;
  r.pattern = pattern;
  r.value = value;
  return bottom_up_apply (&r);
}

/*****************************************************************************/

Formula * 
Formula::replace_variable (const Variable *v, const Formula *value) const
{
  FormulaReplaceSubtermRule r;
  r.pattern = v;
  r.value = value;
  return bottom_up_apply (&r);
}

Formula * 
Formula::replace_variable (string v_id, const Formula *value) const
{
  Variable *v = Variable::create (v_id);
  Formula *result = replace_variable (v, value);
  v->deref ();

  return result;
}

bool 
Formula::replace_variable_in_place(Formula **phi, const Variable *v, 
				   const Formula *value)
{
  FormulaReplaceSubtermRule r;
  r.pattern = v;
  r.value = value;
  try
    {
      Formula *new_phi = (*phi)->bottom_up_apply(&r);
      (*phi)->deref ();
      *phi = new_phi;
      return true;
    }
  catch (NotApplicable &)
    {
      return false;
    }
}

/*****************************************************************************/

class BURPRule : public FormulaReplacingRule
{
public:
  const Formula *pattern;
  std::list<const Variable *> free_variables;
  const Formula *value;

  Formula *f(const Formula *phi)
  {
    try
      {
	PatternMatching *vm = 
	  this->pattern->pattern_matching(phi, free_variables);
        Formula *value_cpy = (Formula *) this->value->ref ();
        for (PatternMatching::const_iterator p = vm->begin(); p != vm->end(); 
	     p++)
          Formula::replace_variable_in_place (&value_cpy, p->first, p->second);
	delete vm;

        return value_cpy;
      }
    catch (Formula::PatternMatchingFailure &)
      {
        throw NotApplicable();
      }
  }
};

bool Formula::bottom_up_rewrite_pattern(const Formula *pattern, 
					const std::list<const Variable *> &free_variables,
                                        const Formula *value,
                                        Formula **phi)
{

  BURPRule r;
  r.pattern = pattern;
  r.value = value;
  r.free_variables = free_variables;
  return Formula::bottom_up_apply_in_place(phi, &r);
}

/*****************************************************************************/

Formula * 
Formula::extract_v_pattern(std::string var_id, const Formula *phi) const
{
  Formula *result = NULL;
  Variable *v = Variable::create (var_id); 
  try
    {
      std::list<const Variable *> fv;
      fv.push_back(v);
      PatternMatching *vm = this->pattern_matching(phi, fv);
      if (vm->has (v))
	result = (Formula *) vm->get (v)->ref ();
      delete vm;
    }
  catch (Expr::PatternMatchingFailure &) {}      // TODO: PatternMatchingFailure should be defined somewhere else than in Expr  
  v->deref ();

  return result;
}


/*****************************************************************************/

PatternMatching *
BooleanConstantFormula::pattern_matching(const Formula *e, 
					 const std::list<const Variable *> &) const
{
  if (this == e)
    return new PatternMatching ();

  throw Expr::PatternMatchingFailure();
}

PatternMatching *
NaryBooleanFormula::pattern_matching(const Formula *e, 
				     const std::list<const Variable *> &free_variables) const
{
  if (! has_type_of (e))
    throw Expr::PatternMatchingFailure();
    
  Operands clause1 = get_operands ();
  Operands clause2 = ((NaryBooleanFormula *) e)->get_operands ();

  if (clause1.size() != clause2.size())
    throw Expr::PatternMatchingFailure();

  OperandsIterator c1 = clause1.begin();
  OperandsIterator c2 = clause2.begin();

  PatternMatching *matching = NULL;

  try
    {
      matching = (*c1)->pattern_matching(*c2, free_variables);
      for (c1++, c2++; c1 != clause1.end() && c2 != clause2.end(); c1++, c2++)
	{
	  PatternMatching *local_matching = 
	    (*c1)->pattern_matching(*c2, free_variables);
	  matching->merge (local_matching);
	  delete local_matching;
	}
    }
  catch (PatternMatchingFailure &)
    {
      if (matching != NULL)
	delete matching;
      throw;
    }
  
  return matching;
}

PatternMatching *
QuantifiedFormula::pattern_matching (const Formula *e, 
				     const std::list<const Variable *> &free_variables) const
{
  const QuantifiedFormula *qf = dynamic_cast<const QuantifiedFormula *> (e);

  if (qf == NULL || qf->is_exist () != is_exist ())
    throw Expr::PatternMatchingFailure();

  if (get_variable() != qf->get_variable())
    throw Expr::PatternMatchingFailure();

  return get_body()->pattern_matching (qf->get_body(), free_variables);
}

/*****************************************************************************/

class CollectMemCell : public FormulaReplacingRule
{
public:
  vector < MemCell * > mem_cells;
  Formula *f(const Formula *phi)
  {
    if (phi->is_Expr())
      if (((Expr *) phi)->is_MemCell())
        mem_cells.push_back((MemCell *) phi);
    return (Formula *) phi->ref ();
  }
};

vector<MemCell *> Formula::collect_all_memory_references() const
{
  CollectMemCell collector;
  bottom_up_apply (&collector);
  return collector.mem_cells;
}

/*****************************************************************************/
/* Simplification System                                                     */
/*****************************************************************************/

class RuleNotApplicableExc {};

/*****************************************************************************/
/* The following functions are rule of simplification of formula
 * They are applied in the Simplify0Rule class below and applied to terms
 * via the bottom up rewriting system. */
/*****************************************************************************/

/*! \brief Decide the syntaxic equality of two terms */
static Formula * 
SyntaxicEqualityRule(const Formula *phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_Expr())
    if (((Expr *) phi)->is_BinaryApp())
      {
        BinaryApp *ap = (BinaryApp *) phi;
        if (ap->get_op() == EQ)
          if (ap->get_arg1() == ap->get_arg2())
            return Constant::create (1);
      }

  throw RuleNotApplicableExc();
}

/*****************************************************************************/

/*! \brief Simplify Expression */
static Formula * 
ExpressionSimplify(const Formula * phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_Expr()) {
      Expr *e = ((Expr *) phi->ref ());
      // \todo optim la copie est peut-etre inutile
      if (Expr::simplify (&e))
	return e;
      e->deref ();
  }
  throw RuleNotApplicableExc();
}

/*****************************************************************************/

/*! \brief Compute the NOT operator on constant.
 *  \todo : Compute all constant operations. */
static Formula * 
NOTOperatorOnConstant(const Formula *phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_Expr())
    if (((Expr *) phi)->is_UnaryApp())
      {
        UnaryApp *un = (UnaryApp *) phi;
        if (un->get_op() == NOT)
          if (un->get_arg1()->is_Constant())
            {
              if (((Constant *) un->get_arg1())->get_val() == 0)
                return Constant::create (1);
              else
                return Constant::create (0);
            }
      }

  throw RuleNotApplicableExc();
}

/*****************************************************************************/

/*! \brief LNot Not Expr ---> Expr */
static Formula * 
Cancel_LNOT_NOT(const Formula *phi) 
  throw (RuleNotApplicableExc)
{
  Formula * pattern = 
    NegationFormula::create (UnaryApp::create(LNOT, Variable::create ("X")));
  Formula * result = pattern->extract_v_pattern("X", phi);
  pattern->deref ();
  if (result != NULL) 
    return result;
  
  throw RuleNotApplicableExc();
}

/*****************************************************************************/

/*! \brief Compute the Logical Negation operator on constant. */
static Formula * 
LogicNegationOperatorOnConstant(const Formula *phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_NegationFormula()) {
      try {
          if (((NegationFormula *) phi)->get_neg()->try_eval_level0().getValue())
            return Constant::create (0);
          else
            return Constant::create (1);
      }
      catch (OptionNoValueExc &) {}
  }

  throw RuleNotApplicableExc();
}

/*****************************************************************************/

/*! \brief Simplify the conjunctive formulae (checks which clauses can be computed) */
static Formula *
ConjunctionSimplification (const Formula *phi) 
  throw (RuleNotApplicableExc)
{
  if (phi->is_ConjunctiveFormula())
    {
      ConjunctiveFormula *conj = (ConjunctiveFormula *) phi;
      bool change = false;
      vector<Formula *> new_clauses;
      vector<Formula *>::const_iterator cl = conj->get_clauses().begin ();
      vector<Formula *>::const_iterator end_cl = conj->get_clauses().end ();

      for (; cl != end_cl; cl++)
        {
          if (find(new_clauses.begin(),
		   new_clauses.end(), *cl) != new_clauses.end())
            {
              change = true;  // Cheap optimization
              continue;
            }

          try
            {
              if ((*cl)->try_eval_level0().getValue())
                {
                  change = true;
                  continue;
                }
              else
                {
                  return Constant::create (0);
                }
            }
          catch (OptionNoValueExc &)   // eval_level0 did not work
            {
              new_clauses.push_back (*cl);
            }
        }

      if (change)
        {
          if (new_clauses.size() >= 2)
	    {
	      for(vector<Formula *>::iterator cl = new_clauses.begin ();
		  cl != new_clauses.end (); cl++)
		(*cl) = (Formula *) (*cl)->ref ();

	      return ConjunctiveFormula::create (new_clauses);
	    }

	  if (new_clauses.size() == 1)
            {
              return (Formula *) new_clauses[0]->ref ();
            }
          return Constant::create (1);
        }
    }

  throw RuleNotApplicableExc();
}


/*****************************************************************************/

/*! \brief Simplify the disjunctive formulae (checks which clauses can be computed) */
static Formula *
DisjunctionSimplification (const Formula *phi) 
  throw (RuleNotApplicableExc)
{
  if (phi->is_DisjunctiveFormula())
    {
      DisjunctiveFormula *conj = (DisjunctiveFormula *) phi;
      bool change = false;
      vector<Formula *> new_clauses;
      vector<Formula *>::const_iterator cl = conj->get_clauses().begin ();
      vector<Formula *>::const_iterator end_cl = conj->get_clauses().end ();

      for (; cl != end_cl; cl++)
        {
          if (find(new_clauses.begin(),
		   new_clauses.end(), *cl) != new_clauses.end())
            {
              change = true;  // Cheap optimization
              continue;
            }

          try
            {
              if ((*cl)->try_eval_level0().getValue())
                {
                  return Constant::create (1);
                }
              else
                {
                  change = true;
                  continue;
                }
            }
          catch (OptionNoValueExc &)
            {
              new_clauses.push_back (*cl);
            }
        }

      if (change)
        {
          if (new_clauses.size() >= 2)
	    {
	      for(vector<Formula *>::iterator cl = new_clauses.begin ();
		  cl != new_clauses.end (); cl++)
		(*cl) = (Formula *) (*cl)->ref ();

	      return DisjunctiveFormula::create (new_clauses);
	    }

          if (new_clauses.size() == 1)
            {
              return (Formula *) new_clauses[0]->ref ();
            }
          return Constant::create (0);
        }
    }

  throw RuleNotApplicableExc();
}

/*****************************************************************************/

static Formula *
AndAndRule (const Formula *phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_ConjunctiveFormula())
    {
      const vector<Formula *> &conj_clauses = 
	((ConjunctiveFormula *) phi)->get_clauses();
      vector<Formula *>::const_iterator psi = conj_clauses.begin();

      while (psi != conj_clauses.end() && !((*psi)->is_ConjunctiveFormula())) 
	psi++;
      if (psi != conj_clauses.end() && (*psi)->is_ConjunctiveFormula())
        {
	  vector<Formula *> new_clauses;     
	  ConjunctiveFormula *int_phi = (ConjunctiveFormula *) * psi;

          for (vector<Formula *>::const_iterator c = conj_clauses.begin(); 
	       c != conj_clauses.end(); c++) {
            if (c != psi)
	      new_clauses.push_back ((Formula *)(*c)->ref ());
	  }
          // TODO			((ConjunctiveFormula*) phi)->get_clauses().erase(psi);

          vector<Formula *> int_clauses = int_phi->get_clauses();
          for (vector<Formula *>::iterator c = int_clauses.begin(); 
	       c != int_clauses.end(); c++)
            new_clauses.push_back ((Formula *)(*c)->ref ());

          return ConjunctiveFormula::create (new_clauses);
        }
    }

  throw RuleNotApplicableExc();
}

static Formula * 
OrOrRule(const Formula *phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_DisjunctiveFormula())
    {
      const vector<Formula *> &conj_clauses = 
	((DisjunctiveFormula *) phi)->get_clauses();
      vector<Formula *>::const_iterator psi = conj_clauses.begin();

      while (psi != conj_clauses.end() && !((*psi)->is_DisjunctiveFormula())) 
	psi++;
      if (psi != conj_clauses.end() && (*psi)->is_DisjunctiveFormula())
        {
	  vector<Formula *> new_clauses;     
	  DisjunctiveFormula *int_phi = (DisjunctiveFormula *) * psi;

          for (vector<Formula *>::const_iterator c = conj_clauses.begin(); 
	       c != conj_clauses.end(); c++) {
            if (c != psi)
	      new_clauses.push_back ((Formula *)(*c)->ref ());
	  }
          // TODO			((DisjunctiveFormula*) phi)->get_clauses().erase(psi);

          vector<Formula *> int_clauses = int_phi->get_clauses();
          for (vector<Formula *>::iterator c = int_clauses.begin(); 
	       c != int_clauses.end(); c++)
            new_clauses.push_back ((Formula *)(*c)->ref ());

          return DisjunctiveFormula::create (new_clauses);
        }
    }

  throw RuleNotApplicableExc();
}

/*****************************************************************************/

static Formula * 
NotDecrease(const Formula *phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_NegationFormula())
    {
      const Formula *neg = ((NegationFormula *) phi)->get_neg();

      if (neg->is_NegationFormula())
        return (Formula *)((NegationFormula *) neg)->get_neg()->ref ();

      if (neg->is_ConjunctiveFormula())
        {
	  vector<Formula *> new_clauses;
	  vector<Formula *>::const_iterator c = 
	    ((ConjunctiveFormula *) neg)->get_clauses().begin ();
	  vector<Formula *>::const_iterator end = 
	    ((ConjunctiveFormula *) neg)->get_clauses().end ();

          for (; c != end; c++) {
	    Formula *cc = (Formula *)(*c)->ref ();
            new_clauses.push_back (NegationFormula::create (cc));
	  }

          return DisjunctiveFormula::create (new_clauses);
        }

      if (neg->is_DisjunctiveFormula())
        {
	  vector<Formula *> new_clauses;
	  vector<Formula *>::const_iterator c = 
	    ((DisjunctiveFormula *) neg)->get_clauses().begin ();
	  vector<Formula *>::const_iterator end = 
	    ((DisjunctiveFormula *) neg)->get_clauses().end ();

          for (; c != end; c++) {
	    Formula *cc = (Formula *)(*c)->ref ();
	    new_clauses.push_back (NegationFormula::create (cc));
	  }

          return ConjunctiveFormula::create (new_clauses);
        }
    }
  throw RuleNotApplicableExc();
}
/*****************************************************************************/

static Formula *
DisjunctiveNormalFormRule(const Formula *phi)
  throw (RuleNotApplicableExc)
{
  try
    {
      return NotDecrease(phi);
    }
  catch (RuleNotApplicableExc &) {}

  if (phi->is_ConjunctiveFormula())
    {
      const vector<Formula *> &conj_clauses = 
	((ConjunctiveFormula *) phi)->get_clauses();
      vector<Formula *>::const_iterator psi = conj_clauses.begin();

      while (psi != conj_clauses.end() && !((*psi)->is_DisjunctiveFormula())) 
	psi++;

      if (psi != conj_clauses.end() && (*psi)->is_DisjunctiveFormula())
        {
	  vector<Formula *> new_clauses;
          vector<Formula *> disj_clauses = 
	    ((DisjunctiveFormula *)(*psi))->get_clauses();

          for (vector<Formula *>::iterator disj_cl = disj_clauses.begin(); 
	       disj_cl != disj_clauses.end(); disj_cl++)
            {
              vector<Formula *> new_conj_clauses;

              new_conj_clauses.push_back ((Formula *)(*disj_cl)->ref ());

              for (vector<Formula *>::const_iterator conj_cl = 
		     conj_clauses.begin(); conj_cl != conj_clauses.end(); 
		   conj_cl++) {
                if (conj_cl != psi)
                  new_conj_clauses.push_back ((Formula *)(*conj_cl)->ref ());
	      }
              new_clauses.push_back (ConjunctiveFormula::create (new_conj_clauses));
            }

          return DisjunctiveFormula::create (new_clauses);
        }
    }

  throw RuleNotApplicableExc();
}

/*****************************************************************************/

static bool 
PhiAndNotPhi(const vector<Formula *> &l)
{
  if (l.size() <= 1) return false;

  vector<Formula *>::const_iterator phi = l.begin();
  phi++;

  for (; phi != l.end(); phi++)
    {
      for (vector<Formula *>::const_iterator psi = l.begin(); psi != phi; psi++)
        {
          if ((*psi)->is_NegationFormula())
            if (((NegationFormula *)(*psi))->get_neg() == *phi)
              return true;

          if ((*phi)->is_NegationFormula())
            {
              if (((NegationFormula *)(*phi))->get_neg() == *psi)
                return true;
            }
        }
    }
  return false;
}

static Formula * 
PhiAndNotPhiRule(const Formula *phi)
  throw (RuleNotApplicableExc)
{
  if (phi->is_DisjunctiveFormula())
    if (PhiAndNotPhi(((DisjunctiveFormula *) phi)->get_clauses()))
      return Constant::create (1);

  if (phi->is_ConjunctiveFormula())
    if (PhiAndNotPhi(((ConjunctiveFormula *) phi)->get_clauses()))
      return Constant::create (0);

  throw RuleNotApplicableExc();
}

/*****************************************************************************/

#define TRY_RULE(rule)                  \
  try { return rule(phi); }             \
  catch (RuleNotApplicableExc &) {}

Formula * Simplify0(const Formula *phi)
{
  TRY_RULE(Cancel_LNOT_NOT);
  TRY_RULE(ExpressionSimplify);
  TRY_RULE(SyntaxicEqualityRule);
  TRY_RULE(NOTOperatorOnConstant);
  TRY_RULE(LogicNegationOperatorOnConstant);
  TRY_RULE(ConjunctionSimplification);
  TRY_RULE(DisjunctionSimplification);
  TRY_RULE(PhiAndNotPhiRule);
  TRY_RULE(AndAndRule);
  TRY_RULE(OrOrRule);
  throw RuleNotApplicableExc();
}

#undef TRY_RULE
/*****************************************************************************/

class RuleApplicationWithChangeDetection : public FormulaReplacingRule
{
private:
  Formula * (*the_rule) (const Formula *);


public:

  bool changed;

  RuleApplicationWithChangeDetection(const RuleApplicationWithChangeDetection &r) 
    : FormulaReplacingRule(), the_rule (r.the_rule), changed(r.changed)
  {
  }

  RuleApplicationWithChangeDetection(Formula * (*rule) (const Formula *)) : 
    the_rule (rule), changed(false)
  {
  }

  Formula *f(const Formula *phi) 
  {
    bool old_changed = changed;
    changed = true;
    try { return the_rule(phi); }
    catch (RuleNotApplicableExc &) {}
    changed = old_changed;
    return (Formula *) phi->ref ();
  }

};

/*****************************************************************************/

static bool 
apply_rule_in_place(RuleApplicationWithChangeDetection &r, Formula **phi)
{
  bool global_changed = false;

  // Apply and apply again until no rule is applicable
  do {
    r.changed = false;
    Formula *simplified = (*phi)->bottom_up_apply (&r);
    (*phi)->deref ();
    *phi = simplified;
    global_changed = global_changed || r.changed;
  }
  while (r.changed);

  return global_changed;
}

/*****************************************************************************/

static Formula *
apply_rule(RuleApplicationWithChangeDetection &r, const Formula * phi)
{
  Formula *copy = phi->ref ();

  // Apply and apply again until no rule is applicable
  do 
    {
      r.changed = false;
      Formula *new_copy = copy->bottom_up_apply (&r);
      copy->deref ();
      copy = new_copy;
    } 
  while (r.changed);

  return copy;
}

/*****************************************************************************/

#define Simplify0Rule RuleApplicationWithChangeDetection(Simplify0)

Formula * Formula::simplify_level0() const
{
  RuleApplicationWithChangeDetection r(Simplify0);

  return apply_rule (r, this);
}

/*****************************************************************************/


bool Formula::simplify_level0(Formula **phi)
{
  RuleApplicationWithChangeDetection r(Simplify0);

  return apply_rule_in_place(r, phi);
}

/*****************************************************************************/

bool Formula::disjunctive_normal_form(Formula **phi)
{
  Formula::simplify_level0(phi);
  RuleApplicationWithChangeDetection r(DisjunctiveNormalFormRule);
  bool result = apply_rule_in_place (r, phi);
  Formula::simplify_level0(phi);

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

string BooleanConstantFormula::pp(std::string prefix) const
{
  ostringstream oss;
  oss << prefix << (value ? "TRUE" : "FALSE");
  return oss.str();
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

/*****************************************************************************/
/*****************************************************************************/
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

			/* --------------- */

void 
BooleanConstantFormula::acceptVisitor (FormulaVisitor *visitor) 
{
  visitor->visit (this);
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
BooleanConstantFormula::acceptVisitor (ConstFormulaVisitor *visitor) const 
{
  visitor->visit (this);
}

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

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

#include <algorithm>

#include <kernel/Expressions.hh>
#include <kernel/expressions/FormulaVisitor.hh>
#include <kernel/expressions/PatternMatching.hh>

using namespace std;

class PatternMatchingVisitor : public ConstFormulaVisitor {
public :
  typedef PatternMatching::VarList VarList;

private:
  const Expr *F;
  const VarList &free_variables;

  PatternMatching *result;

public: 
  PatternMatchingVisitor (const Expr *form, 
			  const VarList &FV)
    : F (form), free_variables (FV), result (NULL) { 
  } 
  
  virtual ~PatternMatchingVisitor () { 
  }

  PatternMatching *get_result () {
    return result;
  }

  virtual void visit (const Constant *C) {
    const Constant *pe = dynamic_cast<const Constant *> (F);

    if (pe == NULL ||
	pe->get_bv_offset() != C->get_bv_offset() || 
	pe->get_bv_size() != C->get_bv_size() || 
	pe != C)
      throw PatternMatching::Failure ();

    result = new PatternMatching ();
  }

  virtual void visit (const Variable *V) {
    const Variable *ve = dynamic_cast<const Variable *> (F);

    if (find(free_variables.begin(),
	     free_variables.end(), V) != free_variables.end())
      {
	result = new PatternMatching (); 
	result->set (V, F->ref ());
      }
    else if (ve == V)
      {
	result = new PatternMatching ();
      }
    else
      {
	throw PatternMatching::Failure ();
      }
  }

  virtual void visit (const UnaryApp *E) {
    const UnaryApp *pe = dynamic_cast<const UnaryApp *> (F);

    if (pe == NULL ||
	pe->get_bv_offset () != E->get_bv_offset () ||
	pe->get_bv_size () != E->get_bv_size () ||
	pe->get_op () != E->get_op ())
      throw PatternMatching::Failure ();
    
    result = PatternMatching::match (pe->get_arg1 (), E->get_arg1 (), 
				     free_variables);
  }

  virtual void visit (const BinaryApp *E) {
    const BinaryApp *pe = dynamic_cast<const BinaryApp *> (F);

    if (pe == NULL || 
	pe->get_bv_offset () != E->get_bv_offset () ||
	pe->get_bv_size () != E->get_bv_size () ||
	pe->get_op () != E->get_op ())
      throw PatternMatching::Failure ();

    PatternMatching *pm1 = 
      PatternMatching::match (pe->get_arg1 (), E->get_arg1 (), free_variables);

    try
      {
	PatternMatching *pm2 = 
	  PatternMatching::match (pe->get_arg2 (), E->get_arg2 (), 
				  free_variables);
	pm1->merge (pm2);
	delete pm2;

	result = pm1;
      }
    catch (PatternMatching::Failure &)
      {
	delete pm1;
	throw;
      }
  }

  virtual void visit (const TernaryApp *E) {
    const TernaryApp *pe = dynamic_cast<const TernaryApp *> (F);

    if (pe == NULL || 
	pe->get_bv_offset () != E->get_bv_offset () ||
	pe->get_bv_size () != E->get_bv_size () ||
	pe->get_op () != E->get_op ())
      throw PatternMatching::Failure ();

    PatternMatching *pm1 = 
      PatternMatching::match (pe->get_arg1 (), E->get_arg1 (), free_variables);
    try
      {
	PatternMatching *pm = 
	  PatternMatching::match (pe->get_arg2 (), E->get_arg2 (), 
				  free_variables);
	pm1->merge (pm);
	delete pm;

	pm = PatternMatching::match (pe->get_arg3 (), E->get_arg3 (), 
				     free_variables);

	pm1->merge (pm);
	delete pm;
	    
	result = pm1;
      }
    catch (PatternMatching::Failure &)
      {
	delete pm1;
	throw;
      }
  }

  virtual void visit (const MemCell *E) {
    const MemCell *pe = dynamic_cast<const MemCell *> (F);

    if (pe == NULL ||
	pe->get_bv_offset() != E->get_bv_offset() ||
	pe->get_bv_size() != E->get_bv_size())
      throw PatternMatching::Failure ();
    
    result = PatternMatching::match (pe->get_addr(), E->get_addr(), 
				     free_variables);
  }

  virtual void visit (const RegisterExpr *E) {
    const RegisterExpr *pe = dynamic_cast<const RegisterExpr *> (F);

    if (pe == NULL || 
	pe->get_bv_offset() != E->get_bv_offset() || 
	pe->get_bv_size() != E->get_bv_size() || 
	pe != E)
      throw PatternMatching::Failure ();

    result = new PatternMatching ();  
  }

  virtual void visit (const QuantifiedExpr *E) {
    const QuantifiedExpr *qf = dynamic_cast<const QuantifiedExpr *> (F);

    if (qf == NULL || qf->is_exist () != E->is_exist ())
      throw PatternMatching::Failure ();

    if (E->get_variable () != qf->get_variable ())
      throw PatternMatching::Failure();

    result = PatternMatching::match (qf->get_body (), E->get_body (), 
				     free_variables);
  }
};

			/* --------------- */

PatternMatching::PatternMatching () : matching () 
{
}

PatternMatching::~PatternMatching ()
{
  for (const_iterator i = matching.begin(); i != matching.end(); i++)
    i->second->deref ();
}

void 
PatternMatching::merge (const PatternMatching *other)
{
  for (const_iterator i = other->begin(); i != other->end(); i++)
    set (i->first, (Expr *) i->second->ref ());
}

const Expr *
PatternMatching::get (const Variable *v) const
{
  const_iterator p = matching.find (v);

  if (p != matching.end ())
    return p->second;
  return NULL;
}

bool
PatternMatching::has (const Variable *v) const
{
  const_iterator p = matching.find (v);

  return (p != matching.end ());
}

void 
PatternMatching::set (const Variable *v, Expr *F)
{
  iterator p = matching.find (v);
  if (p != matching.end ())
    {
      Expr *old = p->second;
      matching.erase (v);
      old->deref ();
    }
  matching[v] = F;
}

void 
PatternMatching::output_text (std::ostream &out) const 
{
  if (matching.size () == 0)
    out << "empty pattern matching" << endl;
  else
    {
      for (const_iterator i = matching.begin(); i != matching.end(); i++)
	out << i->first->pp () << "-->" << i->second->pp () << endl;
    }
}

PatternMatching::const_iterator 
PatternMatching::begin() const
{
  return matching.begin ();
}

PatternMatching::const_iterator 
PatternMatching::end() const
{
  return matching.end ();
}

bool 
PatternMatching::equal (const PatternMatching *other) const
{
  bool result = matching.size () == other->matching.size ();

  for (const_iterator i = begin (); i != end () && result; i++)
    result = (other->has (i->first) && 
	      get (i->first) == other->get (i->first));

  return result;
}

PatternMatching * 
PatternMatching::match (const Expr *F, const Expr *pattern, 
			const VarList &free_variables)
  throw (Failure)
{
  PatternMatchingVisitor pmv (F, free_variables);

  pattern->acceptVisitor (&pmv);

  return pmv.get_result ();
}

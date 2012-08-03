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

#include <kernel/expressions/ConditionalSet.hh>

#include <cassert>
#include <exception>
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <utils/infrastructure.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/PatternMatching.hh>
#include <kernel/expressions/BottomUpApplyVisitor.hh>
#include <kernel/expressions/FormulaUtils.hh>

using namespace std;

Variable *
ConditionalSet::EltSymbol ()
{
  return Variable::create ("elt");
}

inline Expr *IsIn (const Expr *elt) 
{
  return BinaryApp::create (EQ, (Expr*) ConditionalSet::EltSymbol (), 
			    (Expr*) elt->ref ());
}

void ConditionalSet::cs_simplify(Formula **set)
{
  FormulaUtils::simplify_level0 (set);
}

// ATTENTION CHANTIER CHANTIER CHANTIER
Formula * ConditionalSet::cs_condition_for_belonging (Formula * set, Expr *) {

  Formula * simple_set = set->ref ();
  cs_simplify (&simple_set);
  
  throw std::runtime_error ("cs_condition_for_belonging");
  return NULL;
}


class ExtractEltRule : public ConstBottomUpApplyVisitor
{
public:
  std::vector<Expr *> elt_list;

  void add_elt (Expr * e) 
  {
    for (int i=0; i<(int) elt_list.size(); i++)
      if (e == elt_list[i]) 
	{
	  e->deref ();
	  return;
	}
    elt_list.push_back (e);
  };

  void apply (const Formula *e) 
  {
    Variable *X = Variable::create ("X"); 
    Formula * elt_def_pattern = 
      Formula::Equality((Expr *) ConditionalSet::EltSymbol (), 
			(Expr *) X->ref ());
    std::list<const Variable *> free_variables; 

    free_variables.push_back(X);
    try 
      {
	PatternMatching * matchings = 
	  PatternMatching::match (e, elt_def_pattern, free_variables);

	assert (matchings->has (X));
	add_elt ((Expr*) matchings->get (X)->ref ());
	delete matchings;
      } catch (PatternMatching::Failure &) {}
    X->deref ();
    elt_def_pattern->deref ();
  }
};

std::vector<Expr*> 
ConditionalSet::cs_possible_values (const Formula *set) 
{
  ExtractEltRule r;
  set->acceptVisitor (r);
  return r.elt_list;
}

Formula * 
ConditionalSet::cs_flatten (const Formula *set) 
{
  std::vector<Expr*> all_values = cs_possible_values (set);
  Formula *flat_set = Constant::False ();

  for (int i = 0; i< (int) all_values.size (); i++) 
    {
      cs_add (&flat_set, all_values[i]);
      all_values[i]->deref ();
    }

  return flat_set;
}

Formula *
ConditionalSet::cs_contains (const Formula *set, const Expr *elt)
{
  Variable *eltsym = ConditionalSet::EltSymbol ();
  Formula *new_set = FormulaUtils::replace_variable (set, eltsym, elt);  
  FormulaUtils::simplify_level0 (&new_set);
  eltsym->deref ();

  return new_set;
}

bool 
ConditionalSet::cs_compute_contains (const Formula *set, const Expr *elt)
{
  Formula *result = ConditionalSet::cs_contains (set, elt);
  bool result_bool = result->eval_level0 ();
  result->deref ();

  return result_bool;
}

bool ConditionalSet::cs_conditional_add(Formula *cond, Formula **set, Expr *elt)
{
  if (!ConditionalSet::cs_compute_contains(*set, elt))
    {
      Formula *tmp = 
	DisjunctiveFormula::create (Formula::implies(cond, IsIn(elt)), *set);
      *set = tmp;
      FormulaUtils::simplify_level0(set);
      return true;
    }
  else return false;
}

bool 
ConditionalSet::cs_conditional_union(Formula *cond, Formula **set1, 
				     Formula *set2)
{
  Formula *included = Formula::implies(set2->ref (), (*set1)->ref ());

  FormulaUtils::simplify_level0 (&included);

  if (!(included->eval_level0()))
    {
      included->deref ();
      *set1 = DisjunctiveFormula::create (Formula::implies(cond, set2), *set1);
      FormulaUtils::simplify_level0 (set1);

      return true;
    }
  else
    {
      included->deref ();
      return false;
    }
}

bool 
ConditionalSet::cs_remove(Formula **set, const Expr *elt)
{
  bool was_in = cs_compute_contains (*set, elt);
  *set = ConjunctiveFormula::create (*set, 
				     NegationFormula::create (IsIn (elt)));
  FormulaUtils::simplify_level0 (set);

  return was_in;
}

bool 
ConditionalSet::cs_add(Formula **set, const Expr *elt)
{
  bool result = ConditionalSet::cs_compute_contains(*set, elt);

  if (! result)
    {
      *set = DisjunctiveFormula::create (IsIn (elt), *set);
      FormulaUtils::simplify_level0 (set);
    }

  return result;
}

bool 
ConditionalSet::cs_union(Formula **set1, const Formula *set2)
{
  bool result = (set2 == *set1);

  if (! result)
    {
      Formula *included = Formula::implies (set2->ref (), (*set1)->ref ());
      FormulaUtils::simplify_level0 (&included);

      if (! included->eval_level0 ())
	{
	  *set1 = DisjunctiveFormula::create (set2->ref (), *set1);
	  FormulaUtils::simplify_level0(set1);
	  result = true;
	}
      included->deref ();
    }
  return result;
}

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
#include <kernel/expressions/exprutils.hh>

using namespace std;

Variable *
ConditionalSet::EltSymbol (int size)
{
  return Variable::create ("elt", size);
}

inline Expr *IsIn (const Expr *elt)
{
  return BinaryApp::createEquality(ConditionalSet::EltSymbol (elt->get_bv_size ()), elt->ref ());
}

void ConditionalSet::cs_simplify(Expr **set)
{
  exprutils::simplify_level0 (set);
}

// ATTENTION CHANTIER CHANTIER CHANTIER
Expr * ConditionalSet::cs_condition_for_belonging (Expr * set, Expr *) {

  Expr * simple_set = set->ref ();
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

  void apply (const Expr *e)
  {
    Variable *X = Variable::create ("X", Expr::get_bv_default_size());
    Expr * elt_def_pattern =
      Expr::createEquality(ConditionalSet::EltSymbol (X->get_bv_size ()), X->ref ());
    std::list<const Variable *> free_variables;

    free_variables.push_back(X);
    try
      {
	PatternMatching * matchings =
	  PatternMatching::match (e, elt_def_pattern, free_variables);

	assert (matchings->has (X));
	add_elt (matchings->get (X)->ref ());
	delete matchings;
      } catch (PatternMatching::Failure &) {}
    X->deref ();
    elt_def_pattern->deref ();
  }
};

std::vector<Expr*>
ConditionalSet::cs_possible_values (const Expr *set)
{
  ExtractEltRule r;
  set->acceptVisitor (r);
  return r.elt_list;
}

Expr *
ConditionalSet::cs_flatten (const Expr *set)
{
  std::vector<Expr*> all_values = cs_possible_values (set);
  Expr *flat_set = Constant::False ();

  for (int i = 0; i< (int) all_values.size (); i++)
    {
      cs_add (&flat_set, all_values[i]);
      all_values[i]->deref ();
    }

  return flat_set;
}

Expr *
ConditionalSet::cs_contains (const Expr *set, const Expr *elt)
{
  Variable *eltsym = ConditionalSet::EltSymbol (elt->get_bv_size ());
  Expr *new_set = exprutils::replace_variable (set, eltsym, elt);
  exprutils::simplify_level0 (&new_set);
  eltsym->deref ();

  return new_set;
}

bool
ConditionalSet::cs_compute_contains (const Expr *set, const Expr *elt)
{
  Expr *result = ConditionalSet::cs_contains (set, elt);
  bool result_bool = result->eval_level0 ();
  result->deref ();

  return result_bool;
}

bool ConditionalSet::cs_conditional_add(Expr *cond, Expr **set, Expr *elt)
{
  if (!ConditionalSet::cs_compute_contains(*set, elt))
    {
      Expr *tmp = Expr::createLOr (Expr::createImplies (cond, IsIn(elt)), *set);
      *set = tmp;
      exprutils::simplify_level0(set);
      return true;
    }
  else return false;
}

bool
ConditionalSet::cs_conditional_union(Expr *cond, Expr **set1,
				     Expr *set2)
{
  Expr *included = Expr::createImplies (set2->ref (), (*set1)->ref ());

  exprutils::simplify_level0 (&included);

  if (!(included->eval_level0()))
    {
      included->deref ();
      *set1 = Expr::createLOr (Expr::createImplies (cond, set2), *set1);
      exprutils::simplify_level0 (set1);

      return true;
    }
  else
    {
      included->deref ();
      return false;
    }
}

bool
ConditionalSet::cs_remove(Expr **set, const Expr *elt)
{
  bool was_in = cs_compute_contains (*set, elt);
  *set = Expr::createLAnd (*set, Expr::createLNot (IsIn (elt)));
  exprutils::simplify_level0 (set);

  return was_in;
}

bool
ConditionalSet::cs_add(Expr **set, const Expr *elt)
{
  bool result = ConditionalSet::cs_compute_contains(*set, elt);

  if (! result)
    {
      *set = Expr::createLOr (IsIn (elt), *set);
      exprutils::simplify_level0 (set);
    }

  return result;
}

bool
ConditionalSet::cs_union(Expr **set1, const Expr *set2)
{
  bool result = (set2 == *set1);

  if (! result)
    {
      Expr *included = Expr::createImplies (set2->ref (), (*set1)->ref ());
      exprutils::simplify_level0 (&included);

      if (! included->eval_level0 ())
	{
	  *set1 = Expr::createLOr (set2->ref (), *set1);
	  exprutils::simplify_level0(set1);
	  result = true;
	}
      included->deref ();
    }
  return result;
}

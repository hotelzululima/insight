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
#include <kernel/expressions/FormulaUtils.hh>

#include <kernel/expressions/PatternMatching.hh>
#include <kernel/expressions/FormulaRewritingFunctions.hh>
#include <kernel/expressions/FormulaReplaceSubtermRule.hh>
#include <kernel/expressions/BottomUpApplyVisitor.hh>
#include <kernel/expressions/BottomUpRewritePatternRule.hh>
#include <kernel/Expressions.hh>


using namespace FormulaUtils;

Formula *
FormulaUtils::replace_subterm (const Formula *F, const Formula *pattern, 
			       const Formula *value)
{
  FormulaReplaceSubtermRule r (pattern, value);
  F->acceptVisitor (&r);

  return r.get_result ();
}

Formula * 
FormulaUtils::replace_variable (const Formula *F, 
				const Variable *v, const Formula *value)
{
  return replace_subterm (F, v, value);
}

bool 
FormulaUtils::replace_variable_and_assign (Formula **phi, 
					   const Variable *v, 
					   const Formula *value)
{
  Formula *F = replace_variable (*phi, v, value);
  bool result = (*phi != F);
  (*phi)->deref ();
  *phi = F;

  return result;
}

Formula *
FormulaUtils::bottom_up_rewrite (const Formula *phi, FormulaRewritingRule &r)
{
  phi->acceptVisitor (r);

  return r.get_result ();
}

bool 
FormulaUtils::bottom_up_rewrite_and_assign (Formula **phi, 
					    FormulaRewritingRule &r)
{
  Formula *new_phi = bottom_up_rewrite (*phi, r);
  bool result = (*phi != new_phi);

  (*phi)->deref ();
  *phi = new_phi;

  return result;
}

Formula *
FormulaUtils::bottom_up_rewrite_pattern (const Formula *phi,
					 const Formula *pattern,
					 const VarList &fv,
					 const Formula *value)
{
  BottomUpRewritePatternRule r (pattern, fv, value);

  return FormulaUtils::bottom_up_rewrite (phi, r);
}
  
bool 
FormulaUtils::bottom_up_rewrite_pattern_and_assign (Formula **phi,
						    const Formula *pattern,
						    const VarList &fv,
						    const Formula *value)
{
  BottomUpRewritePatternRule r (pattern, fv, value);

  return FormulaUtils::bottom_up_rewrite_and_assign (phi, r);
}

bool
FormulaUtils::rewrite_in_DNF (Formula **phi)
{
  FunctionRewritingRule r (disjunctive_normal_form_rule);

  FormulaUtils::simplify_level0 (phi);
  bool result = FormulaUtils::bottom_up_rewrite_and_assign (phi, r);
  FormulaUtils::simplify_level0 (phi);

  return result;
}

bool
FormulaUtils::simplify_level0 (Formula **F)
{
  FunctionRewritingRule r (simplify_formula);

  bool result = FormulaUtils::bottom_up_rewrite_and_assign (F, r);

  return result;
}


bool
FormulaUtils::simplify (Expr **E)
{
  Formula **F = (Formula **) E;
  FunctionRewritingRule r (simplify_expr);

  bool result = FormulaUtils::bottom_up_rewrite_and_assign (F, r);
  if (result)
    {
      while (result)
	result = FormulaUtils::bottom_up_rewrite_and_assign (F, r);
      result = true;
    }

  return result;
}

Formula * 
FormulaUtils::extract_v_pattern (std::string var_id, const Formula *phi, 
				 const Formula *pattern)
{
  Formula *result = NULL;
  Variable *v = Variable::create (var_id); 
  try
    {
      PatternMatching::VarList fv;
      fv.push_back(v);

      PatternMatching *vm = 
	PatternMatching::match (phi, pattern, fv);

      if (vm->has (v))
	result = (Formula *) vm->get (v)->ref ();
      delete vm;
    }
  catch (PatternMatching::Failure &) 
    {
    }
  v->deref ();

  return result;
}

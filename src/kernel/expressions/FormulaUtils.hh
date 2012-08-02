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

#ifndef KERNEL_EXPRESSIONS_FORMULAUTILS_HH
# define KERNEL_EXPRESSIONS_FORMULAUTILS_HH

# include <string>
# include <list>
# include <vector>
# include <kernel/expressions/Formula.hh>
# include <kernel/expressions/FormulaRewritingRule.hh>

namespace FormulaUtils
{
  typedef std::list<const Variable *> VarList;

  extern Formula *
  replace_subterm (const Formula *F, 
		   const Formula *pattern, const Formula *value);

  extern Formula * 
  replace_variable (const Formula *F, 
		    const Variable *v, const Formula *value);

  extern bool 
  replace_variable_and_assign (Formula **phi, 
			       const Variable *v, const Formula *value);


  extern Formula *
  bottom_up_rewrite (const Formula *phi, FormulaRewritingRule &r);

  extern bool 
  bottom_up_rewrite_and_assign (Formula **phi, FormulaRewritingRule &r);

  extern Formula *
  bottom_up_rewrite_pattern (const Formula *Phi,
			     const Formula *pattern,
			     const VarList &free_variables,
			     const Formula *value);
  
  extern bool 
  bottom_up_rewrite_pattern_and_assign (Formula **phi,
					const Formula *pattern,
					const VarList &free_variables,
					const Formula * value);

  extern bool
  rewrite_in_DNF (Formula **phi);

  extern bool
  simplify_level0 (Formula **F);

  extern bool
  simplify (Expr **E);

  template <typename ContainerType, typename ExprType>
  ContainerType
  collect_subterms_of_type (const Formula *F, bool eliminate_duplicate);  
};

# include <kernel/expressions/FormulaUtils.ii>

#endif /* ! KERNEL_EXPRESSIONS_FORMULAUTILS_HH */

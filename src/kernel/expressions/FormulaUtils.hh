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
# include <kernel/Expressions.hh>
# include <kernel/expressions/FormulaRewritingRule.hh>

namespace FormulaUtils
{
  typedef std::list<const Variable *> VarList;

  extern Expr *
  replace_subterm (const Expr *F, 
		   const Expr *pattern, const Expr *value);

  extern Expr * 
  replace_variable (const Expr *F, 
		    const Variable *v, const Expr *value);

  extern bool 
  replace_variable_and_assign (Expr **phi, 
			       const Variable *v, const Expr *value);


  extern Expr *
  bottom_up_rewrite (const Expr *phi, FormulaRewritingRule &r);

  extern bool 
  bottom_up_rewrite_and_assign (Expr **phi, FormulaRewritingRule &r);

  extern Expr *
  bottom_up_rewrite_pattern (const Expr *Phi,
			     const Expr *pattern,
			     const VarList &free_variables,
			     const Expr *value);
  
  extern bool 
  bottom_up_rewrite_pattern_and_assign (Expr **phi,
					const Expr *pattern,
					const VarList &free_variables,
					const Expr * value);

  extern bool
  rewrite_in_DNF (Expr **phi);

  extern bool
  simplify_level0 (Expr **F);

  extern bool
  simplify (Expr **E);

  template <typename ContainerType, typename ExprType>
  ContainerType
  collect_subterms_of_type (const Expr *F, bool eliminate_duplicate);  

  /* return the matchin of var_id if 'this' matchs phi. Or NULL if 'this' does 
     not match phi. */
  extern Expr * 
  extract_v_pattern (std::string var_id, const Expr *phi, 
		     const Expr *pattern);
};

# include <kernel/expressions/FormulaUtils.ii>

#endif /* ! KERNEL_EXPRESSIONS_FORMULAUTILS_HH */

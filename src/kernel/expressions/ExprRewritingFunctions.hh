/*
 * Copyright (c) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.

 * All rights reserved.

 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:

 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.

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
#ifndef KERNEL_EXPRESSIONS_EXPRREWRITINGFUNCTIONS_HH
# define KERNEL_EXPRESSIONS_EXPRREWRITINGFUNCTIONS_HH

# include <kernel/Expressions.hh>
# include <kernel/expressions/FunctionRewritingRule.hh>

extern void
rewrite_in_place (FunctionRewritingRule::RewriteExprFunc *func,
		  Expr **pF);

extern Expr *
syntaxic_equality_rule (const Expr *phi);

extern Expr *
zero_shift_rule (const Expr *phi);

extern Expr *
not_operator_on_constant (const Expr *phi);

extern Expr *
cancel_lnot_not (const Expr *phi) ;

extern Expr *
logical_negation_operator_on_constant (const Expr *phi);

extern Expr *
conjunction_simplification (const Expr *phi);

extern Expr *
disjunction_simplification (const Expr *phi);

extern Expr *
and_and_rule (const Expr *phi);

extern Expr *
or_or_rule (const Expr *phi);

extern Expr *
not_decrease (const Expr *phi);

extern Expr *
disjunctive_normal_form_rule (const Expr *phi);

extern Expr *
phi_and_not_phi_rule (const Expr *phi);

extern Expr *
compute_constants (const Expr *phi);

extern Expr *
void_operations (const Expr *phi);

extern Expr *
bit_field_computation (const Expr *phi);

extern Expr *
binary_operations_simplification (const Expr *phi);

extern Expr *
simplify_formula (const Expr *phi);

extern Expr *
simplify_expr (const Expr *phi);


#endif /* !KERNEL_EXPRESSIONS_EXPRREWRITINGFUNCTIONS_HH */

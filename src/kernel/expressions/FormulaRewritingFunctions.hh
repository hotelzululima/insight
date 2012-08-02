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
#ifndef FORMULAREWRITINGFUNCTIONS_HH
# define FORMULAREWRITINGFUNCTIONS_HH

# include <kernel/expressions/Formula.hh>
# include <kernel/expressions/FunctionRewritingRule.hh>


extern void
rewrite_in_place (FunctionRewritingRule::RewriteFormulaFunc *func, 
		  Formula **pF);
  
extern Formula * 
syntaxic_equality_rule (const Formula *phi);
  
extern Formula * 
not_operator_on_constant (const Formula *phi);
  
extern Formula * 
cancel_lnot_not (const Formula *phi) ;
  
extern Formula * 
logical_negation_operator_on_constant (const Formula *phi);
  
extern Formula *
conjunction_simplification (const Formula *phi);
  
extern Formula *
disjunction_simplification (const Formula *phi);
  
extern Formula * 
and_and_rule (const Formula *phi);
  
extern Formula * 
or_or_rule (const Formula *phi);
  
extern Formula * 
not_decrease (const Formula *phi);
  
extern Formula *
disjunctive_normal_form_rule (const Formula *phi);
  
extern Formula * 
phi_and_not_phi_rule (const Formula *phi);
  
extern Formula *
compute_constants (const Formula *phi);

extern Formula *
void_operations (const Formula *phi);

extern Formula * 
bit_field_computation (const Formula *phi);

extern Formula * 
binary_operations_simplification (const Formula *phi);

extern Formula * 
simplify_formula (const Formula *phi);

extern Formula * 
simplify_expr (const Formula *phi);


#endif /* ! FORMULAREWRITINGFUNCTIONS_HH */

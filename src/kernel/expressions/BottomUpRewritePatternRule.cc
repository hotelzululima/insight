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

#include <kernel/expressions/PatternMatching.hh>
#include <kernel/expressions/ExprUtils.hh>
#include <kernel/expressions/BottomUpRewritePatternRule.hh>

BottomUpRewritePatternRule::BottomUpRewritePatternRule (const Expr *p, 
							const VarList &fv, 
							const Expr *v)
  : pattern (p), free_variables (fv), value (v)
{  
}

BottomUpRewritePatternRule::~BottomUpRewritePatternRule ()
{
}

Expr *
BottomUpRewritePatternRule::rewrite (const Expr *phi)
{
  Expr *result;

  try
    {
      PatternMatching *vm = 
	PatternMatching::match (phi, pattern, free_variables);
            
      Expr *value_cpy = value->ref ();
      for (PatternMatching::const_iterator p = vm->begin(); p != vm->end(); p++)
	exprutils::replace_variable_and_assign (&value_cpy, p->first, 
						p->second);
      delete vm;
      
      result = value_cpy;
    }
  catch (PatternMatching::Failure &)
    {
      result = phi->ref ();
    }
  return result;
}

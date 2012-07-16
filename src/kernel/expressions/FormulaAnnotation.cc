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

#include <kernel/expressions/FormulaAnnotation.hh>

FormulaAnnotation::FormulaAnnotation()
  : Annotation (), formula (NULL) 
{
}

FormulaAnnotation::FormulaAnnotation (const FormulaAnnotation &other) 
  : Annotation (other), formula (NULL)
{
  set_formula (other.formula);
}

FormulaAnnotation::FormulaAnnotation (Formula *F)
  : Annotation ()
{
  formula = F->ref ();
}

FormulaAnnotation::~FormulaAnnotation()
{
  if (formula != NULL)
    formula->deref ();
}

std::string 
FormulaAnnotation::pp(std::string prefix) const
{
  return formula->pp(prefix);
}

void *
FormulaAnnotation::clone() const
{ 
  return new FormulaAnnotation (formula);
}

void 
FormulaAnnotation::set_formula (Formula *F)
{
  if (formula != NULL)
    formula->deref ();
  formula = F->ref ();  
}

			/* --------------- */

const Formula *
FormulaAnnotation::get_formula () const
{
  return formula;
}

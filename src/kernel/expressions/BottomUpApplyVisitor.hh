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
#ifndef BOTTOMUPAPPLYVISITOR_HH
# define BOTTOMUPAPPLYVISITOR_HH

# include <kernel/expressions/FormulaVisitor.hh>

class BottomUpApplyVisitor : public FormulaVisitor 
{
protected :
  BottomUpApplyVisitor ();

public :
  virtual ~BottomUpApplyVisitor ();

  virtual void visit (Constant *);
  virtual void visit (Variable *);
  virtual void visit (UnaryApp *); 
  virtual void visit (BinaryApp *);
  virtual void visit (TernaryApp *);
  virtual void visit (MemCell *); 
  virtual void visit (RegisterExpr *); 

  virtual void visit (ConjunctiveFormula *); 
  virtual void visit (DisjunctiveFormula *); 
  virtual void visit (NegationFormula *); 
  virtual void visit (QuantifiedFormula *); 

  virtual void pre (Formula *);
  virtual void apply (Formula *) = 0;

  virtual void visit (NaryBooleanFormula *); 
};  

class ConstBottomUpApplyVisitor : public ConstFormulaVisitor 
{
protected :
  ConstBottomUpApplyVisitor ();

public :
  virtual ~ConstBottomUpApplyVisitor ();

  virtual void visit (const Constant *);
  virtual void visit (const Variable *);
  virtual void visit (const UnaryApp *); 
  virtual void visit (const BinaryApp *);
  virtual void visit (const TernaryApp *);
  virtual void visit (const MemCell *);
  virtual void visit (const RegisterExpr *);

  virtual void visit (const ConjunctiveFormula *); 
  virtual void visit (const DisjunctiveFormula *); 
  virtual void visit (const NegationFormula *); 
  virtual void visit (const QuantifiedFormula *); 

  virtual void pre (const Formula *);
  virtual void apply (const Formula *) = 0;

  virtual void visit (const NaryBooleanFormula *); 
};  


#endif /* ! BOTTOMUPAPPLYVISITOR_HH */

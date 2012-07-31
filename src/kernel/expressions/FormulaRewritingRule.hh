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
#ifndef KERNEL_EXPRESSIONS_FORMULAREWRITINGRULE_HH
# define KERNEL_EXPRESSIONS_FORMULAREWRITINGRULE_HH

# include <kernel/expressions/FormulaVisitor.hh>

class Expr;
class Formula;
class NaryBooleanFormula;

class FormulaRewritingRule : public ConstFormulaVisitor 
{

protected:
  FormulaRewritingRule ();

public:

  virtual ~FormulaRewritingRule ();

  virtual void visit (const Constant *);
  virtual void visit (const Variable *);
  virtual void visit (const UnaryApp *);
  virtual void visit (const BinaryApp *);
  virtual void visit (const TernaryApp *);
  virtual void visit (const MemCell *);
  virtual void visit (const RegisterExpr *);

  virtual void visit (const BooleanConstantFormula *);
  virtual void visit (const ConjunctiveFormula *);
  virtual void visit (const DisjunctiveFormula *);
  virtual void visit (const NegationFormula *);
  virtual void visit (const QuantifiedFormula *);

  virtual Formula *rewrite (const Formula *F);
  virtual Expr *rewrite (const Expr *F);

  virtual Formula *get_result () const;

private:
  Formula *result;

  virtual void visit (const NaryBooleanFormula *);
};

#endif /* ! KERNEL_EXPRESSIONS_FORMULAREWRITINGRULE_HH */

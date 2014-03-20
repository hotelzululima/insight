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
#ifndef KERNEL_EXPRESSIONS_EXPRREWRITINGRULE_HH
# define KERNEL_EXPRESSIONS_EXPRREWRITINGRULE_HH

# include <kernel/expressions/ExprVisitor.hh>

class Expr;

class ExprRewritingRule : public ConstExprVisitor
{

protected:
  ExprRewritingRule ();

public:

  virtual ~ExprRewritingRule ();

  virtual void visit (const Constant *);
  virtual void visit (const RandomValue *);
  virtual void visit (const Variable *);
  virtual void visit (const UnaryApp *);
  virtual void visit (const BinaryApp *);
  virtual void visit (const TernaryApp *);
  virtual void visit (const MemCell *);
  virtual void visit (const RegisterExpr *);
  virtual void visit (const QuantifiedExpr *);

  virtual Expr *rewrite (const Expr *F) = 0;

  virtual Expr *get_result () const;

private:
  Expr *result;
};

#endif /* ! KERNEL_EXPRESSIONS_EXPRREWRITINGRULE_HH */

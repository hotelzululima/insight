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

# include <kernel/expressions/ExprVisitor.hh>

class BottomUpApplyVisitor : public ExprVisitor
{
protected :
  BottomUpApplyVisitor ();

public :
  virtual ~BottomUpApplyVisitor ();

  virtual void visit (Constant *);
  virtual void visit (RandomValue *);
  virtual void visit (Variable *);
  virtual void visit (UnaryApp *);
  virtual void visit (BinaryApp *);
  virtual void visit (TernaryApp *);
  virtual void visit (MemCell *);
  virtual void visit (RegisterExpr *);
  virtual void visit (QuantifiedExpr *);

  virtual void pre (Expr *);
  virtual void apply (Expr *) = 0;
};

class ConstBottomUpApplyVisitor : public ConstExprVisitor
{
protected :
  ConstBottomUpApplyVisitor ();

public :
  virtual ~ConstBottomUpApplyVisitor ();

  virtual void visit (const Constant *);
  virtual void visit (const RandomValue *);
  virtual void visit (const Variable *);
  virtual void visit (const UnaryApp *);
  virtual void visit (const BinaryApp *);
  virtual void visit (const TernaryApp *);
  virtual void visit (const MemCell *);
  virtual void visit (const RegisterExpr *);
  virtual void visit (const QuantifiedExpr *);

  virtual void pre (const Expr *);
  virtual void apply (const Expr *) = 0;
};


#endif /* ! BOTTOMUPAPPLYVISITOR_HH */

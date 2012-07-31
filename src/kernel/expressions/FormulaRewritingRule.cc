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
#include <kernel/expressions/Formula.hh>
#include <kernel/Expressions.hh>
#include "FormulaRewritingRule.hh"

FormulaRewritingRule::FormulaRewritingRule () 
  : ConstFormulaVisitor ()
{
  result = NULL;
}

FormulaRewritingRule::~FormulaRewritingRule ()
{
  if (result != NULL)
    result->deref ();
}

void 
FormulaRewritingRule::visit (const Constant *c)
{
  result = rewrite (c);
}

void 
FormulaRewritingRule::visit (const Variable *v)
{
  result = rewrite (v);
}

void 
FormulaRewritingRule::visit (const UnaryApp *ua)
{
  Expr *arg = ua->get_arg1 ();
  arg->acceptVisitor (this);
  arg = dynamic_cast<Expr *> (result);

  Expr *tmp = UnaryApp::create (ua->get_op (), arg,
				ua->get_bv_offset (), ua->get_bv_size ());
  result = rewrite (tmp);
  tmp->deref ();  
}

void 
FormulaRewritingRule::visit (const BinaryApp *ba)
{
  Expr *arg1 = ba->get_arg1 ();
  arg1->acceptVisitor (this);
  arg1 = dynamic_cast<Expr *> (result);

  Expr *arg2 = ba->get_arg2 ();
  arg2->acceptVisitor (this);
  arg2 = dynamic_cast<Expr *> (result);

  Expr *tmp = BinaryApp::create (ba->get_op (), arg1, arg2, 
				 ba->get_bv_offset (), ba->get_bv_size ());
  result = rewrite (tmp);
  tmp->deref ();  
}

void 
FormulaRewritingRule::visit (const TernaryApp *ta)
{
  Expr *arg1 = ta->get_arg1 ();
  arg1->acceptVisitor (this);
  arg1 = dynamic_cast<Expr *> (result);

  Expr *arg2 = ta->get_arg2 ();
  arg2->acceptVisitor (this);
  arg2 = dynamic_cast<Expr *> (result);

  Expr *arg3 = ta->get_arg3 ();
  arg3->acceptVisitor (this);
  arg3 = dynamic_cast<Expr *> (result);

  Expr *tmp = TernaryApp::create (ta->get_op (), arg1, arg2, arg3,
				  ta->get_bv_offset (), ta->get_bv_size ());
  result = rewrite (tmp);
  tmp->deref ();  
}

void 
FormulaRewritingRule::visit (const MemCell *mc)
{
  result = rewrite (mc);
}

void 
FormulaRewritingRule::visit (const RegisterExpr *reg)
{
  result = rewrite (reg);
}


void 
FormulaRewritingRule::visit (const BooleanConstantFormula *c)
{
  result = rewrite (c);
}

void 
FormulaRewritingRule::visit (const NaryBooleanFormula *F)
{
  NaryBooleanFormula::Operands new_ops;
  NaryBooleanFormula::OperandsConstIterator it = F->const_operands_begin ();
  NaryBooleanFormula::OperandsConstIterator end = F->const_operands_end ();

  for (; it != end; it++)
    {
      (*it)->acceptVisitor (this);
      new_ops.push_back (result);
    }
  
  Formula *tmp = F->create_from_operands (new_ops);
  result = rewrite (tmp);
  tmp->deref ();
}

void 
FormulaRewritingRule::visit (const ConjunctiveFormula *F)
{
  visit ((NaryBooleanFormula *) F);
}

void 
FormulaRewritingRule::visit (const DisjunctiveFormula *F)
{
  visit ((NaryBooleanFormula *) F);
}

void 
FormulaRewritingRule::visit (const NegationFormula *F)
{
  visit ((NaryBooleanFormula *) F);
}

void 
FormulaRewritingRule::visit (const QuantifiedFormula *F)
{
  visit ((NaryBooleanFormula *) F);
}

Formula *
FormulaRewritingRule::rewrite (const Formula *F)
{
  return F->ref ();
}

Expr *
FormulaRewritingRule::rewrite (const Expr *E)
{
  return (Expr *) rewrite ((const Formula *) E);
}

Formula *
FormulaRewritingRule::get_result () const
{
  if (result != NULL)
    return result->ref ();
  return NULL;
}

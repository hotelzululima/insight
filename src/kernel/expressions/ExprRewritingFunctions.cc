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
#include <kernel/expressions/ExprRewritingFunctions.hh>

#include <algorithm>
#include <domains/concrete/ConcreteExprSemantics.hh>
#include <domains/concrete/ConcreteValue.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/exprutils.hh>

using namespace std;

void
rewrite_in_place (FunctionRewritingRule::RewriteExprFunc *func, 
		  Expr **pF) 
{
  Expr *newF = func (*pF);

  if (newF != NULL)
    {
      (*pF)->deref ();

      *pF = newF;
    }
}

Expr * 
not_operator_on_constant (const Expr *phi)
{
  const UnaryApp *ua = dynamic_cast<const UnaryApp *> (phi);
  Expr *result = NULL;

  if (ua != NULL && ua->get_op () == BV_OP_NOT && 
      ua->get_arg1()->is_Constant ())
    {
      if (((Constant *) ua->get_arg1())->get_val() == 0)
	result = Constant::one (1);
      else
	result = Constant::zero (1);
    }

  return result;
}

Expr * 
syntaxic_equality_rule (const Expr *phi)
{
  const BinaryApp *ba = dynamic_cast<const BinaryApp *> (phi);
  Expr *result = NULL;

  if (ba != NULL && ba->get_op () == BV_OP_EQ && 
      ba->get_arg1 () == ba->get_arg2 ())
    result = Constant::one (1);

  return result;
}

Expr * 
cancel_lnot_not (const Expr *phi) 
{
  Expr *pattern = 
    Expr::createNot (UnaryApp::create (BV_OP_NOT, Variable::create ("X")));
  Expr *result = exprutils::extract_v_pattern ("X", phi, pattern);
  pattern->deref ();

  return result;
}

Expr * 
logical_negation_operator_on_constant (const Expr *phi)
{
  if (!phi->is_NegationFormula ())
    return NULL;

  const UnaryApp *nf = dynamic_cast<const UnaryApp *> (phi);
  Expr *result = NULL;

  Option<bool> val = nf->get_arg1 ()->try_eval_level0 ();
  if (val.hasValue ())
    {
      if (val.getValue ())
	result = Constant::False ();
      else
	result = Constant::True ();
    }

  return result;
}

Expr *
conjunction_simplification (const Expr *phi) 
{
  if (!phi->is_ConjunctiveFormula ())
    return NULL;

  const BinaryApp *conj = dynamic_cast<const BinaryApp *> (phi);
  Expr *result = NULL;

  if (conj->get_arg1 () == conj->get_arg2 ())
    result = conj->get_arg1 ()->ref ();
  else if (conj->get_arg1 ()->is_TrueFormula ())
    result = conj->get_arg2 ()->ref ();
  else if (conj->get_arg2 ()->is_TrueFormula ())
    result = conj->get_arg1 ()->ref ();
  else if (conj->get_arg1 ()->is_FalseFormula () || 
	   conj->get_arg1 ()->is_FalseFormula ())
    result = Constant::False ();

  return result;
}

Expr *
disjunction_simplification (const Expr *phi) 
{
  if (!phi->is_DisjunctiveFormula ())
    return NULL;

  const BinaryApp *disj = dynamic_cast<const BinaryApp *> (phi);
  Expr *result = NULL;

  if (disj->get_arg1 () == disj->get_arg2 ())
    result = disj->get_arg1 ()->ref ();
  else if (disj->get_arg1 ()->is_FalseFormula ())
    result = disj->get_arg2 ()->ref ();
  else if (disj->get_arg2 ()->is_FalseFormula ())
    result = disj->get_arg1 ()->ref ();
  else if (disj->get_arg1 ()->is_TrueFormula () || 
	   disj->get_arg1 ()->is_TrueFormula ())
    result = Constant::True ();

  return result;
}

Expr * 
and_and_rule (const Expr *phi)
{
  if (!phi->is_ConjunctiveFormula ())
    return NULL;

  const BinaryApp *conj = dynamic_cast<const BinaryApp *> (phi);
  Expr *result = NULL;

  if (! conj->get_arg1()->is_ConjunctiveFormula ())
    return NULL;

  BinaryApp *arg1 = dynamic_cast <BinaryApp *> (conj->get_arg1 ());
  
  // (arg1.1 and  arg1.2) and  arg2 --> arg1.1 and  (arg1.2 and  arg2)
  if (arg1 != NULL) 
    {
      result = BinaryApp::createAnd (arg1->get_arg2 ()->ref (), 
					   conj->get_arg2 ()->ref ());
      result = BinaryApp::createAnd (arg1->get_arg1 ()->ref (), 
					   result);
    }

  return result;
}

Expr * 
or_or_rule (const Expr *phi)
{
  if (!phi->is_DisjunctiveFormula ())
    return NULL;

  const BinaryApp *disj = dynamic_cast<const BinaryApp *> (phi);
  Expr *result = NULL;

  if (! disj->get_arg1()->is_DisjunctiveFormula ())
    return NULL;

  BinaryApp *arg1 = dynamic_cast <BinaryApp *> (disj->get_arg1 ());
  
  // (arg1.1 or  arg1.2) or  arg2 --> arg1.1 or  (arg1.2 or  arg2)
  if (arg1 != NULL) 
    {
      result = BinaryApp::createOr (arg1->get_arg2 ()->ref (), 
					   disj->get_arg2 ()->ref ());
      result = BinaryApp::createOr (arg1->get_arg1 ()->ref (), 
					   result);
    }

  return result;
}

Expr * 
not_decrease (const Expr *phi)
{
  if (!phi->is_NegationFormula ())
    return NULL;

  const UnaryApp *nf = dynamic_cast<const UnaryApp *> (phi);
  Expr *result = NULL;

  const Expr *arg = nf->get_arg1 ();

  if (arg->is_NegationFormula ())
    result = ((UnaryApp *) arg)->get_arg1 ()->ref ();
  else if (arg->is_ConjunctiveFormula () || arg->is_DisjunctiveFormula ())
    {
      BinaryApp *ba = (BinaryApp *) arg;

      Expr *arg1 = UnaryApp::createNot (ba->get_arg1 ()->ref ());
      Expr *arg2 = UnaryApp::createNot (ba->get_arg2 ()->ref ());

      if (ba->get_op() == BV_OP_OR)
	result = BinaryApp::createOr (arg1, arg2);
      else
	result = BinaryApp::createAnd (arg1, arg2);
    }

  return result;
}

Expr *
disjunctive_normal_form_rule (const Expr *phi)
{
  Expr *result = not_decrease (phi);

  if (result != NULL)
    {
      if (phi != result)
	return result;
      else
	{
	  result->deref ();
	  result = NULL;
	}
    }

  if (! phi->is_ConjunctiveFormula ())
    return NULL;

  const BinaryApp *conj = dynamic_cast <const BinaryApp *> (phi);

  BinaryApp *disj = NULL;
  Expr *other;

  if (conj->get_arg1 ()->is_DisjunctiveFormula ())
    {
      disj = (BinaryApp *) conj->get_arg1 ();
      other = conj->get_arg2 ();
    }
  else if (conj->get_arg2 ()->is_DisjunctiveFormula ())
    {
      disj = (BinaryApp *) conj->get_arg2 ();
      other = conj->get_arg1 ();
    }

  if (disj != NULL)
    {
      Expr *c1 = Expr::createAnd (disj->get_arg1 ()->ref (), other->ref ());
      Expr *c2 = Expr::createAnd (disj->get_arg2 ()->ref (), other->ref ());
      result = Expr::createOr (c1, c2);
    }

  return result;
}

static bool 
s_phi_and_not_phi (const Expr *a1, const Expr *a2)
{
  if (a1->is_NegationFormula () && 
      ((UnaryApp *) a1)->get_arg1 () == a2)
    return true;

  if (a2->is_NegationFormula () && 
      ((UnaryApp *) a2)->get_arg1 () == a1)
    return true;

  return false;
}

Expr * 
phi_and_not_phi_rule (const Expr *phi)
{
  Expr *result = NULL;
  BinaryApp *ba = (BinaryApp *) phi;

  if (phi->is_DisjunctiveFormula() && 
      s_phi_and_not_phi (ba->get_arg1 (),ba->get_arg2 ()))
    result = Constant::True ();
  else if (phi->is_ConjunctiveFormula() && 
	   s_phi_and_not_phi (ba->get_arg1 (), ba->get_arg2 ()))
    result = Constant::False (); 

  return result;
}

Expr *
compute_constants (const Expr *e)
{
  Expr *result = NULL;
  int offset = e->get_bv_offset ();
  int size = e->get_bv_size ();

  if (e->is_UnaryApp ()) 
    {
      const UnaryApp * ua = (const UnaryApp *) e;
      Expr * arg = ua->get_arg1();
      if (arg->is_Constant()) 
	{
	  Constant * c = NULL;
	  switch (ua->get_op())
	    {
#define UNARY_OP(_op,_pp)						\
	      case _op:							\
		c = Constant::create (ConcreteExprSemantics::_op ## _eval (((Constant *) arg), offset, size).get(), offset, size); \
		break;
#include <kernel/expressions/Operators.def>
#undef UNARY_OP
	    default:
	      log::fatal_error ("unknown UnaryOp code");
	    }
	  result = c;
	}
    }

  if (e->is_BinaryApp()) 
    {
      const BinaryApp * ba = (BinaryApp *) e;
      Expr * arg1 = ba->get_arg1();
      Expr * arg2 = ba->get_arg2();
      if (arg1->is_Constant() && arg2->is_Constant()) 
	{
	  Constant * c = NULL;
	  switch (ba->get_op())
	    {
#define BINARY_OP(_op,_pp,_commut,_assoc)				\
	      case _op: c = Constant::create (ConcreteExprSemantics::_op ## _eval (((Constant *) arg1),((Constant *) arg2), offset, size).get(), offset, size); \
		break;
#include <kernel/expressions/Operators.def>
#undef BINARY_OP
	    default:
	      log::fatal_error ("unknown UnaryOp code");
	    }
	  result = c;
	}
    }

  return result;
}

Expr *
void_operations (const Expr *e)
{
  Expr *result = NULL;
  const BinaryApp *ba = dynamic_cast<const BinaryApp *> (e);

  if (ba == NULL)
    return NULL;

  BinaryOp op = ba->get_op();

  if ((op == BV_OP_SUB || op == BV_OP_XOR) && 
      ba->get_arg1 () == ba->get_arg2 ()) 
    {
      result = Constant::create (0, ba->get_bv_offset(),  ba->get_bv_size());
    }

  return result;
}

Expr * 
bit_field_computation (const Expr *e)
{
  Expr *result = NULL;
  const Constant *c = dynamic_cast<const Constant *> (e);

  if (c == NULL)
    return NULL;

  //Not -1 because it raises unsignedness error from time to time
  long long max = 1;
  max = (max << (c->get_bv_size() - c->get_bv_offset())) - 1;
  long long min = 0 - max - 1;
  constant_t val = c->get_val();
  if (c->get_bv_offset() > 0 || val > max || val < min)
    {
      unsigned long long v = val;
      unsigned long long mask = 1;
      mask = (mask << (c->get_bv_size())) - 1;
      v = v & mask;
      v = v >> c->get_bv_offset();
      result = Constant::create ((constant_t)v, 0,
				 c->get_bv_size() - 
				 c->get_bv_offset());
    }
  
  return result;
}

Expr * 
binary_operations_simplification (const Expr *e)
{
  Expr *result = NULL;
  const BinaryApp *ba = dynamic_cast<const BinaryApp *> (e);

  if (ba == NULL)
    return NULL;

  Expr *arg1 = ba->get_arg1 ();
  Expr *arg2 = ba->get_arg2 ();
  BinaryOp op = ba->get_op ();

  const BinaryApp *o = dynamic_cast <const BinaryApp *> (arg1);
  if (o == NULL)
    return NULL;

  //Nul element
  if (((o->get_op () == BV_OP_ADD && op == BV_OP_SUB) || 
       (o->get_op () == BV_OP_SUB && op == BV_OP_ADD)) &&
      o->get_arg2 () == arg2)
    {
      result = (Expr *) o->get_arg1()->extract_with_bit_vector_of (ba);
    }
  else if (arg2->is_Constant() && o->get_arg2()->is_Constant()) // OL: ????
    {
      //Distributivity
      constant_t c1 = ((Constant *)arg2)->get_val();
      constant_t c2 = ((Constant *)o->get_arg2())->get_val();
      if ((op == BV_OP_ADD && o->get_op() == BV_OP_ADD) || 
	  (op == BV_OP_SUB && o->get_op() == BV_OP_SUB))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  arg2 = Constant::create (c1 + c2);
	  result = BinaryApp::create (op, arg1, arg2, ba->get_bv_offset(),
				      ba->get_bv_size());
	}
      else if ((op == BV_OP_DIV_U && o->get_op() == BV_OP_DIV_U) || 
	       (op == BV_OP_MUL_U && o->get_op() == BV_OP_MUL_U))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  arg2 = Constant::create (c1 * c2);
	  result = BinaryApp::create (op, arg1, arg2, 
				      ba->get_bv_offset(),
				      ba->get_bv_size());
	}
      else if ((op == BV_OP_ADD && o->get_op() == BV_OP_SUB) || 
	       (op == BV_OP_SUB && o->get_op() == BV_OP_SUB))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  if (c1 - c2 < 0)
	    {
	      arg2 = Constant::create (c2 - c1);
	      op = BV_OP_SUB;
	    }
	  else
	    arg2 = Constant::create (c1 - c2);
	  result = BinaryApp::create (op, arg1, arg2, 
				      ba->get_bv_offset(),
				      ba->get_bv_size());
	}
      else if ((op == BV_OP_SUB && o->get_op() == BV_OP_ADD) || 
	       (op == BV_OP_SUB && o->get_op() == BV_OP_SUB))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  if (c1 - c2 < 0)
	    {
	      arg2 = Constant::create (c2 - c1);
	      op = BV_OP_ADD;
	    }
	  else
	    arg2 = Constant::create (c1 - c2);
	  result = BinaryApp::create (op, arg1, arg2, 
				      ba->get_bv_offset(), 
				      ba->get_bv_size());
	}
    }
  
  return result;
}

Expr * 
simplify_formula (const Expr *phi)
{
  static FunctionRewritingRule::RewriteExprFunc *functions[] = {
    cancel_lnot_not, 
    simplify_expr, 
    syntaxic_equality_rule, 
    not_operator_on_constant, 
    logical_negation_operator_on_constant, 
    conjunction_simplification, 
    disjunction_simplification, 
    phi_and_not_phi_rule, 
    and_and_rule,
    or_or_rule,
    NULL 
  };

  FunctionRewritingRule::RewriteExprFunc **f;
  Expr *result = phi->ref ();
  for (f = functions; *f && result == phi; f++)
    rewrite_in_place (*f, &result);

  return result;
}

Expr * 
simplify_expr (const Expr *phi)
{
  static FunctionRewritingRule::RewriteExprFunc *functions[] = {
    compute_constants, 
    void_operations, 
    bit_field_computation, 
    binary_operations_simplification, 
    NULL 
  };

  FunctionRewritingRule::RewriteExprFunc **f;
  Expr *result = phi->ref ();
  for (f = functions; *f && result == phi; f++)
    rewrite_in_place (*f, &result);

  return result;
}


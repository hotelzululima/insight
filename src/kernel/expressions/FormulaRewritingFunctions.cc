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
#include <kernel/expressions/FormulaRewritingFunctions.hh>

#include <algorithm>
#include <domains/concrete/ConcreteExprSemantics.hh>
#include <domains/concrete/ConcreteValue.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/FormulaUtils.hh>

using namespace std;

void
rewrite_in_place (FunctionRewritingRule::RewriteFormulaFunc *func, 
		  Formula **pF) 
{
  Formula *newF = func (*pF);

  if (newF != NULL)
    {
      (*pF)->deref ();

      *pF = newF;
    }
}

Formula * 
not_operator_on_constant (const Formula *phi)
{
  const UnaryApp *ua = dynamic_cast<const UnaryApp *> (phi);
  Formula *result = NULL;

  if (ua != NULL && ua->get_op () == NOT && ua->get_arg1()->is_Constant ())
    {
      if (((Constant *) ua->get_arg1())->get_val() == 0)
	result = Constant::one (1);
      else
	result = Constant::zero (1);
    }

  return result;
}

Formula * 
syntaxic_equality_rule (const Formula *phi)
{
  const BinaryApp *ba = dynamic_cast<const BinaryApp *> (phi);
  Formula *result = NULL;

  if (ba != NULL && ba->get_op () == EQ && ba->get_arg1 () == ba->get_arg2 ())
    result = Constant::one (1);

  return result;
}

Formula * 
cancel_lnot_not (const Formula *phi) 
{
  Formula *pattern = 
    NegationFormula::create (UnaryApp::create (LNOT, Variable::create ("X")));
  Formula *result = FormulaUtils::extract_v_pattern ("X", phi, pattern);
  pattern->deref ();

  return result;
}

Formula * 
logical_negation_operator_on_constant (const Formula *phi)
{
  const NegationFormula *nf = dynamic_cast<const NegationFormula *> (phi);
  Formula *result = NULL;

  if (nf == NULL)
    return NULL;

  Option<bool> val = nf->get_neg ()->try_eval_level0 ();
  if (val.hasValue ())
    {
      if (val.getValue ())
	result = Constant::False ();
      else
	result = Constant::True ();
    }

  return result;
}

Formula *
conjunction_simplification (const Formula *phi) 
{
  const ConjunctiveFormula *conj = 
    dynamic_cast<const ConjunctiveFormula *> (phi);
  Formula *result = NULL;

  if (conj == NULL)
    return NULL;

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

Formula *
disjunction_simplification (const Formula *phi) 
{
  const DisjunctiveFormula *disj = 
    dynamic_cast<const DisjunctiveFormula *> (phi);
  Formula *result = NULL;

  if (disj == NULL)
    return NULL;

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

Formula * 
and_and_rule (const Formula *phi)
{
  const ConjunctiveFormula *conj = 
    dynamic_cast<const ConjunctiveFormula *> (phi);
  Formula *result = NULL;

  if (conj == NULL)
    return NULL;

  ConjunctiveFormula *arg1 = 
    dynamic_cast <ConjunctiveFormula *> (conj->get_arg1 ());
  
  // (arg1.1 and  arg1.2) and  arg2 --> arg1.1 and  (arg1.2 and  arg2)
  if (arg1 != NULL) 
    {
      result = ConjunctiveFormula::create (arg1->get_arg2 ()->ref (), 
					   conj->get_arg2 ()->ref ());
      result = ConjunctiveFormula::create (arg1->get_arg1 ()->ref (), 
					   result);
    }

  return result;
}

Formula * 
or_or_rule (const Formula *phi)
{
  const DisjunctiveFormula *disj = 
    dynamic_cast<const DisjunctiveFormula *> (phi);
  Formula *result = NULL;

  if (disj == NULL)
    return NULL;

  DisjunctiveFormula *arg1 = 
    dynamic_cast <DisjunctiveFormula *> (disj->get_arg1 ());
  
  // (arg1.1 or  arg1.2) or  arg2 --> arg1.1 or  (arg1.2 or  arg2)
  if (arg1 != NULL) 
    {
      result = DisjunctiveFormula::create (arg1->get_arg2 ()->ref (), 
					   disj->get_arg2 ()->ref ());
      result = DisjunctiveFormula::create (arg1->get_arg1 ()->ref (), 
					   result);
    }

  return result;
}

Formula * 
not_decrease (const Formula *phi)
{
  const NegationFormula *nf = 
    dynamic_cast<const NegationFormula *> (phi);
  Formula *result = NULL;

  if (nf == NULL)
    return NULL;

  const Formula *arg = nf->get_neg ();

  if (arg->is_NegationFormula ())
    result = ((NegationFormula *) arg)->get_neg ()->ref ();
  else if (arg->is_ConjunctiveFormula ())
    {
      ConjunctiveFormula *conj = (ConjunctiveFormula *) arg;

      Formula *arg1 = NegationFormula::create (conj->get_arg1 ()->ref ());
      Formula *arg2 = NegationFormula::create (conj->get_arg2 ()->ref ());
      result = DisjunctiveFormula::create (arg1, arg2);
    }
  else if (arg->is_DisjunctiveFormula ())
    {
      DisjunctiveFormula *conj = (DisjunctiveFormula *) arg;

      Formula *arg1 = NegationFormula::create (conj->get_arg1 ()->ref ());
      Formula *arg2 = NegationFormula::create (conj->get_arg2 ()->ref ());
      result = ConjunctiveFormula::create (arg1, arg2);
    }    

  return result;
}

Formula *
disjunctive_normal_form_rule (const Formula *phi)
{
  Formula *result = not_decrease (phi);

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

  const ConjunctiveFormula *conj = 
    dynamic_cast <const ConjunctiveFormula *> (phi);

  if (conj == NULL)
    return NULL;

  DisjunctiveFormula *disj = 
    dynamic_cast<DisjunctiveFormula *> (conj->get_arg1 ());
  Formula *other;
  if (disj != NULL)
    other = conj->get_arg2 ();
  else 
    {
      disj = dynamic_cast<DisjunctiveFormula *> (conj->get_arg2 ());
      if (disj != NULL)
	other = conj->get_arg1 ();
    }

  if (disj != NULL)
    {
      Formula *c1 = 
	ConjunctiveFormula::create (disj->get_arg1 ()->ref (), other->ref ());
      Formula *c2 = 
	ConjunctiveFormula::create (disj->get_arg2 ()->ref (), other->ref ());
      result = DisjunctiveFormula::create (c1, c2);
    }

  return result;
}

static bool 
s_phi_and_not_phi (const Formula *a1, const Formula *a2)
{
  if (a1->is_NegationFormula () && 
      ((NegationFormula *) a1)->get_neg () == a2)
    return true;

  if (a2->is_NegationFormula () && 
      ((NegationFormula *) a2)->get_neg () == a1)
    return true;

  return false;
}

Formula * 
phi_and_not_phi_rule (const Formula *phi)
{
  Formula *result = NULL;

  if (phi->is_DisjunctiveFormula() &&
      s_phi_and_not_phi (((DisjunctiveFormula *) phi)->get_arg1 (),
			 ((DisjunctiveFormula *) phi)->get_arg2 ()))
    result = Constant::True ();
  else if (phi->is_ConjunctiveFormula() && 
	   s_phi_and_not_phi (((DisjunctiveFormula *) phi)->get_arg1 (),
			      ((DisjunctiveFormula *) phi)->get_arg2 ()))
    result = Constant::False ();

  return result;
}

Formula *
compute_constants (const Formula *phi)
{
  Formula *result = NULL;
  const Expr *e = dynamic_cast<const Expr *> (phi);

  if (e == NULL)
    return NULL;

  int offset = e->get_bv_offset ();
  int size = e->get_bv_size ();

  if (e->is_UnaryApp()) 
    {
      const UnaryApp * ua = (const UnaryApp *) e;
      Expr * arg = ua->get_arg1();
      if (arg->is_Constant()) 
	{
	  Constant * c;
	  switch (ua->get_op())
	    {
#define UNARY_OP(_op,_pp)						\
	      case _op:							\
		c = Constant::create (ConcreteExprSemantics::_op ## _eval (((Constant *) arg), offset, size).get(), offset, size); \
		break;
#include <kernel/expressions/Operators.def>
#undef UNARY_OP
	    default:
	      Log::fatal_error ("unknown UnaryOp code");
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
	  Constant * c;
	  switch (ba->get_op())
	    {
#define BINARY_OP(_op,_pp,_commut,_assoc)				\
	      case _op: c = Constant::create (ConcreteExprSemantics::_op ## _eval (((Constant *) arg1),((Constant *) arg2), offset, size).get(), offset, size); \
		break;
#include <kernel/expressions/Operators.def>
#undef BINARY_OP
	    default:
	      Log::fatal_error ("unknown UnaryOp code");
	    }
	  result = c;
	}
    }

  return result;
}

Formula *
void_operations (const Formula *e)
{
  Formula *result = NULL;
  const BinaryApp *ba = dynamic_cast<const BinaryApp*> (e);

  if (ba == NULL)
    return NULL;

  BinaryOp op = ba->get_op();

  if ((op == SUB || op == XOR) && ba->get_arg1() == ba->get_arg2()) 
    {
      result = Constant::create (0, ba->get_bv_offset(),  ba->get_bv_size());
    }

  return result;
}

Formula * 
bit_field_computation (const Formula *e)
{
  Formula *result = NULL;
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

Formula * 
binary_operations_simplification (const Formula *e)
{
  Formula *result = NULL;
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
  if (((o->get_op () == ADD && op == SUB) || 
       (o->get_op () == SUB && op == ADD)) &&
      o->get_arg2 () == arg2)
    {
      result = (Expr *) o->get_arg1()->extract_with_bit_vector_of (ba);
    }
  else if (arg2->is_Constant() && o->get_arg2()->is_Constant()) // OL: ????
    {
      //Distributivity
      constant_t c1 = ((Constant *)arg2)->get_val();
      constant_t c2 = ((Constant *)o->get_arg2())->get_val();
      if ((op == ADD && o->get_op() == ADD) || 
	  (op == SUB && o->get_op() == SUB))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  arg2 = Constant::create (c1 + c2);
	  result = BinaryApp::create (op, arg1, arg2, ba->get_bv_offset(),
				      ba->get_bv_size());
	}
      else if ((op == DIV_U && o->get_op() == DIV_U) || 
	       (op == MUL_U && o->get_op() == MUL_U))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  arg2 = Constant::create (c1 * c2);
	  result = BinaryApp::create (op, arg1, arg2, 
				      ba->get_bv_offset(),
				      ba->get_bv_size());
	}
      else if ((op == ADD && o->get_op() == SUB) || 
	       (op == SUB && o->get_op() == SUB))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  if (c1 - c2 < 0)
	    {
	      arg2 = Constant::create (c2 - c1);
	      op = SUB;
	    }
	  else
	    arg2 = Constant::create (c1 - c2);
	  result = BinaryApp::create (op, arg1, arg2, 
				      ba->get_bv_offset(),
				      ba->get_bv_size());
	}
      else if ((op == SUB && o->get_op() == ADD) || 
	       (op == SUB && o->get_op() == SUB))
	{
	  arg1 = (Expr *)o->get_arg1()->ref ();
	  if (c1 - c2 < 0)
	    {
	      arg2 = Constant::create (c2 - c1);
	      op = ADD;
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

Formula * 
simplify_formula (const Formula *phi)
{
  static FunctionRewritingRule::RewriteFormulaFunc *functions[] = {
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

  FunctionRewritingRule::RewriteFormulaFunc **f;
  Formula *result = phi->ref ();
  for (f = functions; *f && result == phi; f++)
    rewrite_in_place (*f, &result);

  return result;
}

Formula * 
simplify_expr (const Formula *phi)
{
  static FunctionRewritingRule::RewriteFormulaFunc *functions[] = {
    compute_constants, 
    void_operations, 
    bit_field_computation, 
    binary_operations_simplification, 
    NULL 
  };

  FunctionRewritingRule::RewriteFormulaFunc **f;
  Formula *result = phi->ref ();
  for (f = functions; *f && result == phi; f++)
    rewrite_in_place (*f, &result);

  return result;
}


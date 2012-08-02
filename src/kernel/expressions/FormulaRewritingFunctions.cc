/*
 * The insight library and accompanying tools are distributed under a
 * 2-clause "BSD license", as below.

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
    result = Constant::zero (1);
  else
    result = Constant::one (1);

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

  bool change = false;
  vector<Formula *> new_clauses;
  vector<Formula *>::const_iterator cl = conj->get_clauses().begin ();
  vector<Formula *>::const_iterator end_cl = conj->get_clauses().end ();

  for (; cl != end_cl && result == NULL; cl++)
    {
      if (find (new_clauses.begin(),
		new_clauses.end(), *cl) != new_clauses.end())
	{
	  change = true;  // Cheap optimization
	  continue;
	}

      Option<bool> val = (*cl)->try_eval_level0();
      if (val.hasValue ())
	{
	  if (val.getValue ())
	    {
	      change = true;
	      continue;
	    }
	  else
	    {
	      result = Constant::zero (1);
	    }
	}
      else
	{
	  new_clauses.push_back (*cl);
	}
    }

  if (change && result == NULL)
    {
      if (new_clauses.size() >= 2)
	{
	  for(vector<Formula *>::iterator cl = new_clauses.begin ();
	      cl != new_clauses.end (); cl++)
	    (*cl) = (Formula *) (*cl)->ref ();

	  result = ConjunctiveFormula::create (new_clauses);
	}
      else if (new_clauses.size() == 1)
	{
	  result = (Formula *) new_clauses[0]->ref ();
	}
      else
	result = Constant::one (1);
    }

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

  bool change = false;
  vector<Formula *> new_clauses;
  vector<Formula *>::const_iterator cl = disj->get_clauses().begin ();
  vector<Formula *>::const_iterator end_cl = disj->get_clauses().end ();

  for (; cl != end_cl && result == NULL; cl++)
    {
      if (find(new_clauses.begin(), 
	       new_clauses.end(), *cl) != new_clauses.end())
	{
	  change = true;  // Cheap optimization
	  continue;
	}

      Option<bool> val = (*cl)->try_eval_level0 ();
      if (val.hasValue ())
	{
	  if (val.getValue())
	    result = Constant::one (1);
	  else
	    {
	      change = true;
	      continue;
	    }
	}
      else
	{
	  new_clauses.push_back (*cl);
	}
    }

  if (change && result == NULL)
    {
      if (new_clauses.size() >= 2)
	{
	  for(vector<Formula *>::iterator cl = new_clauses.begin ();
	      cl != new_clauses.end (); cl++)
	    (*cl) = (Formula *) (*cl)->ref ();

	  result = DisjunctiveFormula::create (new_clauses);
	}
      else if (new_clauses.size() == 1)
	{
	  result = (Formula *) new_clauses[0]->ref ();
	}
      else
	{
	  result = Constant::zero (1);
	}
    }

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

  const vector<Formula *> &conj_clauses = conj->get_clauses();
  vector<Formula *>::const_iterator psi = conj_clauses.begin();

  while (psi != conj_clauses.end() && !((*psi)->is_ConjunctiveFormula())) 
    psi++;

  if (psi != conj_clauses.end() && (*psi)->is_ConjunctiveFormula())
    {
      vector<Formula *> new_clauses;     
      ConjunctiveFormula *int_phi = (ConjunctiveFormula *) * psi;

      for (vector<Formula *>::const_iterator c = conj_clauses.begin(); 
	   c != conj_clauses.end(); c++) {
	if (c != psi)
	  new_clauses.push_back ((Formula *)(*c)->ref ());
      }
      // TODO ((ConjunctiveFormula*) phi)->get_clauses().erase(psi);

      vector<Formula *> int_clauses = int_phi->get_clauses();
      for (vector<Formula *>::iterator c = int_clauses.begin(); 
	   c != int_clauses.end(); c++)
	new_clauses.push_back ((Formula *)(*c)->ref ());

      result = ConjunctiveFormula::create (new_clauses);
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

  const vector<Formula *> &disj_clauses = disj->get_clauses();
  vector<Formula *>::const_iterator psi = disj_clauses.begin();

  while (psi != disj_clauses.end() && !((*psi)->is_DisjunctiveFormula())) 
    psi++;
  if (psi != disj_clauses.end() && (*psi)->is_DisjunctiveFormula())
    {
      vector<Formula *> new_clauses;     
      DisjunctiveFormula *int_phi = (DisjunctiveFormula *) * psi;

      for (vector<Formula *>::const_iterator c = disj_clauses.begin(); 
	   c != disj_clauses.end(); c++) {
	if (c != psi)
	  new_clauses.push_back ((Formula *)(*c)->ref ());
      }
      // TODO ((DisjunctiveFormula*) phi)->get_clauses().erase(psi);

      vector<Formula *> int_clauses = int_phi->get_clauses();
      for (vector<Formula *>::iterator c = int_clauses.begin(); 
	   c != int_clauses.end(); c++)
	new_clauses.push_back ((Formula *)(*c)->ref ());

      result = DisjunctiveFormula::create (new_clauses);
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
      vector<Formula *> new_clauses;
      ConjunctiveFormula *conj = (ConjunctiveFormula *) arg;
      vector<Formula *>::const_iterator c = conj->get_clauses().begin ();
      vector<Formula *>::const_iterator end = conj->get_clauses().end ();

      for (; c != end; c++) 
	{
	  Formula *cc = (*c)->ref ();
	  new_clauses.push_back (NegationFormula::create (cc));
	}

      result = DisjunctiveFormula::create (new_clauses);
    }
  else if (arg->is_DisjunctiveFormula ())
    {
      vector<Formula *> new_clauses;
      DisjunctiveFormula *disj = (DisjunctiveFormula *) arg;
      vector<Formula *>::const_iterator c = disj->get_clauses().begin ();
      vector<Formula *>::const_iterator end = disj->get_clauses().end ();

      for (; c != end; c++) 
	{
	  Formula *cc = (*c)->ref ();
	  new_clauses.push_back (NegationFormula::create (cc));
	}
	  
      result = ConjunctiveFormula::create (new_clauses);
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

  if (conj != NULL)
    {
      const vector<Formula *> &conj_clauses = conj->get_clauses ();
      vector<Formula *>::const_iterator psi = conj_clauses.begin ();

      while (psi != conj_clauses.end() && !((*psi)->is_DisjunctiveFormula())) 
	psi++;

      if (psi != conj_clauses.end() && (*psi)->is_DisjunctiveFormula())
        {
	  vector<Formula *> new_clauses;
          vector<Formula *> disj_clauses = 
	    ((DisjunctiveFormula *)(*psi))->get_clauses();

          for (vector<Formula *>::iterator disj_cl = disj_clauses.begin(); 
	       disj_cl != disj_clauses.end(); disj_cl++)
            {
              vector<Formula *> new_conj_clauses;

              new_conj_clauses.push_back ((Formula *)(*disj_cl)->ref ());

              for (vector<Formula *>::const_iterator conj_cl = 
		     conj_clauses.begin(); conj_cl != conj_clauses.end(); 
		   conj_cl++) {
                if (conj_cl != psi)
                  new_conj_clauses.push_back ((Formula *)(*conj_cl)->ref ());
	      }
	      Formula *new_clause = 
		ConjunctiveFormula::create (new_conj_clauses);
              new_clauses.push_back (new_clause);
            }

          result = DisjunctiveFormula::create (new_clauses);
        }
    }

  return result;
}

static bool 
s_phi_and_not_phi (const vector<Formula *> &l)
{
  if (l.size() <= 1) 
    return false;

  vector<Formula *>::const_iterator phi = l.begin();
  phi++;

  for (; phi != l.end(); phi++)
    {
      for (vector<Formula *>::const_iterator psi = l.begin(); psi != phi; psi++)
        {
          if ((*psi)->is_NegationFormula())
            if (((NegationFormula *)(*psi))->get_neg() == *phi)
              return true;

          if ((*phi)->is_NegationFormula())
            {
              if (((NegationFormula *)(*phi))->get_neg() == *psi)
                return true;
            }
        }
    }
  return false;
}

Formula * 
phi_and_not_phi_rule (const Formula *phi)
{
  Formula *result = NULL;

  if (phi->is_DisjunctiveFormula() &&
      s_phi_and_not_phi (((DisjunctiveFormula *) phi)->get_clauses ()))
    result = Constant::one (1);
  else if (phi->is_ConjunctiveFormula() && 
	   s_phi_and_not_phi (((ConjunctiveFormula *) phi)->get_clauses ()))
    result = Constant::zero (1);

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


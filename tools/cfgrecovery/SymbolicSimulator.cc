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
#include <tr1/unordered_map>
#include <kernel/annotations/AsmAnnotation.hh>
#include <kernel/expressions/exprutils.hh>
#include <kernel/expressions/ExprSolver.hh>
#include <kernel/expressions/ExprRewritingRule.hh>
#include <domains/symbolic/SymbolicExprSemantics.hh>
#include "SymbolicSimulator.hh"

using namespace std::tr1;
using namespace std;

class SymbolicSimulator::StateSpace 
  : public unordered_map<MicrocodeAddress, SymbolicState *> {
};

SymbolicSimulator::SymbolicSimulator(const ConcreteMemory *mem, Decoder *dec, 
				     Microcode *prog)
  : base (mem), decoder (dec), program (prog)
{
  solver = ExprSolver::create_default_solver (dec->get_arch ());
  states = new StateSpace ();
  arch = decoder->get_arch ()->get_reference_arch ();
}

SymbolicSimulator::~SymbolicSimulator () 
{
  delete states;
  delete solver;
}

SymbolicState *
SymbolicSimulator::init (const ConcreteAddress &entrypoint)
{
  MicrocodeAddress start (entrypoint.get_address ());
  SymbolicMemory *mem = new SymbolicMemory (base);
  Expr *cond = Constant::True ();

  return new SymbolicState (start, mem, cond);
}

SymbolicSimulator::ArrowSet 
SymbolicSimulator::get_arrows (const SymbolicState *ctx) const
  throw (Decoder::Exception)
{
  MicrocodeAddress pp = ctx->get_address ();
  MicrocodeNode *node = get_node (pp);
  ArrowSet result;

  MicrocodeNode_iterate_successors(*node, succ)
    result.push_back (*succ);

  return result;
}

class RewriteWithAssignedValues : public ExprRewritingRule {
  const SymbolicState *ctx;  
  const Architecture::endianness_t endianness;
public:
  RewriteWithAssignedValues (const SymbolicState *ctx, 
			     Architecture::endianness_t e) 
    : ctx (ctx), endianness (e) {
  }

  virtual Expr *rewrite (const Expr *F) {
    Expr *result = NULL;
    int offset = F->get_bv_offset ();
    int size = F->get_bv_size ();
    Option<SymbolicValue> val;

    if (F->is_RegisterExpr ()) 
      {
	RegisterExpr *regexpr = (RegisterExpr *) F;
	const RegisterDesc *rdesc = regexpr->get_descriptor ();

	if (! ctx->get_memory ()->is_defined (rdesc))
	  {
	    int regsize = rdesc->get_register_size ();
	    SymbolicValue unk = SymbolicValue::unknown_value (regsize);
	    ctx->get_memory ()->put (rdesc, unk);
	  }
	val = ctx->get_memory ()->get (rdesc);
      } 
    else if (F->is_MemCell ()) 
      {
	MemCell *mc = (MemCell *) F;      
	Expr *addr = mc->get_addr()->ref ();
	exprutils::simplify (&addr);
	Constant *c = dynamic_cast<Constant *> (addr);
	if (c != NULL)
	  {
	    int i;
	    int size = (mc->get_bv_offset() + mc->get_bv_size () - 1) / 8 + 1;
	    for (i = 0; i < size; i++)
	      if (! ctx->get_memory ()->is_defined (c->get_val () + i))
		break;
	    if (i == size)
	      val = ctx->get_memory ()->get (c->get_val (), size, endianness);
	    else
	      val = SymbolicValue::unknown_value (size * 8);
	  }
	addr->deref ();
    } 
    
    if (val.hasValue ())
      {
	SymbolicValue sv = 
	  SymbolicExprSemantics::extract_eval (val.getValue (), offset, size); 
	result = sv.get_Expr ()->ref ();
      }

    if (result == NULL)
      result = F->ref ();

    return result;
  }
};


MicrocodeNode * 
SymbolicSimulator::get_node (const MicrocodeAddress &pp) const
  throw (Decoder::Exception)
{
  bool is_global = (pp.getLocal () == 0);
  MicrocodeNode *result = NULL;
  Microcode *mc = dynamic_cast<Microcode *> (program);
  assert (mc != NULL);

  try
    {
      result = program->get_node (pp);
      if (is_global && ! result->has_annotation (AsmAnnotation::ID))
	{
	  // result is a node added by the decoder but asm instruction at
	  // pp.to_address () has not yet been decoded.
	  MicrocodeAddress addr = result->get_loc ();
	  assert (addr.getLocal () == 0);
	  decoder->decode (mc, ConcreteAddress (addr.getGlobal ()));
	}	
    }
  catch (GetNodeNotFoundExc &)
    {
      if (! is_global)
	throw;
      decoder->decode (mc, ConcreteAddress (pp.getGlobal ()));
      result = program->get_node (pp);
    }

  return result;
}

const Microcode * 
SymbolicSimulator::get_program () const 
{
  return program;
}

void 
SymbolicSimulator::step (SymbolicState *ctxt, const StaticArrow *sa)
{
  assert (ctxt != NULL);

  MicrocodeAddress tgt = sa->get_target ();
  
  exec (ctxt, sa->get_stmt (), tgt);
}

void 
SymbolicSimulator::step (SymbolicState *&ctxt, const DynamicArrow *da)
{
  assert (ctxt != NULL);

  Expr *addr = da->get_target ();
  assert (! da->get_stmt()->is_Assignment ());

  Option<SymbolicValue> svaddr = eval (ctxt, addr);
  if (svaddr.hasValue ())
    {
      const Constant *c = 
	dynamic_cast<const Constant *> (svaddr.getValue ().get_Expr ());

      if (c != NULL)
	{
	  MicrocodeAddress tgt (c->get_val ());
	  ctxt->set_address (tgt);
	  program->add_skip (ctxt->get_address (), tgt, 
			     ctxt->get_condition ()->ref ());
	}
      else
	{
	  delete ctxt;
	  ctxt = NULL;
	}
    }
  else
    {
      delete ctxt;
      ctxt = NULL;
    }
}

SymbolicState *
SymbolicSimulator::step (const SymbolicState *ctx, const StmtArrow *arrow)
{
  SymbolicState *result = check_guard (ctx, arrow->get_condition ());

  if (result == NULL)
    return result;

  try
    {
      /* determination of the target node */
      if (arrow->is_static ())
	step (result, (StaticArrow *) arrow);
      else
	step (result, (DynamicArrow *) arrow);
    }
  catch (UndefinedValueException &e)
    {
      if (result != NULL)
	delete result;
      throw;
    }
  
  return result;
}

SymbolicValue
SymbolicSimulator::eval (const SymbolicState *ctx, const Expr *e) const
{
  SymbolicValue result;
  RewriteWithAssignedValues r (ctx, arch->endianness);
  Expr *f = e->ref ();

  for (;;)
    {
      f->acceptVisitor (r);
      Expr *aux = r.get_result ();
      f->deref ();
      if (aux == f)
	break;
      f = aux;
    }
  
  Constant *c = solver->evaluate (f, ctx->get_condition ());
  if (c != NULL)
    {
      f->deref ();
      f = c;
    }

  result = SymbolicValue (f);
  f->deref ();

  return result;
}

void
SymbolicSimulator::exec (SymbolicState *ctxt, const Statement *st,
			 const MicrocodeAddress &tgt) const
{
  if (ctxt == NULL)
    return;

  ctxt->set_address (tgt);

  const Assignment *assign = dynamic_cast<const Assignment *> (st);
  if (assign == NULL)
    return;

  SymbolicMemory *memory = ctxt->get_memory ();

  
  if (assign->get_lval()->is_MemCell())
    {
      const MemCell *cell = dynamic_cast<const MemCell *> (assign->get_lval());

      assert (cell->get_bv_offset () == 0);
      assert (cell->get_bv_size () == assign->get_rval()->get_bv_size ());
      
      ConcreteAddress a (eval (ctxt, cell->get_addr ()));
      SymbolicValue v (simplify (ctxt, assign->get_rval()));

      memory->put (a, v, arch->endianness);
    }
  else if (assign->get_lval()->is_RegisterExpr())
    {
      RegisterExpr *reg = (RegisterExpr *) assign->get_lval();
      const RegisterDesc *rdesc = reg->get_descriptor();
      SymbolicValue v (simplify (ctxt, assign->get_rval ()));
      SymbolicValue regval;
      
      if (v.get_size () != rdesc->get_register_size ())
	{
	  if (ctxt->get_memory ()->is_defined (rdesc))
	    regval = ctxt->get_memory ()->get (rdesc);
	  else 
	    regval = SymbolicValue::unknown_value (rdesc->get_window_size ());
	  
	  v = SymbolicExprSemantics::embed_eval (regval, v, 
						 reg->get_bv_offset());	  
	  v.simplify ();
	}
      
      memory->put (rdesc, v);
    }
}

Option<bool> 
SymbolicSimulator::to_bool (const SymbolicState *ctx, const Expr *e) const
{
  Option<bool> result;
  RewriteWithAssignedValues r (ctx, arch->endianness);
  Expr *f = e->ref ();
  f->acceptVisitor (r);
  f->deref ();
  f = r.get_result ();

  ExprSolver::Result sat = solver->check_sat (f, true);
  if (sat == ExprSolver::SAT)
    {
      f = Expr::createLNot (f);
      sat = solver->check_sat (f, true);
      if (sat  == ExprSolver::UNSAT)
	result = true;
    }
  else if (sat == ExprSolver::UNSAT)
    {
      result = false;
    }

  f->deref ();

  return result;
}

SymbolicState *
SymbolicSimulator::check_guard (const SymbolicState *ctx, 
				const Expr *cond) const
{
  SymbolicState *result = NULL;
  Expr *e = Expr::createLAnd (ctx->get_condition ()->ref (), cond->ref ());
  Option<bool> eval = to_bool (ctx, e);

  if (eval.hasValue ())
    {
      if (eval.getValue ())
	result = ctx->clone ();
      e->deref ();
    }
  else
    {      
      exprutils::simplify_level0 (&e);
      result = ctx->clone ();
      result->set_condition (e);
    }
  
  return result;
}

SymbolicValue 
SymbolicSimulator::simplify (const SymbolicState *ctx, const Expr *e) const
{
  SymbolicValue res = eval (ctx, e);

  if (! res.get_Expr ()->is_Constant ())
    res.simplify ();

  return res;
}

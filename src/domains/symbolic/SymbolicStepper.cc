
#include <exception>

#include <kernel/expressions/exprutils.hh>
#include <kernel/expressions/ExprRewritingRule.hh>
#include <kernel/expressions/ExprSolver.hh>

#include "SymbolicStepper.hh"

namespace SymbStepper {
  class RewriteWithAssignedValues : public ExprRewritingRule {
    const SymbolicContext *ctx;  
    const Architecture::endianness_t endianness;
  public:
    RewriteWithAssignedValues (const SymbolicContext *ctx, 
			       Architecture::endianness_t e) 
      : ctx (ctx), endianness (e) {
    }

    virtual Expr *rewrite (const Expr *F) {
      Expr *result = NULL;
      int offset = F->get_bv_offset ();
      int size = F->get_bv_size ();
      Option<SymbolicValue> val;

      if (F->is_RandomValue ()) 
	val = SymbolicValue::unknown_value (size);
      else if (F->is_RegisterExpr ()) 
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
		{
		  SymbolicValue v = SymbolicValue::unknown_value (size * 8);
		  ctx->get_memory ()->put (ConcreteAddress (c->get_val ()), v,
					   endianness);
		  val = v;
		}
	    }
	  addr->deref ();
	} 
    
      if (val.hasValue ())
	{
	  SymbolicValue sv = 
	    SymbolicExprSemantics::extract_eval (val.getValue (), offset, 
						 size); 
	  result = sv.get_Expr ()->ref ();
	}

      if (result == NULL)
	result = F->ref ();

      return result;
    }
  };
}

using namespace SymbStepper;

SymbolicStepper::SymbolicStepper (ConcreteMemory *memory, 
				  const MicrocodeArchitecture *arch)
  : Super (arch->get_reference_arch ()), memory (memory)
    
{
  solver = ExprSolver::create_default_solver (arch);
  if (solver == NULL)
    throw std::runtime_error("can't create default solver");
}

SymbolicStepper::~SymbolicStepper () {
  delete solver;
}

ConcreteValue 
SymbolicStepper::value_to_ConcreteValue (const Context *ctx, const Value &v, 
					 bool *is_unique)
  throw (UndefinedValueException)
{
  if (v.get_Expr() == NULL)
    throw UndefinedValueException (v.to_string ());

  const SymbolicContext *sc = dynamic_cast<const SymbolicContext *> (ctx);
  assert (sc != NULL);
  RewriteWithAssignedValues r (sc, this->arch->get_endian ());
  Expr *f = v.get_Expr ()->ref ();

  for (;;)
    {
      f->acceptVisitor (r);
      Expr *aux = r.get_result ();
      f->deref ();
      if (aux == f)
	break;
      f = aux;
    }
  exprutils::simplify (&f);

  Expr *cond = sc->get_path_condition ()->ref ();
  
  std::vector<constant_t> *values = 
    solver->evaluate (f, cond, is_unique ? 2 : 1);
  f->deref ();
  cond->deref ();

  if (values->size () == 0)
    {
      delete values;
      throw UndefinedValueException (v.to_string ());
    }
  ConcreteValue result (f->get_bv_size (), values->at (0));
  if (is_unique)
    *is_unique = (values->size () == 1);
  delete values;

  return result;    
}

SymbolicStepper::Address 
SymbolicStepper::value_to_address (const Context *, const Value &v) 
  throw (UndefinedValueException)
{
  return (SymbolicStepper::Address) v;
}

static Expr *
s_expr_in_range (const Expr *e, address_t min, address_t max)
{
  Expr *in1 = BinaryApp::create (BV_OP_LEQ_U, 
				 Constant::create (min, 0, e->get_bv_size ()),
				 e->ref (), 0, 1);
  Expr *in2 = BinaryApp::create (BV_OP_LEQ_U, 
				 e->ref (),
				 Constant::create (max, 0, e->get_bv_size ()),
				 0, 1);
  return Expr::createLAnd (in1, in2);
}

void
s_expand_memcell_indexes_rec (class ExprSolver *solver,
			      std::vector<const Expr *> *indexes, 
			      std::vector<Expr *>::size_type current, 
			      const SymbolicContext *ctx, const Expr *e, 
			      const Expr *cond, const Architecture *arch, 
			      std::vector<Expr *> *result, int jmpthreshold)
{
  if (current < indexes->size ())
    {
      int th = jmpthreshold;
      const Expr *index = indexes->at (current);

      std::vector<constant_t> *tmp = solver->evaluate (index, cond, th);

      if (th >= 0 && (int)tmp->size () > th)
	tmp->clear ();
      
      for (std::vector<constant_t>::size_type i = 0; i < tmp->size (); i++)
	{
	  Constant *cst = Constant::create (tmp->at (i), 
					    index->get_bv_offset (),
					    index->get_bv_size ());
	  Expr *ne = exprutils::replace_subterm (e, index, cst);
	  s_expand_memcell_indexes_rec (solver, indexes, current + 1, ctx, ne,
					cond, arch, result, jmpthreshold);
	  ne->deref ();
	  cst->deref ();
	}
      delete tmp;
    }
  else
    {
      RewriteWithAssignedValues r (ctx, arch->get_endian ());
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

      result->push_back (f);
    }
}

std::vector<Expr *> *
s_expand_memcell_indexes (class ExprSolver *solver, const Architecture *arch, 
			  const SymbolicContext *ctx, const Expr *e,
			  const Expr *cond, int jmpthreshold)
{
  std::vector<Expr *> *result = new std::vector<Expr *>;
  std::vector<const Expr *> *indexes = exprutils::collect_memcell_indexes (e);
  s_expand_memcell_indexes_rec (solver, indexes, 0, ctx, e, cond, arch, result,
				jmpthreshold);
  delete (indexes);

  return result;
}

std::vector<address_t> *
SymbolicStepper::value_to_concrete_addresses (const Context *ctx, 
					      const Value &v) 
  throw (UndefinedValueException) 
{
  const SymbolicContext *sc = dynamic_cast<const SymbolicContext *> (ctx);
  assert (sc != NULL);

  std::vector<address_t> *result = new std::vector<address_t> ();
  RewriteWithAssignedValues r (sc, this->arch->get_endian ());
  const Expr *e = v.get_Expr ();
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

  address_t range[2];
  sc->get_memory ()->get_address_range (range[0], range[1]);
  Expr *cond = sc->get_path_condition ()->ref ();
      
  if (this->map_dynamic_jumps_to_memory)
    cond = Expr::createLAnd (s_expr_in_range (e, range[0], range[1]), cond);
      
  for (;;)
    {
      cond->acceptVisitor (r);
      Expr *aux = r.get_result ();
      cond->deref ();
      if (aux == cond)
	break;
      cond = aux;
    }

  std::vector<Expr *> *expaddr = 
    s_expand_memcell_indexes (solver, this->arch, sc, f, cond, 
			      this->dynamic_jump_threshold);
  for (std::vector<Expr *>::size_type i = 0; i < expaddr->size (); i++)
    {
      int th = this->dynamic_jump_threshold;
      Expr *aux = expaddr->at (i);
      std::vector<constant_t> *tmp = solver->evaluate (aux, cond, th);
      aux->deref ();

      if (th >= 0 && (int)tmp->size () >= th)
	tmp->clear ();
      
      for (size_t i = 0; i < tmp->size (); i++)
	result->push_back (tmp->at (i));
      delete tmp;
    }
  delete (expaddr);

  f->deref ();
  cond->deref ();

  assert (result != NULL);

  return result;  
}

SymbolicStepper::Value 
SymbolicStepper::eval (const Context *ctx, const Expr *e) 
  throw (UndefinedValueException)
{
  SymbolicStepper::Value result;
  const SymbolicContext *sc = dynamic_cast<const SymbolicContext *> (ctx);
  assert (sc != NULL);
  RewriteWithAssignedValues r (sc, this->arch->get_endian ());
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
  exprutils::simplify (&f);
  Constant *c = solver->evaluate (f, sc->get_path_condition ());
  if (c != NULL)
    {
      f->deref ();
      f = c;
    }

  result = SymbolicValue (f);
  f->deref ();

  if (! result.get_Expr ()->is_Constant ())
    result.simplify ();

  return result;
}

SymbolicStepper::Value 
SymbolicStepper::embed_eval (const SymbolicStepper::Value &v1, 
			     const SymbolicStepper::Value &v2, 
			     int off) const
{
  return SymbolicExprSemantics::embed_eval (v1, v2, off);
}
    

static Option<bool> 
s_to_bool (ExprSolver *solver, const Architecture *arch, 
	   const SymbolicContext *ctx, const Expr *e, 
	   Expr **symbval) 
{
  Option<bool> result;
  RewriteWithAssignedValues r (ctx, arch->get_endian ());
  Expr *f = e->ref ();
  f->acceptVisitor (r);
  f->deref ();
  f = r.get_result ();

  ExprSolver::Result sat = solver->check_sat (f, true);
  if (sat == ExprSolver::SAT)
    {
      Expr *tmp = Expr::createLNot (f->ref ());
      sat = solver->check_sat (tmp, true);
      if (sat  == ExprSolver::UNSAT)
	result = true;
      tmp->deref ();
    }
  else if (sat == ExprSolver::UNSAT)
    {
      result = false;
    }

  if (! result.hasValue () && symbval != NULL)
    *symbval = f;
  else
    f->deref ();

  return result;
}

SymbolicStepper::Context * 
SymbolicStepper::restrict_to_condition (const Context *ctx, const Expr *cond)
{
  const SymbolicContext *sc = dynamic_cast<const SymbolicContext *> (ctx);
  assert (sc != NULL);
  SymbolicContext *result = NULL;
  Expr *e = Expr::createLAnd (sc->get_path_condition ()->ref (), cond->ref ());
  Expr *val = NULL;
  Option<bool> eval = s_to_bool (solver, this->arch, sc, e, &val);

  if (eval.hasValue ())
    {
      assert (val == NULL);
      if (eval.getValue ())
	result = sc->clone ();
    }
  else
    {      
      assert (val != NULL);
      exprutils::simplify_level0 (&val);
      result = sc->clone ();
      result->set_path_condition (val);
    }
  e->deref ();

  return result;
}

SymbolicStepper::State *
SymbolicStepper::get_initial_state (const ConcreteAddress &entrypoint)
{
  MicrocodeAddress ma (entrypoint.get_address ());
  State *result = new State (new ProgramPoint (ma), 
			     new Context (new SymbolicMemory (memory), 
					  Constant::True ()));

  return result;
}

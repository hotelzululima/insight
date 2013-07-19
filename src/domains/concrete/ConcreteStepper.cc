#include <kernel/expressions/exprutils.hh>
#include <kernel/expressions/ExprRewritingRule.hh>
#include "ConcreteStepper.hh"

namespace ConcStepper {
  class RewriteWithAssignedValues : public ExprRewritingRule {
    const ConcreteContext *ctx;  
    const Architecture::endianness_t endianness;
  public:
    RewriteWithAssignedValues (const ConcreteContext *ctx, 
			       Architecture::endianness_t e) 
      : ctx (ctx), endianness (e) {
    }

    virtual Expr *rewrite (const Expr *F) {
      Expr *result = NULL;
      int offset = F->get_bv_offset ();
      int size = F->get_bv_size ();
      Option<ConcreteValue> val;

      if (F->is_RegisterExpr ()) 
	{
	  RegisterExpr *regexpr = (RegisterExpr *) F;
	  const RegisterDesc *rdesc = regexpr->get_descriptor ();

	  if (ctx->get_memory ()->is_defined (rdesc))
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
	    }
	  addr->deref ();
	} 
    
      if (val.hasValue ())
	result = Constant::create (val.getValue ().get (), offset, size); 

      if (result == NULL)
	result = F->ref ();

      return result;
    }
  };
}

using namespace ConcStepper;

ConcreteStepper::ConcreteStepper (ConcreteMemory *memory, 
				  const MicrocodeArchitecture *arch)
  : Super (arch->get_reference_arch ()), memory (memory)
    
{
}

ConcreteStepper::~ConcreteStepper () 
{
}

ConcreteStepper::Address 
ConcreteStepper::value_to_address (const ConcreteStepper::Context *, 
				   const ConcreteStepper::Value &v) 
  throw (UndefinedValueException)
{
  return ConcreteStepper::Address (v.get ());
}

std::vector<address_t> *
ConcreteStepper::value_to_concrete_addresses (const Context *, const Value &v) 
  throw (UndefinedValueException) 
{
  std::vector<address_t> *result = new std::vector<address_t> ();
  result->push_back (v.get ());

  return result;  
}

ConcreteStepper::Value 
ConcreteStepper::eval (const Context *ctx, const Expr *e) 
    throw (UndefinedValueException)
{
  Option<ConcreteStepper::Value> result;
  const ConcreteContext *sc = dynamic_cast<const ConcreteContext *> (ctx);
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
  if (f->is_Constant ())
    result = ConcreteValue ((Constant *) f);
  f->deref ();

  if (!result.hasValue ())
    throw UndefinedValueException (e->to_string ());

  return result.getValue ();
}

ConcreteStepper::Value 
ConcreteStepper::embed_eval (const ConcreteStepper::Value &v1, 
			     const ConcreteStepper::Value &v2, 
			     int off) const
{
  return ConcreteExprSemantics::embed_eval (v1, v2, off);
}
    
ConcreteStepper::Context * 
ConcreteStepper::restrict_to_condition (const Context *ctx, const Expr *cond)
{
  ConcreteContext *result = NULL;

  if ((bool) eval (ctx, cond).get ())
    result = ctx->clone ();
  
  return result;
}

ConcreteStepper::State *
ConcreteStepper::get_initial_state (const ConcreteAddress &entrypoint)
{
  MicrocodeAddress ma (entrypoint.get_address ());
  State *result = new State (new ProgramPoint (ma), 
			     new Context (new ConcreteMemory (memory)));

  return result;
}


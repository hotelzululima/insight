#include "SymbolicContext.hh"

SymbolicContext::SymbolicContext (SymbolicMemory *mem, Expr *cond)
  : AbstractDomainContext<SymbolicMemory> (mem), condition (cond)
{
}

SymbolicContext::~SymbolicContext ()
{
  condition->deref ();
}

bool
SymbolicContext::equals (const AbstractContext *ctx) const
{
  const SymbolicContext *sctx = dynamic_cast<const SymbolicContext *> (ctx);

  return (sctx != NULL && SType::equals ((const SType *) ctx) &&
	  condition == sctx->condition);
}

std::size_t
SymbolicContext::hashcode () const
{
  return (13 * SType::hashcode () + 141 * condition->hash ());
}

void
SymbolicContext::output_text (std::ostream &out) const
{
  SType::output_text (out);
  out << "condition = " << *condition << std::endl;
}

const Expr *
SymbolicContext::get_path_condition () const
{
  return condition;
}

void
SymbolicContext::set_path_condition (Expr *cond)
{
  condition->deref ();
  condition = cond;
}

SymbolicContext *
SymbolicContext::clone () const
{
  return new SymbolicContext (memory->clone (), condition->ref ());
}

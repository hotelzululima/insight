#include "ConcreteContext.hh"

ConcreteContext::ConcreteContext (ConcreteMemory *mem) 
  : AbstractDomainContext<ConcreteMemory>  (mem)
{
}

ConcreteContext::~ConcreteContext () 
{
}

ConcreteContext *
ConcreteContext::clone () const 
{
  return new ConcreteContext (new ConcreteMemory (*memory));
}

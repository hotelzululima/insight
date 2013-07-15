#include "NullContext.hh"


NullContext::NullContext () : AbstractContext ()
{
}

NullContext::~NullContext () 
{ 
}

bool 
NullContext::equals (const AbstractContext *other) const 
{ 
  return dynamic_cast<const NullContext *>(other) == this;
}

std::size_t 
NullContext::hashcode () const 
{
  return (std::size_t) this;
}

void 
NullContext::output_text (std::ostream &out) const 
{
  out << "null context";
}

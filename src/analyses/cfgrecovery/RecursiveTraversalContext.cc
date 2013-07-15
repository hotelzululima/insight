#include "RecursiveTraversal.hh"


RecursiveTraversal::Context::Context () 
  : AbstractContext(), stack (), hvalue (0) 
{ 
}

RecursiveTraversal::Context::Context (const CallStack &cs) 
  : AbstractContext(), stack (cs) 
{
  compute_hvalue ();
}

RecursiveTraversal::Context::~Context () 
{ 
}
    
bool 
RecursiveTraversal::Context::equals (const AbstractContext *other) const 
{
  const Context *rtctx = dynamic_cast<const Context *> (other);
  return hvalue == rtctx->hvalue && stack == rtctx->stack;
}

bool 
RecursiveTraversal::Context::empty () const 
{
  return stack.empty ();
}

RecursiveTraversal::Context *
RecursiveTraversal::Context::push (const ConcreteAddress &ca) const 
{
  Context *result = new Context ();
  result->stack = stack;
  result->stack.push_front (ca);
  
  return result;
}

ConcreteAddress 
RecursiveTraversal::Context::top () const 
{
  assert (! empty ());
  return stack.front ();
}

RecursiveTraversal::Context *
RecursiveTraversal::Context::pop () const 
{
  assert (! empty ());
  
  Context *result = new Context ();
  result->stack = stack;
  result->stack.pop_front ();
  
  return result;
}

RecursiveTraversal::Context *
RecursiveTraversal::Context::clone () const 
{
  return new RecursiveTraversal::Context (stack);
}

std::size_t 
RecursiveTraversal::Context::hashcode () const 
{
  return hvalue;
}

void 
RecursiveTraversal::Context::output_text (std::ostream &out) const 
{
  out << "[";
  for (CallStack::const_iterator i = stack.begin (); i != stack.end (); 
       i++)
    out << " " << (*i);
  out << " ]";
}

void 
RecursiveTraversal::Context::compute_hvalue () 
{
  hvalue = 0;
  for (CallStack::const_iterator i = stack.begin (); i != stack.end (); 
       i++)
    hvalue = (hvalue << 3) + 13 * (i->get_address ());
}

#include "AbstractContext.hh"

AbstractContext::AbstractContext () : refcount (1)
{
}

AbstractContext::~AbstractContext ()
{
}

void
AbstractContext::ref () const
{
  refcount++;
}

void
AbstractContext::deref ()
{
  if (--refcount == 0)
    delete this;
}


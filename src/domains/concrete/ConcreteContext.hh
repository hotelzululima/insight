#ifndef CONCRETECONTEXT_HH
# define CONCRETECONTEXT_HH

# include <analyses/cfgrecovery/AbstractDomainContext.hh>
# include <domains/concrete/ConcreteMemory.hh>

class ConcreteContext : public AbstractDomainContext<ConcreteMemory>
{
public:
  ConcreteContext (ConcreteMemory *mem);
  virtual ~ConcreteContext ();

  virtual ConcreteContext *clone () const ;
};

#endif /* ! CONCRETECONTEXT_HH */

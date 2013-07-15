#ifndef ABSTRACTDOMAINCONTEXT_HH
# define ABSTRACTDOMAINCONTEXT_HH

# include <cassert>
# include <analyses/cfgrecovery/AbstractContext.hh>

template <typename MEM>
class AbstractDomainContext : public AbstractContext 
{

public:
  typedef MEM Memory;
  
  AbstractDomainContext (Memory *mem);

  virtual ~AbstractDomainContext ();

  virtual Memory *get_memory () const;

  virtual bool equals (const AbstractContext *ctx) const;

  virtual std::size_t hashcode () const;

  virtual void output_text (std::ostream &out) const;

protected:
  Memory *memory;
};

# include <analyses/cfgrecovery/AbstractDomainContext.ii>

#endif /* ! ABSTRACTDOMAINCONTEXT_HH */

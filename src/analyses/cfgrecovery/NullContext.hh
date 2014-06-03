#ifndef NULLCONTEXT_HH
# define NULLCONTEXT_HH

# include <analyses/cfgrecovery/AbstractContext.hh>

class NullContext : public AbstractContext
{
public:
  NullContext ();
  virtual ~NullContext ();

  virtual bool equals (const AbstractContext *other) const;

  virtual std::size_t hashcode () const;

  virtual void output_text (std::ostream &out) const;
};

#endif /* ! NULLCONTEXT_HH */

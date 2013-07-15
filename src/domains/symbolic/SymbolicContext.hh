#ifndef SYMBOLICCONTEXT_HH
# define SYMBOLICCONTEXT_HH

# include <analyses/cfgrecovery/AbstractDomainContext.hh>
# include <kernel/Expressions.hh>
# include <domains/symbolic/SymbolicMemory.hh>

class SymbolicContext : public AbstractDomainContext<SymbolicMemory>
{
  typedef AbstractDomainContext<SymbolicMemory> SType;

public:
  SymbolicContext (SymbolicMemory *mem, Expr *cond); 

  virtual ~SymbolicContext ();

  virtual bool equals (const AbstractContext *ctx) const;

  virtual std::size_t hashcode () const;
  virtual void output_text (std::ostream &out) const;
  virtual const Expr *get_path_condition () const;
  virtual void set_path_condition (Expr *cond);    
  virtual SymbolicContext *clone () const;

protected:
  Expr *condition;
};

#endif /* ! SYMBOLICCONTEXT_HH */

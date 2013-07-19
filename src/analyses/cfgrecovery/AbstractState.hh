#ifndef ABSTRACTSTATE_HH
# define ABSTRACTSTATE_HH

# include <analyses/cfgrecovery/AbstractProgramPoint.hh>
# include <analyses/cfgrecovery/AbstractContext.hh>

template<typename PP, typename CTX>
class AbstractState : public Object 
{
public:
  typedef PP ProgramPoint;
  typedef CTX Context;

  AbstractState (ProgramPoint *pp, Context *ctx);

  virtual ProgramPoint *get_ProgramPoint () const;
  virtual Context *get_Context () const;
  virtual bool equals (const AbstractState<ProgramPoint,Context> *s) const;
  virtual std::size_t hashcode () const;
  virtual void output_text (std::ostream &out) const;
  virtual AbstractState<PP,CTX> *clone () const;
  void ref () const;
  void deref ();

protected:
  virtual ~AbstractState ();

private:
  ProgramPoint *program_point;
  Context *context;
  mutable int refcount;
};

#include <analyses/cfgrecovery/AbstractState.ii>

#endif /* ! ABSTRACTSTATE_HH */

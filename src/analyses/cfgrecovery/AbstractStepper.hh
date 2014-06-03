#ifndef ABSTRACTSTEPPER_HH
# define ABSTRACTSTEPPER_HH

# include <set>
# include <kernel/Microcode.hh>
# include <analyses/cfgrecovery/AbstractState.hh>

template<typename S>
class AbstractStepper
{
public:
  typedef S State;
  typedef typename S::ProgramPoint ProgramPoint;
  typedef typename S::Context Context;
  typedef std::set<State *> StateSet;

  virtual ~AbstractStepper () { }

  virtual State *get_initial_state (const ConcreteAddress &entrypoint) = 0;

  virtual StateSet *get_successors (const State *s, const StmtArrow *arrow) = 0;
};

#endif /* ! ABSTRACTSTEPPER_HH */

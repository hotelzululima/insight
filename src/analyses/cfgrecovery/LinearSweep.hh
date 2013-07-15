#ifndef LINEARSWEEP_HH
# define LINEARSWEEP_HH

# include <analyses/cfgrecovery/NullContext.hh>
# include <analyses/cfgrecovery/MicrocodeAddressProgramPoint.hh>
# include <analyses/cfgrecovery/AbstractStepper.hh>
# include <analyses/cfgrecovery/SingleContextStateSpace.hh>
# include <analyses/cfgrecovery/AbstractMemoryTraversal.hh>

class LinearSweep
{
public:
  typedef NullContext Context;
  typedef MicrocodeAddressProgramPoint ProgramPoint;
  typedef AbstractState<ProgramPoint, Context> State;
  typedef SingleContextStateSpace<State> StateSpace;

  class Stepper : public AbstractStepper<State> {
  public:
    Stepper ();
    virtual ~Stepper ();

    virtual State *get_initial_state (const ConcreteAddress &entrypoint);
    
    virtual StateSet *get_successors (const State *s, const StmtArrow *arrow);

    static bool compute_successor (const StmtArrow *arrow,
				   MicrocodeAddress &result);
  };

  typedef AbstractMemoryTraversal<LinearSweep> Traversal;
};

#endif /* ! LINEARSWEEP_HH */

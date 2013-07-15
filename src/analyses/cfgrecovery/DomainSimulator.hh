#ifndef DOMAINSIMULATOR_HH
# define DOMAINSIMULATOR_HH

# include <analyses/cfgrecovery/AbstractMemoryTraversal.hh>

template<typename S>
class DomainSimulator
{
public:
  typedef S Stepper;
  typedef typename Stepper::ProgramPoint ProgramPoint;
  typedef typename Stepper::Context Context;
  typedef typename Stepper::State State;
  typedef SingleContextStateSpace<State> StateSpace;
  typedef AbstractMemoryTraversal< DomainSimulator<S> > Traversal;
};

#endif /* ! DOMAINSIMULATOR_HH */

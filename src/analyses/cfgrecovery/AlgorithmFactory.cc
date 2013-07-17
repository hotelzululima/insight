#include <cassert>

#include "LinearSweep.hh"
#include "FloodTraversal.hh"
#include "RecursiveTraversal.hh"

#include <domains/symbolic/SymbolicStepper.hh>
#include <domains/concrete/ConcreteStepper.hh>
#include "DomainSimulator.hh"

#include "AlgorithmFactory.hh"

typedef DomainSimulator<SymbolicStepper> SymbolicSimulator;
typedef DomainSimulator<ConcreteStepper> ConcreteSimulator;

template<typename SIMULATOR>
class GenAlgorithm : public AlgorithmFactory::Algorithm
{  
public:
  typedef typename SIMULATOR::Stepper Stepper;
  typedef typename SIMULATOR::StateSpace StateSpace;
  typedef typename SIMULATOR::Traversal Traversal;

public:
  GenAlgorithm () 
    : Algorithm (), stepper (NULL), states (NULL), traversal (NULL) {
  }

  virtual ~GenAlgorithm () {
    delete stepper;
    delete states;
    delete traversal;
  }

  virtual void setup_stepper (AlgorithmFactory *F) {
  }

  virtual void setup_traversal (AlgorithmFactory *F) {
    assert (stepper != NULL);

    states = new StateSpace ();
    traversal = new Traversal (F->get_memory (), F->get_decoder (), stepper, 
			       states);

    traversal->set_show_states (F->get_show_states ());
    traversal->set_show_state_space_size (F->get_show_state_space_size ());
    traversal->set_show_pending_arrows (F->get_show_pending_arrows ());
    traversal->set_warn_on_unsolved_dynamic_jumps (F->get_warn_on_unsolved_dynamic_jumps ());
    traversal->set_warn_skipped_dynamic_jumps (F->get_warn_skipped_dynamic_jumps ());
    traversal->set_number_of_visits_per_address (F->get_max_number_of_visits_per_address ());   
  }

  virtual void setup (AlgorithmFactory *factory) {
    setup_stepper (factory);
    setup_traversal (factory);
  }

  virtual void stop () {
    if (traversal)
      traversal->abort_computation ();
  }

  virtual void compute (const ConcreteAddress &entrypoint, Microcode *result) {
    traversal->compute (entrypoint, result);
  }

private:
  friend class AlgorithmFactory;
  Stepper *stepper;
  StateSpace *states;
  Traversal *traversal;      
};

AlgorithmFactory::AlgorithmFactory () 
{
#define ALGORITHM_FACTORY_PROPERTY(type_, name_, defval_) name_ = defval_;  
  ALGORITHM_FACTORY_PROPERTIES
#undef ALGORITHM_FACTORY_PROPERTY
}

AlgorithmFactory::~AlgorithmFactory ()
{
}

template<> void 
GenAlgorithm<LinearSweep>::setup_stepper (AlgorithmFactory *)
{
  stepper = new LinearSweep::Stepper ();
}

AlgorithmFactory::Algorithm *
AlgorithmFactory::buildLinearSweep ()
{
  Algorithm *result = new GenAlgorithm<LinearSweep> ();

  result->setup (this);

  return result;
}

template<> void 
GenAlgorithm<FloodTraversal>::setup_stepper (AlgorithmFactory *F)
{
  const Architecture *arch = 
    F->get_decoder ()->get_arch ()->get_reference_arch();
  stepper = new FloodTraversal::Stepper (F->get_memory (), arch);
}

AlgorithmFactory::Algorithm *
AlgorithmFactory::buildFloodTraversal ()
{
  Algorithm *result = new GenAlgorithm<FloodTraversal> ();

  result->setup (this);

  return result;
}

template<> void 
GenAlgorithm<RecursiveTraversal>::setup_stepper (AlgorithmFactory *F)
{
  const Architecture *arch = 
    F->get_decoder ()->get_arch ()->get_reference_arch();
  stepper = new RecursiveTraversal::Stepper (F->get_memory (), arch);
}

AlgorithmFactory::Algorithm *
AlgorithmFactory::buildRecursiveTraversal ()
{
  Algorithm *result = new GenAlgorithm<RecursiveTraversal> ();

  result->setup (this);

  return result;
}

template<> void 
GenAlgorithm<SymbolicSimulator>::setup_stepper (AlgorithmFactory *F)
{
  stepper = 
    new SymbolicSimulator::Stepper (F->get_memory (), 
				    F->get_decoder ()->get_arch ());
  
  stepper->set_dynamic_jump_threshold (F->get_dynamic_jumps_threshold ());
  stepper->set_map_dynamic_jumps_to_memory (F->get_map_dynamic_jumps_to_memory ());  
}

AlgorithmFactory::Algorithm *
AlgorithmFactory::buildSymbolicSimulator ()
{
  Algorithm *result = new GenAlgorithm<SymbolicSimulator> ();

  result->setup (this);

  return result;
}

template<> void 
GenAlgorithm<ConcreteSimulator>::setup_stepper (AlgorithmFactory *F)
{
  stepper = 
    new ConcreteSimulator::Stepper (F->get_memory (), 
				    F->get_decoder ()->get_arch ());
}

AlgorithmFactory::Algorithm *
AlgorithmFactory::buildConcreteSimulator ()
{
  Algorithm *result =  new GenAlgorithm<ConcreteSimulator> ();

  result->setup (this);

  return result;
}


#ifndef ABSTRACTMEMORYTRAVERSAL_HH
# define ABSTRACTMEMORYTRAVERSAL_HH

# include <list>
# include <decoders/Decoder.hh>
# include <utils/logs.hh>
# include <kernel/Microcode.hh>
# include <kernel/annotations/AsmAnnotation.hh>
# include <kernel/annotations/NextInstAnnotation.hh>
# include <tr1/unordered_map>

template<typename AlgoSpec>
class AbstractMemoryTraversal 
{
public:
  typedef typename AlgoSpec::Stepper Stepper;
  typedef typename AlgoSpec::StateSpace StateSpace;

  typedef typename Stepper::Context Context;
  typedef typename Stepper::ProgramPoint ProgramPoint;
  typedef typename Stepper::State State;
  typedef typename Stepper::StateSet StateSet;

  struct PendingArrow {
    const State *s;
    StmtArrow *arrow;
  };

  AbstractMemoryTraversal (ConcreteMemory *memory, Decoder *decoder, 
			   Stepper *stepper, StateSpace *states, Microcode *mc);

  virtual ~AbstractMemoryTraversal ();

  void set_show_states (bool value);

  void set_show_pending_arrows (bool value);

  void set_number_of_visits_per_address (int value);

  void compute (const ConcreteAddress &entrypoint);
    
  PendingArrow nextPendinArrow ();

  bool skip_pending_arrow (const PendingArrow &pa);

  void computePendingArrowsFor (State *s)
    throw (Decoder::Exception);

  MicrocodeNode *get_node (const ProgramPoint *pp)
    throw (Decoder::Exception);

private:

  ConcreteMemory *memory;
  std::list<PendingArrow> worklist;
  Stepper *stepper;
  Decoder *decoder;
  Microcode *program;
  StateSpace *states;
  int nb_visits_per_address;
  std::tr1::unordered_map<address_t,int> visits;
  bool show_states;
  bool show_pending_arrows;
};

# include <analyses/cfgrecovery/AbstractMemoryTraversal.ii>

#endif /* ! ABSTRACTMEMORYTRAVERSAL_HH */

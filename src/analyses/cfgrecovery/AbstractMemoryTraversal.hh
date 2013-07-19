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
# define ABSTRACT_MEMORY_TRAVERSAL_PROPERTIES				\
  ABSTRACT_MEMORY_TRAVERSAL_PROPERTY (bool, show_states, false)		\
  ABSTRACT_MEMORY_TRAVERSAL_PROPERTY (bool, show_state_space_size, false) \
  ABSTRACT_MEMORY_TRAVERSAL_PROPERTY (bool, show_pending_arrows, false)	\
  ABSTRACT_MEMORY_TRAVERSAL_PROPERTY (bool, warn_on_unsolved_dynamic_jumps, \
				      false)				\
  ABSTRACT_MEMORY_TRAVERSAL_PROPERTY (bool, warn_skipped_dynamic_jumps, false) \
  ABSTRACT_MEMORY_TRAVERSAL_PROPERTY (int, number_of_visits_per_address, 1)
# undef ABSTRACT_MEMORY_TRAVERSAL_PROPERTY

public:
  typedef typename AlgoSpec::Stepper Stepper;
  typedef typename AlgoSpec::StateSpace StateSpace;

  typedef typename Stepper::Context Context;
  typedef typename Stepper::ProgramPoint ProgramPoint;
  typedef typename Stepper::State State;
  typedef typename Stepper::StateSet StateSet;

  struct PendingArrow {
    State *s;
    StmtArrow *arrow;
  };

  AbstractMemoryTraversal (ConcreteMemory *memory, Decoder *decoder, 
			   Stepper *stepper, StateSpace *states);

  virtual ~AbstractMemoryTraversal ();

  void abort_computation ();

  void compute (const ConcreteAddress &entrypoint, Microcode *result);
    
protected:
  virtual MicrocodeNode *get_node (const ProgramPoint *pp)
    throw (Decoder::Exception);

  virtual PendingArrow nextPendingArrow ();

  virtual bool skip_pending_arrow (const PendingArrow &pa);

  virtual void computePendingArrowsFor (State *s)
    throw (Decoder::Exception);
private:
  ConcreteMemory *memory;
  std::list<PendingArrow> worklist;
  Stepper *stepper;
  Decoder *decoder;
  Microcode *program;
  StateSpace *states;
  std::tr1::unordered_map<address_t,int> visits;
  bool stop_computation;

# define ABSTRACT_MEMORY_TRAVERSAL_PROPERTY(type_, name_, defval_)	\
  private: type_ name_; \
  public: void set_ ## name_ (type_ value) { name_ = value; } 

  ABSTRACT_MEMORY_TRAVERSAL_PROPERTIES
# undef ABSTRACT_MEMORY_TRAVERSAL_PROPERTY
};

# include <analyses/cfgrecovery/AbstractMemoryTraversal.ii>

#endif /* ! ABSTRACTMEMORYTRAVERSAL_HH */

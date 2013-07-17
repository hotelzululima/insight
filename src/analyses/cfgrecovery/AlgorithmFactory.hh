#ifndef ALGORITHMFACTORY_HH
# define ALGORITHMFACTORY_HH

# include <kernel/Microcode.hh>
# include <decoders/Decoder.hh>

class AlgorithmFactory 
{
# define ALGORITHM_FACTORY_PROPERTIES					\
  ALGORITHM_FACTORY_PROPERTY (ConcreteMemory *, memory, NULL)		\
  ALGORITHM_FACTORY_PROPERTY (Decoder *, decoder, NULL)			\
  ALGORITHM_FACTORY_PROPERTY (bool, show_states, false)			\
  ALGORITHM_FACTORY_PROPERTY (bool, show_state_space_size, false)	\
  ALGORITHM_FACTORY_PROPERTY (bool, show_pending_arrows, false)		\
  ALGORITHM_FACTORY_PROPERTY (bool, warn_on_unsolved_dynamic_jumps, false) \
  ALGORITHM_FACTORY_PROPERTY (bool, warn_skipped_dynamic_jumps, false)	\
  ALGORITHM_FACTORY_PROPERTY (bool, map_dynamic_jumps_to_memory, false)	\
  ALGORITHM_FACTORY_PROPERTY (int, dynamic_jumps_threshold, 1000) 	\
  ALGORITHM_FACTORY_PROPERTY (int, max_number_of_visits_per_address, 1)

public:
  class Algorithm {
  protected:
    friend class AlgorithmFactory;
    virtual void setup (AlgorithmFactory *factory) = 0;

  public:
    virtual ~Algorithm () { }
    virtual void stop () = 0;
    virtual void compute (const ConcreteAddress &ca, Microcode *result) = 0;

  };
  
  AlgorithmFactory ();
  ~AlgorithmFactory ();

  Algorithm *buildLinearSweep ();
  Algorithm *buildFloodTraversal ();
  Algorithm *buildRecursiveTraversal ();
  Algorithm *buildSymbolicSimulator ();
  Algorithm *buildConcreteSimulator ();

# define ALGORITHM_FACTORY_PROPERTY(type_, name_, defval_)	\
  private: type_ name_;						\
  public: void set_ ## name_ (type_ value) { name_ = value; }	\
  public: type_ get_ ## name_ () { return name_;} 
  
  ALGORITHM_FACTORY_PROPERTIES
# undef ALGORITHM_FACTORY_PROPERTY
};

#endif /* ! ALGORITHMFACTORY_HH */

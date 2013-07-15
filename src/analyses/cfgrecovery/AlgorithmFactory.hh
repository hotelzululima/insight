#ifndef ALGORITHMFACTORY_HH
# define ALGORITHMFACTORY_HH

# include <kernel/Microcode.hh>
# include <decoders/Decoder.hh>

class AlgorithmFactory 
{
public:
  class Algorithm {
  protected:
    friend class AlgorithmFactory;
    virtual void setup (AlgorithmFactory *factory) = 0;

  public:
    virtual ~Algorithm () { }
    virtual void compute (const ConcreteAddress &ca, Microcode *result) = 0;

  };
  
  AlgorithmFactory ();
  ~AlgorithmFactory ();

  void set_memory (ConcreteMemory *memory);
  ConcreteMemory *get_memory ();
  void set_decoder (Decoder *decoder);
  Decoder *get_decoder ();

  void set_show_states (bool value);
  bool get_show_states ();
  void set_show_pending_arrows (bool value);
  bool get_show_pending_arrows ();
  void set_warn_on_unsolved_dynamic_jumps (bool value);
  bool get_warn_on_unsolved_dynamic_jumps ();

  void set_map_dynamic_jumps_to_memory (bool value);
  bool get_map_dynamic_jumps_to_memory ();
  void set_dynamic_jumps_threshold (int threshold);
  int get_dynamic_jumps_threshold ();
  void set_max_number_of_visits_per_address (int max_nb_visits);
  int get_max_number_of_visits_per_address ();

  Algorithm *buildLinearSweep ();
  Algorithm *buildFloodTraversal ();
  Algorithm *buildRecursiveTraversal ();
  Algorithm *buildSymbolicSimulator ();
  Algorithm *buildConcreteSimulator ();

private:
  ConcreteMemory *memory;
  Decoder *decoder;

  bool show_states;
  bool show_pending_arrows;
  bool warn_on_unsolved_dynamic_jumps;

  bool map_dynamic_jumps_to_memory;
  int dynamic_jumps_threshold;
  int max_number_of_visits_per_address;
};

#endif /* ! ALGORITHMFACTORY_HH */

#include <domains/symbolic/SymbolicStepper.hh>
#include <domains/concrete/ConcreteStepper.hh>
#include <analyses/cfgrecovery/DomainSimulator.hh>
#include <utils/logs.hh>
#include <simulator.hh>

typedef DomainSimulator<SymbolicStepper> SymbolicSimulator;
typedef DomainSimulator<ConcreteStepper> ConcreteSimulator;

const std::string SIMULATOR_X86_32_INIT_ESP_PROP =
  "disas.simulator.x86_32.init-esp";
const std::string SIMULATOR_X86_32_INIT_EBP_PROP =
  "disas.simulator.x86_32.init-ebp";
const std::string SIMULATOR_NB_VISITS_PER_ADDRESS =
  "disas.simulator.nb-visits-per-address";
const std::string SIMULATOR_WARN_UNSOLVED_DYNAMIC_JUMPS =
  "disas.simulator.warn-unsolved-dynamic-jumps";
const std::string SIMULATOR_DEBUG_SHOW_STATES =
  "disas.simulator.debug.show-states";
const std::string SIMULATOR_DEBUG_SHOW_PENDING_ARROWS =
  "disas.simulator.debug.show-pending-arrows";

const std::string SYMSIM_DYNAMIC_JUMP_THRESHOLD =
  "disas.symsim.dynamic-jump-threshold";
const std::string SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY =
  "disas.symsim.map-dynamic-jump-to-memory";


static void
s_symbolic_stepper_setup (SymbolicSimulator::Stepper *stepper)
{
  int djmpth = CFGRECOVERY_CONFIG->get_integer (SYMSIM_DYNAMIC_JUMP_THRESHOLD);
  bool djmp2mem = 
    CFGRECOVERY_CONFIG->get_boolean (SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY);

  stepper->set_dynamic_jump_threshold (djmpth);
  stepper->set_map_dynamic_jumps_to_memory (djmp2mem);
}

#define s_concrete_stepper_setup NULL

template<typename SIMULATOR>
static Microcode *
simulate (const ConcreteAddress *entrypoint, ConcreteMemory *memory,
	  Decoder *decoder,
	  void (*stepper_setup) (typename SIMULATOR::Stepper *))
{
  typedef typename SIMULATOR::Stepper Stepper;
  typedef typename SIMULATOR::StateSpace StateSpace;
  typedef typename SIMULATOR::Traversal Traversal;

  Microcode *result = new Microcode ();  
  Stepper *stepper = new Stepper (memory, decoder->get_arch ());
  StateSpace *states = new StateSpace ();
  Traversal rec (memory, decoder, stepper, states, result);

  bool warn_unsolved = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_WARN_UNSOLVED_DYNAMIC_JUMPS, 
				     false);
  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATES, false);
  bool show_pending_arrows = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_PENDING_ARROWS, 
				     false);
  rec.set_warn_on_unsolved_dynamic_jump (warn_unsolved);
  rec.set_show_states (show_states);
  rec.set_show_pending_arrows (show_pending_arrows);
  int max_nb_visits =
    CFGRECOVERY_CONFIG->get_integer (SIMULATOR_NB_VISITS_PER_ADDRESS, 0);

  if (max_nb_visits > 0 && verbosity)
    {
      logs::warning << "warning: restrict number of visits per program point "
		    << "to " << std::dec << max_nb_visits << " visits." 
		    << std::endl;
    }
  rec.set_number_of_visits_per_address (max_nb_visits);
  if (stepper_setup != NULL)
    stepper_setup (stepper);


  if (decoder->get_arch ()->get_proc () == Architecture::X86_32)
    {
      if (CFGRECOVERY_CONFIG->has (SIMULATOR_X86_32_INIT_ESP_PROP))
	{
	  long valesp = 
	    CFGRECOVERY_CONFIG->get_integer (SIMULATOR_X86_32_INIT_ESP_PROP);
	  if (verbosity)
	    logs::warning << "warning: setting %esp to " << std::hex << "0x" 
			  << valesp << std::endl;
	  
	  Constant *c = Constant::create (valesp, 0, 32);
	  
	  memory->put (decoder->get_arch ()->get_register ("esp"),  c);
	  c->deref ();
	}
      if (CFGRECOVERY_CONFIG->has (SIMULATOR_X86_32_INIT_EBP_PROP))
	{
	  long valesp = 
	    CFGRECOVERY_CONFIG->get_integer (SIMULATOR_X86_32_INIT_EBP_PROP);
	  if (verbosity)
	    logs::warning << "warning: setting %ebp to " << std::hex << "0x" 
			  << valesp << std::endl;
	  
	  Constant *c = Constant::create (valesp, 0, 32);
	  
	  memory->put (decoder->get_arch ()->get_register ("ebp"),  c);
	  c->deref ();
	}
    }

  rec.compute (*entrypoint);

  delete stepper;
  delete states;
  
  return result;
}

Microcode *
simulator (const ConcreteAddress *entrypoint, ConcreteMemory *memory,
	   Decoder *decoder, DomainName dom)
{
  Microcode *result = NULL;

  switch (dom)
    {
    case SYMBOLIC_DOMAIN: 
      result = simulate<SymbolicSimulator> (entrypoint, memory, decoder, 
					    s_symbolic_stepper_setup);
      break;
    case CONCRETE_DOMAIN: 
      result = simulate<ConcreteSimulator> (entrypoint, memory, decoder, 
					    s_concrete_stepper_setup);
      break;
    }

  return result;
}



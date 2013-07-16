#include <analyses/cfgrecovery/AlgorithmFactory.hh>
#include "cfgrecovery.hh"
#include "algorithms.hh"

static const std::string SIMULATOR_X86_32_INIT_ESP_PROP =
  "disas.simulator.x86_32.init-esp";
static const std::string SIMULATOR_X86_32_ZERO_REGISTERS =
  "disas.simulator.x86_32.zero-registers";
static const std::string SIMULATOR_NB_VISITS_PER_ADDRESS =
  "disas.simulator.nb-visits-per-address";
static const std::string SIMULATOR_WARN_UNSOLVED_DYNAMIC_JUMPS =
  "disas.simulator.warn-unsolved-dynamic-jumps";
static const std::string SIMULATOR_DEBUG_SHOW_STATES =
  "disas.simulator.debug.show-states";
static const std::string SIMULATOR_DEBUG_SHOW_PENDING_ARROWS =
  "disas.simulator.debug.show-pending-arrows";

static const std::string SYMSIM_DYNAMIC_JUMP_THRESHOLD =
  "disas.symsim.dynamic-jump-threshold";
static const std::string SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY =
  "disas.symsim.map-dynamic-jump-to-memory";

typedef AlgorithmFactory::Algorithm * (AlgorithmFactory::* FactoryMethod) ();

static Microcode *
s_generic_call (const ConcreteAddress &entrypoint, ConcreteMemory *memory,
		Decoder *decoder, FactoryMethod build)
{
  Microcode *result = new Microcode ();
  AlgorithmFactory F;

  if (decoder->get_arch ()->get_proc () == Architecture::X86_32)
    {
      if (CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_X86_32_ZERO_REGISTERS, 
					   false))
	{	
	  const Architecture *arch = 
	    decoder->get_arch ()->get_reference_arch ();
	  
	  for (RegisterSpecs::const_iterator i = 
		 arch->get_registers ()->begin ();
	       i != arch->get_registers ()->end (); i++)
	    {
	      if (i->second->is_alias ())
		continue;
	      
	      Constant *c = 
		Constant::create (0, 0, i->second->get_register_size ());
	      
	      memory->put (i->second,  c);
	      c->deref ();
	    }
	}
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
    }

  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATES, false);
  bool show_pending_arrows = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_PENDING_ARROWS, 
				     false);
  bool warn_unsolved_jumps =
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_WARN_UNSOLVED_DYNAMIC_JUMPS, 
				     false);
  int max_nb_visits =
    CFGRECOVERY_CONFIG->get_integer (SIMULATOR_NB_VISITS_PER_ADDRESS, 0);

  if (max_nb_visits > 0 && verbosity)
    {
      logs::warning << "warning: restrict number of visits per program point "
		    << "to " << std::dec << max_nb_visits << " visits." 
		    << std::endl;
    }
  int djmpth = 
    CFGRECOVERY_CONFIG->get_integer (SYMSIM_DYNAMIC_JUMP_THRESHOLD);
  bool djmp2mem = 
    CFGRECOVERY_CONFIG->get_boolean (SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY);

  F.set_memory (memory);
  F.set_decoder (decoder); 
  F.set_show_states (show_states);
  F.set_show_pending_arrows (show_pending_arrows);
  F.set_warn_on_unsolved_dynamic_jumps (warn_unsolved_jumps);
  F.set_map_dynamic_jumps_to_memory (djmp2mem);
  F.set_dynamic_jumps_threshold (djmpth);
  F.set_max_number_of_visits_per_address (max_nb_visits);
 
  AlgorithmFactory::Algorithm *algo = (F.* build) ();

  try
    {
      algo->compute (entrypoint, result);
      delete algo;
    }
  catch (Decoder::Exception &)
    {
      delete algo;
      delete result;
      throw;
    }
  return result;
}

Microcode * 
linear_sweep(const ConcreteAddress &entrypoint, ConcreteMemory * memory,
	    Decoder * decoder)
  throw (Decoder::Exception &)
{ 
  return s_generic_call (entrypoint, memory, decoder, 
			 &AlgorithmFactory::buildLinearSweep);
}

Microcode *
flood_traversal (const ConcreteAddress &entrypoint, ConcreteMemory *memory,
		 Decoder *decoder)
  throw (Decoder::Exception &)
{
  return s_generic_call (entrypoint, memory, decoder, 
			 &AlgorithmFactory::buildFloodTraversal);
}

Microcode * 
recursive_traversal (const ConcreteAddress &entrypoint, ConcreteMemory *memory,
		     Decoder *decoder)
  throw (Decoder::Exception &)
{
  return s_generic_call (entrypoint, memory, decoder, 
			 &AlgorithmFactory::buildRecursiveTraversal);
}

Microcode * 
symbolic_simulator (const ConcreteAddress &entrypoint, ConcreteMemory *memory,
		    Decoder *decoder)
  throw (Decoder::Exception &)
{
  return s_generic_call (entrypoint, memory, decoder, 
			 &AlgorithmFactory::buildSymbolicSimulator);
}

Microcode * 
concrete_simulator (const ConcreteAddress &entrypoint, ConcreteMemory *memory,
		    Decoder *decoder)
  throw (Decoder::Exception &)
{
  return s_generic_call (entrypoint, memory, decoder, 
			 &AlgorithmFactory::buildConcreteSimulator);
}

#include <analyses/cfgrecovery/recovery_algorithms.hh>
#include "cfgrecovery.hh"
#include "algorithms.hh"

static const std::string SIMULATOR_X86_32_INIT_ESP_PROP =
  "disas.simulator.x86_32.init-esp";
static const std::string SIMULATOR_X86_32_INIT_EBP_PROP =
  "disas.simulator.x86_32.init-ebp";
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


Microcode * 
linear_sweep(const ConcreteAddress * entrypoint, ConcreteMemory * memory,
	    Decoder * decoder)
  throw (Decoder::Exception &)
{
  Microcode *result = new Microcode ();
  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATES, false);
  bool show_pending_arrows = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_PENDING_ARROWS, 
				     false);
  try
    {
      cfgrecovery_linear_sweep (entrypoint, memory, decoder, result, 
				show_states, show_pending_arrows);
    }
  catch (Decoder::Exception &)
    {
      delete result;
      throw;
    }
  return result;
}

Microcode *
flood_traversal (const ConcreteAddress *entrypoint, ConcreteMemory *memory,
		 Decoder *decoder)
  throw (Decoder::Exception &)
{
  Microcode *result = new Microcode ();
  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATES, false);
  bool show_pending_arrows = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_PENDING_ARROWS, 
				     false);
  try
    {
      cfgrecovery_flood_traversal (entrypoint, memory, decoder, result, 
				   show_states, show_pending_arrows);
    }
  catch (Decoder::Exception &)
    {
      delete result;
      throw;
    }
  return result;
}

Microcode * 
recursive_traversal (const ConcreteAddress * entrypoint, 
		     ConcreteMemory * memory,
		     Decoder * decoder)
  throw (Decoder::Exception &)
{
  Microcode *result = new Microcode ();
  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATES, false);
  bool show_pending_arrows = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_PENDING_ARROWS, 
				     false);
  int max_nb_visits =
    CFGRECOVERY_CONFIG->get_integer (SIMULATOR_NB_VISITS_PER_ADDRESS, 0);

  if (max_nb_visits > 0 && verbosity)
    {
      logs::warning << "warning: restrict number of visits per program point "
		    << "to " << std::dec << max_nb_visits << " visits." 
		    << std::endl;
    }

  try
    {
      cfgrecovery_recursive_traversal (entrypoint, memory, decoder, result, 
				       show_states, show_pending_arrows,
				       max_nb_visits);
    }
  catch (Decoder::Exception &)
    {
      delete result;
      throw;
    }
  return result;
}

static Microcode * 
s_simulator (const ConcreteAddress * entrypoint, ConcreteMemory * memory,
	     Decoder * decoder, bool symbolic)
  throw (Decoder::Exception &)
{
  Microcode *result = new Microcode ();
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

  try
    {
      if (symbolic)
	{
	  int djmpth = 
	    CFGRECOVERY_CONFIG->get_integer (SYMSIM_DYNAMIC_JUMP_THRESHOLD);
	  bool djmp2mem = 
	    CFGRECOVERY_CONFIG->get_boolean (SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY);
	  cfgrecovery_symbolic_simulator (entrypoint, memory, decoder, result, 
					  show_states, show_pending_arrows,
					  warn_unsolved_jumps,
					  max_nb_visits,
					  djmpth, djmp2mem);
	}
      else
	{
	  cfgrecovery_concrete_simulator (entrypoint, memory, decoder, result, 
					  show_states, show_pending_arrows,
					  warn_unsolved_jumps, 
					  max_nb_visits);
	}
    }
  catch (Decoder::Exception &)
    {
      delete result;
      throw;
    }
  return result;
}

Microcode * 
symbolic_simulator (const ConcreteAddress * entrypoint, ConcreteMemory * memory,
		    Decoder * decoder)
  throw (Decoder::Exception &)
{
  return s_simulator (entrypoint, memory, decoder, true);
}

Microcode * 
concrete_simulator (const ConcreteAddress * entrypoint, ConcreteMemory * memory,
		    Decoder * decoder)
  throw (Decoder::Exception &)
{
  return s_simulator (entrypoint, memory, decoder, false);
}

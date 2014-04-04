/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS AND CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include "algorithms.hh"
#include "cfgrecovery.hh"

#include <signal.h>

#include <analyses/cfgrecovery/AlgorithmFactory.hh>

using namespace std;

static const string SIMULATOR_INIT_SP_PROP =
  "disas.simulator.init-sp";
static const string SIMULATOR_ZERO_REGISTERS =
  "disas.simulator.zero-registers";
static const string SIMULATOR_NB_VISITS_PER_ADDRESS =
  "disas.simulator.nb-visits-per-address";
static const string SIMULATOR_WARN_UNSOLVED_DYNAMIC_JUMPS =
  "disas.simulator.warn-unsolved-dynamic-jumps";
static const string SIMULATOR_WARN_SKIPPED_DYNAMIC_JUMPS =
  "disas.simulator.warn-skipped-dynamic-jumps";
static const string SIMULATOR_DEBUG_SHOW_STATES =
  "disas.simulator.debug.show-states";
static const string SIMULATOR_DEBUG_SHOW_STATE_SPACE_SIZE =
  "disas.simulator.debug.show-state-space-size";
static const string SIMULATOR_DEBUG_SHOW_PENDING_ARROWS =
  "disas.simulator.debug.show-pending-arrows";

static const string SYMSIM_DYNAMIC_JUMP_THRESHOLD =
  "disas.symsim.dynamic-jump-threshold";
static const string SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY =
  "disas.symsim.map-dynamic-jump-to-memory";

typedef AlgorithmFactory::Algorithm * (AlgorithmFactory::* FactoryMethod) ();

static AlgorithmFactory::Algorithm *running_algorithm = NULL;

static void 
s_sigint_handler (int)
{
  if (running_algorithm)
    running_algorithm->stop ();
}

static void
s_generic_call (const list<ConcreteAddress >&entrypoint,
		ConcreteMemory *memory,
		Decoder *decoder, FactoryMethod build, Microcode *result)
{
  AlgorithmFactory F;

  if (CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_ZERO_REGISTERS, false))
    {
      const Architecture *arch = decoder->get_arch ()->get_reference_arch ();

      for (RegisterSpecs::const_iterator i = arch->get_registers ()->begin ();
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

  if (CFGRECOVERY_CONFIG->has (SIMULATOR_INIT_SP_PROP))
    {
      Constant *c = NULL;
      long valsp = CFGRECOVERY_CONFIG->get_integer (SIMULATOR_INIT_SP_PROP);

      if (verbosity)
	logs::warning << "warning: setting stack-pointer to "
		      << hex << "0x" << valsp << endl;

      switch (decoder->get_arch ()->get_proc ())
	{
	case Architecture::X86_32:
	  c = Constant::create (valsp, 0, 32);
	  memory->put (decoder->get_arch ()->get_register ("esp"),  c);
	  break;

	case Architecture::X86_64:
	  c = Constant::create (valsp, 0, 64);
	  memory->put (decoder->get_arch ()->get_register ("rsp"),  c);
	  break;

	default:
	  /* Do nothing */
	  logs::warning << "warning: 'disas.simulator.init-sp'"
			<< " is not supported for this architecture"
			<< endl;
	}
      if (c != NULL)
	c->deref ();
    }

  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATES, false);
  bool show_state_space_size = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATE_SPACE_SIZE, 
				     false);
  bool show_pending_arrows = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_PENDING_ARROWS, 
				     false);
  bool warn_unsolved_jumps =
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_WARN_UNSOLVED_DYNAMIC_JUMPS, 
				     true);
  bool warn_skipped_jumps =
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_WARN_UNSOLVED_DYNAMIC_JUMPS, 
				     true);
  int max_nb_visits =
    CFGRECOVERY_CONFIG->get_integer (SIMULATOR_NB_VISITS_PER_ADDRESS, 0);

  if (max_nb_visits > 0 && verbosity)
    {
      logs::warning << "warning: restrict number of visits per program point "
		    << "to " << dec << max_nb_visits << " visits."
		    << endl;
    }
  int djmpth = 
    CFGRECOVERY_CONFIG->get_integer (SYMSIM_DYNAMIC_JUMP_THRESHOLD);
  bool djmp2mem = 
    CFGRECOVERY_CONFIG->get_boolean (SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY);

  F.set_memory (memory);
  F.set_decoder (decoder); 
  F.set_show_states (show_states);
  F.set_show_state_space_size (show_state_space_size);
  F.set_show_pending_arrows (show_pending_arrows);
  F.set_warn_on_unsolved_dynamic_jumps (warn_unsolved_jumps);
  F.set_warn_skipped_dynamic_jumps (warn_skipped_jumps);
  F.set_map_dynamic_jumps_to_memory (djmp2mem);
  F.set_dynamic_jumps_threshold (djmpth);
  F.set_max_number_of_visits_per_address (max_nb_visits);
 
  running_algorithm = (F.* build) ();
  if (signal (SIGINT, &s_sigint_handler) == SIG_ERR)
    logs::error << "unable to set CTRL-C handler." << endl;

  try
    {
      logs::warning << "Starting the analysis, hit Ctrl-C to interrupt..."
		    << endl;

      running_algorithm->compute (entrypoint, result);
      delete running_algorithm;
      running_algorithm = NULL;
    }
  catch (Decoder::Exception &)
    {
      delete running_algorithm;
      running_algorithm = NULL;
      delete result;
      throw;
    }
}

void
linear_sweep(const list<ConcreteAddress> &entrypoints,
	     ConcreteMemory * memory, Decoder * decoder, Microcode *result)
  throw (Decoder::Exception &, AlgorithmFactory::Exception &)
{ 
  s_generic_call (entrypoints, memory, decoder, 
		  &AlgorithmFactory::buildLinearSweep, result);
}

void 
flood_traversal (const list<ConcreteAddress> &entrypoints,
		 ConcreteMemory *memory, Decoder *decoder, Microcode *result)
  throw (Decoder::Exception &, AlgorithmFactory::Exception &)
{
  s_generic_call (entrypoints, memory, decoder, 
		  &AlgorithmFactory::buildFloodTraversal, result);
}

void 
recursive_traversal (const list<ConcreteAddress> &entrypoints,
		     ConcreteMemory *memory, Decoder *decoder, Microcode *result)
  throw (Decoder::Exception &, AlgorithmFactory::Exception &)
{
  s_generic_call (entrypoints, memory, decoder,
		  &AlgorithmFactory::buildRecursiveTraversal, result);
}

void 
symbolic_simulator (const list<ConcreteAddress> &entrypoints,
		    ConcreteMemory *memory, Decoder *decoder, Microcode *result)
  throw (Decoder::Exception &, AlgorithmFactory::Exception &)
{
  s_generic_call (entrypoints, memory, decoder,
		  &AlgorithmFactory::buildSymbolicSimulator, result);
}

void 
concrete_simulator (const list<ConcreteAddress> &entrypoints,
		    ConcreteMemory *memory, Decoder *decoder, Microcode *result)
  throw (Decoder::Exception &, AlgorithmFactory::Exception &)
{
  s_generic_call (entrypoints, memory, decoder,
		  &AlgorithmFactory::buildConcreteSimulator, result);
}

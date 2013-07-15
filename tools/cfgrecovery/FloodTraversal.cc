/*-
 * Copyright (C) 2012, Centre National de la Recherche Scientifique,
 *                     Institut Polytechnique de Bordeaux,
 *                     Universite Bordeaux 1.
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
#include <analyses/cfgrecovery/FloodTraversal.hh>
#include "simulator.hh"

/* Flood traversal disassembly method */
Microcode *
flood_traversal (const ConcreteAddress *entrypoint, ConcreteMemory *memory,
		 Decoder *decoder)
  throw (Decoder::Exception &)
{
  Microcode *result = new Microcode ();
  FloodTraversal::Stepper *stepper = 
    new FloodTraversal::Stepper (memory, 
				 decoder->get_arch ()->get_reference_arch());
  FloodTraversal::StateSpace *states = new FloodTraversal::StateSpace ();
  FloodTraversal::Traversal rec (memory, decoder, stepper, states, result);

  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_STATES, false);
  bool show_pending_arrows = 
    CFGRECOVERY_CONFIG->get_boolean (SIMULATOR_DEBUG_SHOW_PENDING_ARROWS, 
				     false);
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
  rec.compute (*entrypoint);

  delete stepper;
  delete states;

  return result;
}

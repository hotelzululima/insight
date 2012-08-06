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

#include <stdlib.h>

#include <kernel/annotations/CallRetAnnotation.hh>

#include "recursivetraversal.hh"

using namespace std;

static void
inner_recursivetraversal (const ConcreteAddress * entrypoint,
			  Microcode * mc,
			  ConcreteMemory * memory,
			  Decoder * decoder)
{
  ConcreteAddress next, current = *entrypoint;

  while (memory->is_defined(current))
    {
      try
	{
	  /* Decode current instruction and get next address */
	  next = decoder->decode(mc, current);

	  /* Get current MicrocodeNode */
	  MicrocodeNode * mc_node =
	    mc->get_node(MicrocodeAddress(current.get_address()));

	  if (mc_node->is_annotated())
	    {
	      CallRetAnnotation * callret =
		(CallRetAnnotation *) mc_node->get_annotation("callret");

	      if (callret != NULL)
		{
		  if (callret->is_call())
		    {
		      MicrocodeNode * current_mloc = mc_node;
		      StmtArrow * next_edge =
			mc->get_first_successor(current_mloc).first;
		      MicrocodeNode * next_mloc =
			mc->get_first_successor(current_mloc).second;

		      while ((next_edge != NULL) && (next_mloc != NULL))
			{
			  if (mc_node->get_loc().getGlobal() !=
			      next_mloc->get_loc().getGlobal())
			    {
			      const ConcreteAddress addr =
				ConcreteAddress(next_mloc->get_loc().getGlobal());
			      inner_recursivetraversal(&addr,
						       mc,
						       memory,
						       decoder);
			      break;
			    }
		      
			  current_mloc = next_mloc;
			  
			  next_edge =
			    mc->get_first_successor(current_mloc).first;
			  next_mloc =
			    mc->get_first_successor(current_mloc).second;
			}		      
		    }
		  else
		    return; /* ret has been reached, poping the stack */
		}
	    }

	  current = next;
	}
      catch (exception& e)
	{
	  if (verbosity > 1)
	    *output << mc->pp() << endl;

	  cerr << prog_name << ": error" << e.what() << endl;
	  exit(EXIT_FAILURE);
	}
    }
}


/* Recursive traversal disassembly method */
Microcode *
recursivetraversal (const ConcreteAddress * entrypoint,
		    ConcreteMemory * memory,
		    Decoder * decoder)
{
  Microcode * mc = new Microcode();

  inner_recursivetraversal(entrypoint, mc, memory, decoder);

  return mc;
}

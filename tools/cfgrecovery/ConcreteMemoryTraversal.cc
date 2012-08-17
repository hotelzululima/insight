/*
 * Copyright (c) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#include <decoders/binutils/BinutilsDecoder.hh>
#include "cfgrecovery.hh"
#include "ConcreteMemoryTraversal.hh"

using namespace std;

struct ArrowCreate : public Microcode::ArrowCreationCallback
{
  list<StmtArrow *> arrows;

  void add_node (Microcode *, StmtArrow *a) {
    arrows.push_back (a);
  }
};

ConcreteMemoryTraversal::ConcreteMemoryTraversal (const ConcreteMemory *memory, 
						  Decoder *decoder)
  : mem (memory), decoder (decoder), visited (), in_todo (), todo ()
{
}

ConcreteMemoryTraversal::~ConcreteMemoryTraversal ()
{
}

bool 
ConcreteMemoryTraversal::can_visit (const ConcreteAddress &loc) const
{ 
  address_t addr = loc.get_address ();

  return (!already_visited (loc) && in_todo.find (addr) == in_todo.end ());
}

bool 
ConcreteMemoryTraversal::already_visited (const ConcreteAddress &loc) const
{
  return visited.find (loc.get_address ()) != visited.end ();
}

void 
ConcreteMemoryTraversal::add_to_todo_list (const ConcreteAddress &loc)
{
  address_t addr = loc.get_address ();
  todo.push_back (addr);
  in_todo.insert (addr);
}

ConcreteAddress 
ConcreteMemoryTraversal::take_from_to_todo_list ()
{
  ConcreteAddress result = todo.front ();
  todo.pop_front ();
  in_todo.erase (result.get_address ());

  return result;
}

void 
ConcreteMemoryTraversal::compute (Microcode *mc,
				  const ConcreteAddress &entrypoint)
{
  ArrowCreate cb;

  if (! can_visit (entrypoint))
    return;

  mc->add_arrow_creation_callback (&cb);
  add_to_todo_list (entrypoint);

  while (! todo.empty ())
    {
      ConcreteAddress addr = take_from_to_todo_list ();

      if (! mem->is_defined (addr) || ! can_visit (addr))
	continue;

      visited.insert (addr.get_address ());
      if (verbosity > 1)
	{
	  string inst = 
	    ((BinutilsDecoder *) decoder)->get_instruction (addr);
	  cerr << addr << " : " << inst << endl;
	}
      ConcreteAddress next = decoder->decode (mc, addr);
      MicrocodeAddress ma (addr.get_address ());
      MicrocodeNode *node = mc->get_node (ma);
      while (! cb.arrows.empty ())
	{
	  StmtArrow *a = cb.arrows.front ();
	  treat_new_arrow (mc, node, a, next);
	  cb.arrows.pop_front ();
        }      
    }

  mc->remove_arrow_creation_callback (&cb);
}

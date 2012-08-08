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

#include "linearsweep.hh"
#include "recursivetraversal.hh"

using namespace std;

class RecursiveTraversal : public LinearSweepTraversal
{
  list<ConcreteAddress> stack;

public :
  RecursiveTraversal (const ConcreteMemory *memory, Decoder *decoder) 
    : LinearSweepTraversal (false, memory, decoder), stack ()
  {
  }
      
  ~RecursiveTraversal ()
  {
  }

protected:
  void treat_new_arrow (const ConcreteAddress &loc, const StmtArrow *arrow, 
			const ConcreteAddress &next)
  {    
    this->LinearSweepTraversal::treat_new_arrow (loc, arrow, next);

    MicrocodeNode *src = arrow->get_src ();
    if (! src->has_annotation (CallRetAnnotation::ID))
      return;
    CallRetAnnotation *an = (CallRetAnnotation *) 
      src->get_annotation (CallRetAnnotation::ID);
    if (an->is_call ())
      stack.push_front (next);
    else
      {
	ConcreteAddress ret = stack.front ();
	stack.pop_front ();
	if (can_visit (ret))
	  add_to_todo_list (ret);
      }
  }
};

/* Recursive traversal disassembly method */
Microcode *
recursivetraversal (const ConcreteAddress * entrypoint,
		    ConcreteMemory * memory,
		    Decoder * decoder)
{
  Microcode * mc = new Microcode();
  RecursiveTraversal rt (memory, decoder);

  rt.compute (mc, *entrypoint);

  return mc;
}

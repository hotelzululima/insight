/*-
 * Copyright (C) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
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

#include <interpreters/common/ConcreteProgramPoint.hh>
#include <interpreters/concrete/ConcreteMemory.hh>
#include <interpreters/concrete/concrete_context.hh>

#include <sstream>

/*****************************************************************************/

bool
ConcreteContext::
merge(AbstractContext<CONCRETE_CLASSES> * other)
{

  delete memory;
  memory = new ConcreteMemory(*(other->memory));
  return true; /* always update the following states */
}

/*****************************************************************************/

AbstractContext<CONCRETE_CLASSES> *
ConcreteContext::empty_context()
{
  return new ConcreteContext(new ConcreteMemory());
}

/*****************************************************************************/

AbstractContext<CONCRETE_CLASSES> *
ConcreteContext::clone()
{
  ConcreteMemory *mem_cpy = new ConcreteMemory(*memory);
  return new ConcreteContext(mem_cpy);
}

/*****************************************************************************/

void 
ConcreteExecContext::request_update (ConcreteProgramPoint &pp)
{
  if (memory->is_undefined (ConcreteAddress (pp.to_address().getGlobal())))
    return;

  if (decoder == NULL)
    AbstractExecContext<CONCRETE_CLASSES>::request_update (pp);
  else
    {
      Microcode *mc = dynamic_cast<Microcode *> (program);

      try 
	  {
	    MicrocodeNode *node = get_node (pp);

	    if (mc->get_nb_successors (node) == 0)
	      {
		MicrocodeAddress addr = node->get_loc ();
		assert (addr.getLocal () == 0);
		decoder->decode (mc, ConcreteAddress (addr.getGlobal ()));
	      }
	  }
      catch (GetNodeNotFoundExc)
	{
	  assert (pp.getLocal () == 0);
	  decoder->decode (mc, ConcreteAddress (pp.getGlobal ()));
	  AbstractExecContext<CONCRETE_CLASSES>::request_update (pp);
	}
      AbstractExecContext<CONCRETE_CLASSES>::request_update (pp);
    }
}

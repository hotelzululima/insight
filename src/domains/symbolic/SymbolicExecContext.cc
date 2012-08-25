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
#include <kernel/annotations/AsmAnnotation.hh>
#include <domains/symbolic/SymbolicExecContext.hh>

SymbolicExecContext::SymbolicExecContext(const ConcreteMemory *mem, 
					 Decoder *dec)
  : base (mem), decoder (dec)
{
  program = new Microcode ();
}

SymbolicExecContext::~SymbolicExecContext () 
{
  delete program;
}

StepResult 
SymbolicExecContext::step(Arrow pa) 
{
  return SymbolicAbstractExecContext::step (pa);
}

bool 
SymbolicExecContext::step()
{
  // Execute a step
  bool result =
    ((AbstractExecContext<SYMBOLIC_CLASSES>*)this)->generic_step();
  if (!result)
    return false;
  
  // This is specific to the simulator: delete all the context which
  // have no pending arrow.
  std::map<ConcreteProgramPoint,
	   AbstractContext<SYMBOLIC_CLASSES>*>::iterator the_pair;
  for (the_pair = exec_map.begin(); the_pair != exec_map.end(); the_pair++)
    {
      bool found = false;
      std::list< PendingArrow<SYMBOLIC_CLASSES> >::iterator arr;
      for (arr = pending_arrows.begin(); arr != pending_arrows.end(); arr++)
	if (arr->pp.equals(the_pair->first))
	  {
	    found = true;
              break;
	  }
      if (!found)
	{
	  delete the_pair->second;
	  exec_map.erase(the_pair);
	  the_pair = exec_map.begin();
	  if (the_pair == exec_map.end())
	    break;
	}
    }
  
  return true;
  
  // \todo : Remove map entries for which there is no pending arrow.
}
#if 0
void 
SymbolicExecContext::request_update (ConcreteProgramPoint &pp)
{
  if (!memory->is_defined (ConcreteAddress (pp.to_address().getGlobal())))
    return;

  if (decoder == NULL)
    AbstractExecContext<SYMBOLIC_CLASSES>::request_update (pp);
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
	}
      SymbolicAbstractExecContext::request_update (pp);
    }
}
#endif

MicrocodeNode * 
SymbolicExecContext::get_node (const ConcreteProgramPoint &pp)
{
  bool is_global = (pp.getLocal () == 0);
  MicrocodeNode *result = NULL;
  Microcode *mc = dynamic_cast<Microcode *> (program);
  assert (mc != NULL);

  try
    {
      result = program->get_node (pp.to_address ());
      if (is_global && ! result->has_annotation (AsmAnnotation::ID))
	{
	  // result is a node added by the decoder but asm instruction at
	  // pp.to_address () has not yet been decoded.
	  MicrocodeAddress addr = result->get_loc ();
	  assert (addr.getLocal () == 0);
	  decoder->decode (mc, ConcreteAddress (addr.getGlobal ()));
	}	
    }
  catch (GetNodeNotFoundExc &)
    {
      if (! is_global)
	throw;
      decoder->decode (mc, ConcreteAddress (pp.getGlobal ()));
      result = program->get_node (pp.to_address ());
    }

  return result;
}

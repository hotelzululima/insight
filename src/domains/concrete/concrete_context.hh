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
#ifndef DOMAINS_CONCRETE_CONCRETE_CONTEXT_HH_
#define DOMAINS_CONCRETE_CONCRETE_CONTEXT_HH_

#include <map>

#include <analyses/microcode_exec.hh>
#include <decoders/Decoder.hh>
#include <domains/common/ConcreteProgramPoint.hh>
#include <domains/concrete/ConcreteValue.hh>
#include <domains/concrete/ConcreteMemory.hh>
#include <domains/concrete/ConcreteExprSemantics.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/Microcode.hh>

class ConcreteContext;
class ConcreteProgramPoint;
class ConcreteExecContext;


#define CONCRETE_CLASSES \
  ConcreteAddress,       \
  ConcreteValue,         \
  ConcreteExprSemantics, \
  ConcreteMemory,        \
  ConcreteProgramPoint

class ConcreteContext : public AbstractContext<CONCRETE_CLASSES>
{

public:

  ConcreteContext(ConcreteMemory *mem)
  {
    memory = mem ;
  }
  ~ConcreteContext()
  {
    delete memory;
  }

  bool merge(AbstractContext<CONCRETE_CLASSES> * other);
  AbstractContext<CONCRETE_CLASSES> * clone();
  static AbstractContext<CONCRETE_CLASSES> * empty_context();

};

class ConcreteExecContext :
  public AbstractExecContext<CONCRETE_CLASSES>
{
  ConcreteMemory *memory;
  Decoder *decoder;

public:

  ConcreteExecContext(ConcreteMemory *mem, Decoder *dec, 
		      MicrocodeStore *prg) : memory (mem), decoder (dec)
					     
  {
    program = prg;
  }

  ConcreteExecContext(MicrocodeStore *prg) : memory (0), decoder (0)
					     
  {
    program = prg;
  }

  virtual ~ConcreteExecContext() {
  }

  virtual StepResult step(Arrow pa) {
    return this->AbstractExecContext<CONCRETE_CLASSES>::step (pa);
  }

  bool step()
  {

    // Execute a step
    bool result =
      ((AbstractExecContext<CONCRETE_CLASSES>*)this)->generic_step();
    if (!result)
      return false;

    // This is specific to the simulator: delete all the context which
    // have no pending arrow.
    std::map<ConcreteProgramPoint,
	     AbstractContext<CONCRETE_CLASSES>*>::iterator the_pair;
    for (the_pair = exec_map.begin(); the_pair != exec_map.end(); the_pair++)
      {
        bool found = false;
        std::list< PendingArrow<CONCRETE_CLASSES> >::iterator arr;
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

  };

  void request_update (ConcreteProgramPoint &pp);
};

#endif /* DOMAINS_CONCRETE_CONCRETE_CONTEXT_HH_ */

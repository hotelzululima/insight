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
#ifndef DOMAINS_SYMBOLIC_SYMBOLIC_EXEC_CONTEXT_HH_
#define DOMAINS_SYMBOLIC_SYMBOLIC_EXEC_CONTEXT_HH_

#include <map>

#include <analyses/microcode_exec.hh>
#include <decoders/Decoder.hh>
#include <domains/common/SymbolicProgramPoint.hh>
#include <domains/symbolic/SymbolicValue.hh>
#include <domains/symbolic/SymbolicMemory.hh>
#include <domains/symbolic/SymbolicExprSemantics.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/Microcode.hh>
#include <domains/symbolic/SymbolicContext.hh>

typedef AbstractExecContext<SYMBOLIC_CLASSES> SymbolicAbstractExecContext;

class SymbolicExecContext : public SymbolicAbstractExecContext
{
  SymbolicMemory *memory;
  Decoder *decoder;

public:

  SymbolicExecContext(SymbolicMemory *mem, Decoder *dec, 
		      MicrocodeStore *prg) : memory (mem), decoder (dec)
					     
  {
    program = prg;
  }

  SymbolicExecContext(MicrocodeStore *prg) : memory (0), decoder (0)
					     
  {
    program = prg;
  }

  virtual ~SymbolicExecContext() {
  }

  virtual StepResult step(Arrow pa) {
    return this->AbstractExecContext<SYMBOLIC_CLASSES>::step (pa);
  }

  bool step()
  {

    // Execute a step
    bool result =
      ((AbstractExecContext<SYMBOLIC_CLASSES>*)this)->generic_step();
    if (!result)
      return false;

    // This is specific to the simulator: delete all the context which
    // have no pending arrow.
    std::map<SymbolicProgramPoint,
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
            exec_map.erase(the_pair);
            the_pair = exec_map.begin();
	    if (the_pair == exec_map.end())
	      break;
          }
      }

    return true;

    // \todo : Remove map entries for which there is no pending arrow.

  };

  void request_update (SymbolicProgramPoint &pp);
};

#endif /* DOMAINS_SYMBOLIC_SYMBOLIC_EXEC_CONTEXT_HH_ */

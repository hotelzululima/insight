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

#include "SymbolicState.hh"

SymbolicState::SymbolicState (const MicrocodeAddress &ma, 
			      SymbolicMemory *mem, Expr *cond) 
  : address (ma), memory (mem), condition (cond) 
{
}

SymbolicState::~SymbolicState ()
{
  delete memory;
  condition->deref ();
}

SymbolicState *
SymbolicState::clone () const 
{
  return new SymbolicState (address, memory->clone (), condition->ref ());
}

SymbolicMemory * 
SymbolicState::get_memory () const
{
  return memory;
}

const Expr *
SymbolicState::get_condition () const
{
  return condition;
}

void 
SymbolicState::set_condition (Expr *cond)
{
  condition->deref ();
  condition = cond;
}

MicrocodeAddress 
SymbolicState::get_address () const
{
  return address;
}

void 
SymbolicState::set_address (const MicrocodeAddress &ma) 
{
  address = ma;
}

void 
SymbolicState::output_text (std::ostream &out) const
{
  out << "@ " << address << " " << std::endl
      << "State of Memory: " << std::endl;
  memory->output_text (out);
  out << std::endl
      << "Reachability condition: " << std::endl
      << *condition << std::endl;
}

bool 
SymbolicState::equals (const SymbolicState &s) const
{  
  return (address.equals (s.address) && condition == s.condition &&
	  memory->equals (*(s.memory)));
}

std::size_t 
SymbolicState::hashcode () const
{
  std::size_t result = (19 * address.getGlobal () + 
			17 * address.getLocal () +
			133 * memory->hashcode () +
			1977 * (uintptr_t) condition);

  return result;
}

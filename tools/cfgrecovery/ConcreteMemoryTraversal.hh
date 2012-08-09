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
#ifndef CONCRETEMEMORYTRAVERSAL_HH
# define CONCRETEMEMORYTRAVERSAL_HH

# include <list>
# include <set>

# include <domains/concrete/ConcreteMemory.hh>
# include <kernel/Microcode.hh>
# include <decoders/Decoder.hh>

class ConcreteMemoryTraversal
{
public:
  ConcreteMemoryTraversal (const ConcreteMemory *memory, Decoder *decoder);
  virtual ~ConcreteMemoryTraversal ();

  virtual void compute (Microcode *mc, const ConcreteAddress &entrypoint);

  virtual bool can_visit (const ConcreteAddress &loc) const;
  virtual bool already_visited (const ConcreteAddress &loc) const;

protected:
  virtual void treat_new_arrow (Microcode *mc, 
				const MicrocodeNode *entry,
				const StmtArrow *a,
				const ConcreteAddress &next) = 0;

  void add_to_todo_list (const ConcreteAddress &loc);
  ConcreteAddress take_from_to_todo_list ();

  const ConcreteMemory *mem;
  Decoder *decoder;
  std::set<address_t> visited;
  std::set<address_t> in_todo;
  std::list<ConcreteAddress> todo;
};

#endif /* ! CONCRETEMEMORYTRAVERSAL_HH */

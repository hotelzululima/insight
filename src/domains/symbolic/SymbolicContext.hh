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
#ifndef DOMAINS_SYMBOLIC_SYMBOLIC_CONTEXT_HH_
#define DOMAINS_SYMBOLIC_SYMBOLIC_CONTEXT_HH_

#include <map>

#include <analyses/microcode_exec.hh>
#include <domains/common/ConcreteProgramPoint.hh>
#include <domains/symbolic/SymbolicValue.hh>
#include <domains/symbolic/SymbolicMemory.hh>
#include <domains/symbolic/SymbolicExprSemantics.hh>

class SymbolicContext;
class SymbolicProgramPoint;
class SymbolicExecContext;


#define SYMBOLIC_CLASSES \
  ConcreteAddress,       \
  SymbolicValue,         \
  SymbolicExprSemantics, \
  SymbolicMemory,        \
  ConcreteProgramPoint

typedef AbstractContext<SYMBOLIC_CLASSES> SymbolicAbstractContext;

class SymbolicContext : public SymbolicAbstractContext
{
  SymbolicContext (SymbolicMemory *mem);

public:

  virtual ~SymbolicContext ();

  virtual bool merge (SymbolicAbstractContext * other);
  virtual SymbolicAbstractContext *clone ();

  static SymbolicContext *empty_context (const ConcreteMemory *base);
};

#endif /* DOMAINS_SYMBOLIC_SYMBOLIC_CONTEXT_HH_ */

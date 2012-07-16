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
#ifndef INTERPRETERS_INTERVAL_CONTEXT_HH_
#define INTERPRETERS_INTERVAL_CONTEXT_HH_

#include <interpreters/common/ConcreteProgramPoint.hh>
#include <interpreters/interval/IntervalAddress.hh>
#include <interpreters/interval/IntervalExprSemantics.hh>
#include <interpreters/interval/IntervalMemory.hh>
#include <interpreters/interval/IntervalValue.hh>
#include <kernel/Architecture.hh>

class IntervalFactory;

#define INTERVAL_CLASSES	\
  IntervalAddress,		\
  IntervalValue,		\
  IntervalExprSemantics,	\
  IntervalMemory,		\
  ConcreteProgramPoint

class IntervalContext : public AbstractContext<INTERVAL_CLASSES>
{
public:
  IntervalContext(IntervalMemory *mem);
  virtual ~IntervalContext();
  virtual IntervalContext *clone();
  virtual bool merge(AbstractContext<INTERVAL_CLASSES> *other);
  static IntervalContext *empty_context();
};

class IntervalExecContext : public AbstractExecContext<INTERVAL_CLASSES>
{

public:
  IntervalExecContext(MicrocodeStore *prg)
  {
    program = prg;
  }
  virtual ~IntervalExecContext() { }

};

#endif /* INTERPRETERS_INTERVAL_CONTEXT_HH_ */

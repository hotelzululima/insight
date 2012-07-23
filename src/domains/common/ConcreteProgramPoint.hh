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
#ifndef INTERPRETERS_COMMON_CONCRETE_PROGRAM_POINT_HH
#define INTERPRETERS_COMMON_CONCRETE_PROGRAM_POINT_HH

#include <string>

#include <kernel/Microcode.hh>

#include <analyses/microcode_exec.hh>
#include <interpreters/concrete/ConcreteMemory.hh>
#include <interpreters/concrete/ConcreteValue.hh>

class ConcreteProgramPoint : public AbstractProgramPoint<ConcreteProgramPoint>,
  public MicrocodeAddress
{
public:
  ConcreteProgramPoint(MicrocodeAddress a);
  ConcreteProgramPoint(const ConcreteProgramPoint &other);

  MicrocodeAddress to_address();
  ConcreteProgramPoint next(MicrocodeAddress addr);

  bool equals(const ConcreteProgramPoint &other) const;
  bool lessThan(const ConcreteProgramPoint &other) const;

  static ConcreteProgramPoint *init_program_point(MicrocodeAddress addr);
  std::string pp() const;

private:
  bool operator==(const ConcreteProgramPoint &other) const;
  bool operator<(const ConcreteProgramPoint &other) const;
};

#endif /* INTERPRETERS_COMMON_CONCRETE_PROGRAM_POINT_HH */

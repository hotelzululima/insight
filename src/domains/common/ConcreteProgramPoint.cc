/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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

#include <domains/common/ConcreteProgramPoint.hh>

#include <sstream>

using namespace std;

ConcreteProgramPoint::ConcreteProgramPoint(MicrocodeAddress addr) :
  MicrocodeAddress(addr)
{
}

ConcreteProgramPoint::ConcreteProgramPoint(const ConcreteProgramPoint &other) :
  AbstractProgramPoint<ConcreteProgramPoint>::AbstractProgramPoint(),
  MicrocodeAddress(other)
{
}

MicrocodeAddress ConcreteProgramPoint::to_address() const
{
  return *this;
}

ConcreteProgramPoint ConcreteProgramPoint::next(MicrocodeAddress addr)
{
  return ConcreteProgramPoint(addr);
}

bool
ConcreteProgramPoint::equals(const ConcreteProgramPoint &other) const
{
  return MicrocodeAddress::equals(other);
}


bool ConcreteProgramPoint::lessThan(const ConcreteProgramPoint &other) const
{
  if (getGlobal() < other.getGlobal()) return true;
  if ((getGlobal() == other.getGlobal()) &&
      (getLocal() < other.getLocal())) return true;
  return false;
}

ConcreteProgramPoint *ConcreteProgramPoint::
init_program_point(MicrocodeAddress addr)
{
  return new ConcreteProgramPoint(addr);
}

string
ConcreteProgramPoint::pp() const
{
  ostringstream oss;
  char tmp[20];
  sprintf(tmp, "0x%X", getGlobal());
  oss << "(" << tmp << "," << getLocal() << ")";
  return oss.str();
}

#include <cstdlib>

bool
ConcreteProgramPoint::operator==(const ConcreteProgramPoint &) const
{
  abort();
}

bool
ConcreteProgramPoint::operator<(const ConcreteProgramPoint &) const
{
  abort();
}

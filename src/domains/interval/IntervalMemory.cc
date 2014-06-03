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

#include <domains/interval/IntervalMemory.hh>

#include <sstream>
#include <string>

using namespace std;

IntervalMemory::IntervalMemory() :
  Memory<IntervalAddress, IntervalValue>(),
  RegisterMap<IntervalValue>(), mem()
{
}

IntervalValue
IntervalMemory::get(const IntervalAddress &ia, int size,
		    Architecture::endianness_t e) const
                   throw (UndefinedValueException)
{

  /*! \todo iterate over addresses. Q: which addresses?? */
  return mem.get(ConcreteAddress(ia.get().getMin()), size, e);
}

void
IntervalMemory::put(const IntervalAddress &ia, const IntervalValue &v,
		    Architecture::endianness_t e)
{

  /*! \todo iterate over addresses. Q: which addresses?? */
  return mem.put(ConcreteAddress(ia.get().getMin()), v, e);
}

bool
IntervalMemory::is_defined(const IntervalAddress &ia) const
{

  /*! \todo iterate over addresses. Q: which addresses?? */
  return mem.is_defined(ConcreteAddress(ia.get().getMin()));
}

bool
IntervalMemory::merge(const IntervalMemory &other)
{
  /*! \todo join elements one by one */
  mem = other.mem;
  return true;
}

string
IntervalMemory::pp()
{
  /*! \todo implement */
  return "";
}

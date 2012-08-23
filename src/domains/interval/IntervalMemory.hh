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
#ifndef DOMAINS_INTERVAL_INTERVAL_MEMORY_HH
#define DOMAINS_INTERVAL_INTERVAL_MEMORY_HH

#include <domains/common/ConcreteAddressMemory.hh>
#include <domains/interval/IntervalAddress.hh>
#include <domains/interval/IntervalValue.hh>
#include <kernel/Architecture.hh>
#include <kernel/Memory.hh>
#include <kernel/RegisterMap.hh>


class IntervalMemory : public Memory<IntervalAddress, IntervalValue>,
		       public RegisterMap<IntervalValue>
{

  ConcreteAddressMemory<IntervalValue> mem;

public:
  IntervalMemory();
  virtual ~IntervalMemory() { }
  /*! \todo : constructeur de copy ? */


  virtual IntervalValue get(const IntervalAddress &a, int size, 
			    Architecture::endianness_t e) const
    throw (UndefinedValueException);

  virtual void put(const IntervalAddress &a, const IntervalValue &v, 
		   Architecture::endianness_t e);
  virtual bool is_defined(const IntervalAddress &a) const;

  virtual bool merge(const IntervalMemory &);

  using RegisterMap<IntervalValue>::get;
  using RegisterMap<IntervalValue>::put;
  using RegisterMap<IntervalValue>::is_defined;
  using RegisterMap<IntervalValue>::clear;

  virtual std::string pp();
};

#endif /* DOMAINS_INTERVAL_INTERVAL_MEMORY_HH */

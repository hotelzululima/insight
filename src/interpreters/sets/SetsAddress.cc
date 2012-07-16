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

#include <interpreters/sets/SetsAddress.hh>

#include <cassert>

#include <interpreters/sets/SetsValue.hh>

SetsAddress::SetsAddress(SetsValue v) : address(v) {}

SetsAddress::SetsAddress(ConcreteAddress addr) :
  address(Option<ConcreteValue>(ConcreteValue(sizeof(address_t) * 8, 
					      (word_t) addr.get_address())))
{
}


SetsAddress::~SetsAddress() 
{ 
}

SetsValue SetsAddress::get() const
{
  return address;
}

bool SetsAddress::equals(const Address &o) const
{
  const SetsAddress *ia = dynamic_cast<const SetsAddress *>(&o);

  assert(ia != NULL);

  return ia->address == address;
}

std::string SetsAddress::pp() const
{
  return address.pp();
}

Address *SetsAddress::clone() const
{
  return new SetsAddress(address);
}

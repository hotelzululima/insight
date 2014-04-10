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

#include "ConcreteAddress.hh"

#include <stdio.h>
#include <assert.h>

#include <sstream>
#include <iomanip>

using namespace std;


address_t
ConcreteAddress::get_address() const
{
  return address;
}

ConcreteAddress
ConcreteAddress::null_addr()
{
  return ConcreteAddress(0);
}

ConcreteAddress
ConcreteAddress::operator++(int)
{
  ConcreteAddress a = *this;
  address++;

  return a;
}

ConcreteAddress &
ConcreteAddress::operator++()
{
  address++;

  return *this;
}

bool
ConcreteAddress::operator==(const ConcreteAddress &a) const
{
  return this->address == a.address;
}

Address *
ConcreteAddress::clone() const
{
  return new ConcreteAddress(*this);
}

bool
ConcreteAddress::equals(const Address &adr) const
{
  assert(dynamic_cast<const ConcreteAddress *>(&adr) != NULL);
  const ConcreteAddress &ca = (ConcreteAddress &) adr;

  return (this->address == ca.address);
}

void
ConcreteAddress::output_text(ostream &os) const
{
  os << std::hex << std::setfill('0') << std::nouppercase
     << (int) this->address
     << std::dec;
}

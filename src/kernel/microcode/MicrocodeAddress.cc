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

#include <kernel/microcode/MicrocodeAddress.hh>

#include <stdio.h>

using namespace std;

MicrocodeAddress::MicrocodeAddress() :
	global(NULL_ADDRESS),
	local(0)
{}

MicrocodeAddress::MicrocodeAddress(address_t g) :
  global(g),
  local(0)
{}

MicrocodeAddress::MicrocodeAddress(address_t g, address_t l) :
  global(g),
  local(l)
{}

MicrocodeAddress::MicrocodeAddress(const MicrocodeAddress &addr)
  : Object (*this)
{
  global = addr.global;
  local = addr.local;
}

MicrocodeAddress::MicrocodeAddress(const MicrocodeAddress &addr, int incr_global, int incr_local)
{
  global = addr.global + incr_global;
  local = addr.local + incr_local;
}

MicrocodeAddress::~MicrocodeAddress() {}

MicrocodeAddress *MicrocodeAddress::clone() const
{
  return new MicrocodeAddress(this->global, this->local);
}

address_t MicrocodeAddress::getGlobal() const
{
  return this->global;
}

address_t MicrocodeAddress::getLocal() const
{
  return this->local;
}

std::size_t
MicrocodeAddress::hashcode () const
{
  return 19 * getGlobal () + 177 * getLocal ();
}

bool MicrocodeAddress::equals(const MicrocodeAddress &other) const
{
  return ((global == other.global) && (local == other.local));
}

bool MicrocodeAddress::lessThan(const MicrocodeAddress &other) const
{
  return ((global < other.global) ||
          ((global == other.global) && (local < other.local)));
}

MicrocodeAddress &
MicrocodeAddress::operator = (const MicrocodeAddress &other)
{
  new (this) MicrocodeAddress (other.global, other.local);

  return *this;
}

MicrocodeAddress MicrocodeAddress::null_addr()
{
  return MicrocodeAddress(NULL_ADDRESS);
}

void
MicrocodeAddress::output_text (std::ostream &out) const
{
  out << "(0x" << hex << global << "," << dec << local << ")";
}

MicrocodeAddress MicrocodeAddress::operator++ (int)
{
  MicrocodeAddress result (*this);

  local++;

  return result;
}

MicrocodeAddress operator +(const MicrocodeAddress &a, int loffset)
{
  return MicrocodeAddress (a, 0, loffset);
}

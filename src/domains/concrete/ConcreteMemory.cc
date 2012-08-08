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

#include "ConcreteMemory.hh"

#include <assert.h>
#include <inttypes.h>

#include <iomanip>
#include <iostream>
#include <list>
#include <sstream>

#include <domains/concrete/ConcreteAddress.hh>

#include <utils/bv-manip.hh>


using namespace std;

/*****************************************************************************/
/* Constructors                                                              */
/*****************************************************************************/

ConcreteMemory::ConcreteMemory() :
  Memory<ConcreteAddress, ConcreteValue>(), RegisterMap<ConcreteValue>(),
  memory()
{
}

ConcreteMemory::ConcreteMemory(ConcreteMemory & m) :
  Memory<ConcreteAddress,ConcreteValue>(m), RegisterMap<ConcreteValue>(m),
  memory(m.memory)
{
}

ConcreteMemory::~ConcreteMemory()
{
    memory.clear();
}

/*****************************************************************************/
/* Memory Access                                                             */
/*****************************************************************************/

ConcreteValue
ConcreteMemory::get(const ConcreteAddress &addr,
		    const int size,
		    const Architecture::endianness_t e) const
  throw (Architecture::UndefinedValue)
{
  word_t res = 0;
  address_t a = addr.get_address();

  for (int i = 0; i < size; i++)
    {
      address_t cur =
	(e == Architecture::LittleEndian ? a + size - i - 1 : a + i);

      if (!is_defined(ConcreteAddress(cur)))
	throw Architecture::UndefinedValue(addr.to_string ());

      res = (res << 8) | memory.find(cur)->second;
    }

  return ConcreteValue(8 * size, res);
}

void
ConcreteMemory::put(const ConcreteAddress &addr,
		    const ConcreteValue &value,
		    const Architecture::endianness_t e)
{
  word_t v = value.get();
  int size = value.get_size();
  address_t a = addr.get_address();

  if (size % 8)
    assert("cannot write value with non multiple of 8 size\n");

  size /= 8;

  for (int i = 0; i < size; i++)
    {
      address_t cur =
	(e == Architecture::BigEndian ? a + size - i - 1 : a + i);

      memory[cur] = v & 0xff;
      v >>= 8;
    }
}

bool
ConcreteMemory::is_defined(const ConcreteAddress &a) const
{
  return (memory.find(a.get_address()) != memory.end());
}

bool
ConcreteMemory::is_defined(const RegisterDesc *r) const
{
  return RegisterMap<ConcreteValue>::is_defined(r);
}

ConcreteValue
ConcreteMemory::get(const RegisterDesc * r) const
    throw (Architecture::UndefinedValue)
{
  assert (! r->is_alias ());
  /* Checking for unspecified access */
  if (!is_defined(r))
    {
      throw Architecture::UndefinedValue (r->get_label ());
    }

  int offset = r->get_window_offset ();
  int size = r->get_window_size ();
  word_t reg = regs_find(r)->second.get();
  word_t val = BitVectorManip::extract_from_word (reg, offset, size);

  return ConcreteValue(size, val);
}

void
ConcreteMemory::put(const RegisterDesc *r, ConcreteValue v)
{
  assert (! r->is_alias ());
  assert (r->get_register_size () == v.get_size());
  registermap[r] = v;
}


/*****************************************************************************/
/* Utils                                                                     */
/*****************************************************************************/

void
ConcreteMemory::output_text(ostream &os) const
{
  os << "Memory: " << endl;
  for (MemoryMap::const_iterator mem = memory.begin(); mem != memory.end(); 
       mem++)
    os << "[ 0x" << hex << setfill('0')
       << nouppercase << setw(4) << (int) mem->first
       << " -> 0x" << hex << setfill('0')
       << nouppercase << setw(2) << (int) mem->second << "]" << endl;
  os << endl;

  os << "Registers: " << endl;

  for (const_reg_iterator iter = regs_begin (); iter != regs_end (); iter++)
    {
      const RegisterDesc * reg = iter->first;
      os << reg->get_label () << ": "
	 << "0x" << hex << setfill('0') << setw(reg->get_register_size ()/4)
	 << nouppercase << iter->second
	 << dec << endl;
    }
}

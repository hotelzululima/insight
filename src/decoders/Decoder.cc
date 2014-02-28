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

#include "Decoder.hh"

class ConcreteMemoryReader : public Decoder::RawBytesReader 
{
public:
  ConcreteMemoryReader (const ConcreteMemory *M);

  virtual ~ConcreteMemoryReader ();

  virtual void read_buffer (address_t from, uint8_t *dest, size_t length)
    throw (Decoder::Exception);

private:
  const ConcreteMemory *memory;
};

Decoder::Decoder(MicrocodeArchitecture *arch, const ConcreteMemory *memory)
  : reader (new ConcreteMemoryReader (memory)), arch (arch)                
{
}

Decoder::Decoder(MicrocodeArchitecture *arch, RawBytesReader *reader)
  : reader (reader), arch (arch)
{
}

Decoder::~Decoder()
{
  delete reader;
}

void 
Decoder::set_memory (const ConcreteMemory *memory)
{
  if (reader != NULL)
    delete reader;
  reader = new ConcreteMemoryReader (memory);
}

const MicrocodeArchitecture *
Decoder::get_arch () const
{
  return arch;
}

ConcreteMemoryReader::ConcreteMemoryReader (const ConcreteMemory *M)
  : memory (M)
{
}

ConcreteMemoryReader::~ConcreteMemoryReader ()
{
}

void 
ConcreteMemoryReader::read_buffer (address_t from, uint8_t *dest, size_t length)
  throw (Decoder::Exception)
{
  for (size_t i = 0; i < length; i++)
    {
      if (memory->is_defined (from + i))
	dest[i] = memory->get(from + i, 1, Architecture::LittleEndian).get();
      else
	throw Decoder::OutOfBounds (from + i);
    }
}

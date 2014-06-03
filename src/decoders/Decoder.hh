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

#ifndef DECODER_HH
#define DECODER_HH

#include <string.h>

#include <string>
#include <utility>
#include <stdexcept>

#include <domains/concrete/ConcreteAddress.hh>
#include <domains/concrete/ConcreteMemory.hh>

#include <kernel/Microcode.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>

#include <utils/Object.hh>

/******************** Decoder class definition ***********************/

/** Pure abstract class to provide a clean interface for all decoder's
 * implementations. 'Decoder' class allow to translate an instruction
 * starting at a precise address into Microcode (translate(addr)).
 * Also, it allows to know where do start the next instruction to
 * decode (next(addr)). */

class Decoder : public Object
{
public:

  class Exception : public std::runtime_error {
  public:
    Exception (const std::string &msg) : std::runtime_error(msg) {}
  };

  /*********************** Decoder Exceptions **************************/
  /** \brief Exception thrown when the mnemonics is not recognized by
   *  the decoder */
  class UnknownMnemonic : public Exception
  {
  public:
    UnknownMnemonic(const std::string &instr) :
      Exception("'" + instr + "' : Unknown mnemonic") {}
  };

  /** \brief Exception thrown when the mnemonics does not match the
   *  needed operands */
  class InconsistentInstruction : public Exception
  {
  public:
    InconsistentInstruction(const std::string &instr) :
      Exception("'" + instr + "' : Inconsistent instruction") {}
  };

  /** \brief Exception thrown when the address given to the decoder is
   *  out of boundaries */
  class OutOfBounds : public Exception
  {
  private:
    ConcreteAddress addr;

  public:
    OutOfBounds(ConcreteAddress addr) :
      Exception("Decoding at 0x" + addr.to_string() + " is out of bounds"),
      addr(addr) { }

    ~OutOfBounds() throw () {}

    ConcreteAddress get_address() {
      return addr;
    }

  };

  /** \brief Exception thrown when the decoder encounter an unexpected
   *  problem */
  class DecoderUnexpectedError : public Exception
  {
  public:
    DecoderUnexpectedError(const std::string error) :
      Exception ("'" + error + "' : Unexpected error") { }
  };


  class RawBytesReader {
  public:
    virtual ~RawBytesReader() {}
    virtual void read_buffer (address_t from, uint8_t *dest, size_t length)
      throw (Decoder::Exception) = 0;
  };

  virtual ~Decoder();

  /* Translates the assembly instruction at 'addr' into Microcode.
   * Returns a pair<Microcode, ConcreteAddress> where:
   * - Microcode is the translation of the decoded instruction;
   * - ConcreteAddress is the address immediately after the
   *   decoded instruction.
   */
  virtual ConcreteAddress decode(Microcode *mc,
				 const ConcreteAddress &addr)
    throw (Exception) = 0;

  /* Returns the address immediately after instruction at 'addr'
   * without translating it into Microcode */
  virtual ConcreteAddress next(const ConcreteAddress &addr)
    throw (Exception) = 0;

  /* Set a new memory to decode */
  void set_memory(const ConcreteMemory *memory);

  const MicrocodeArchitecture *get_arch () const;

protected:
  /* Constructor is protected to enforce to use the DecoderFactory */
  Decoder(MicrocodeArchitecture *arch, const ConcreteMemory *memory);

  /* Constructor is protected to enforce to use the DecoderFactory */
  Decoder(MicrocodeArchitecture *arch, RawBytesReader *reader);

  /* A pointer on the memory to decode */
  RawBytesReader *reader;
  MicrocodeArchitecture *arch;
};

#endif /* DECODER_HH */

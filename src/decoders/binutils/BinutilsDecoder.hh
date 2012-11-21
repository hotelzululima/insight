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

#ifndef BINUTILSDECODER_HH
#define BINUTILSDECODER_HH

#include <config.h>

#include <bfd.h>
#include <dis-asm.h>

#include <sstream>

#include <decoders/Decoder.hh>
#include <kernel/Microcode.hh>

/* Decoder function type */
typedef bool 
(*decoder_ftype)(MicrocodeArchitecture *arch,
		 Microcode *mc, 
		 const std::string &instruction,
                 const ConcreteAddress &start,
                 const ConcreteAddress &next);


/* Abstract class that factorize code common to all binutils decoders */
class BinutilsDecoder : public Decoder
{
public:
  BinutilsDecoder(MicrocodeArchitecture *arch, ConcreteMemory *mem);
  virtual ~BinutilsDecoder();

  /***** Using the decoder *****/

  /* Returns the microcode and the address of the next instruction */
  virtual ConcreteAddress decode(Microcode *mc,
				 const ConcreteAddress &addr)
    throw (Exception);

  /* Returns the address of the next instruction */
  virtual ConcreteAddress next(const ConcreteAddress &addr);

  /* Returns a string with instruction's mnemonic and its arguments */
  std::string get_instruction (const ConcreteAddress &addr);

  /***** Setting the decoder *****/
  struct disassemble_info *get_disassembler_info();
  void set_disassembler_info(struct disassemble_info *info);

private:
  /* Decoder internal fields */
  decoder_ftype decoder;              /* Decoder function */
  struct disassemble_info *info;      /* Disassembler info */
  disassembler_ftype disassembler_fn; /* Disassembler function */
  std::stringstream *instr_buffer;    /* Disassembled instruction buffer */
};

#endif /* BINUTILSDECODER_HH */

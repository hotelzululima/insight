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
#ifndef KERNEL_MICROCODE_MICROCODE_ADDRESS_HH
#define KERNEL_MICROCODE_MICROCODE_ADDRESS_HH

#include <kernel/Address.hh>
#include <kernel/Architecture.hh>

/* MicrocodeAddress is intended to allow to split macro assembler
 * instructions into smaller steps. So, the 'global' address is the
 * address of the assembly instruction. And the 'local' address
 * correspond to the address of one of the microinstruction needed to
 * code the higher level assembly instruction. A microcode address is
 * therefore represented as a couple (global_addr, local_addr).
 *
 * For example, an instruction at global address 0xdeadbeef might be
 * splitted into several microinstructions each it localized at
 * (0xdeadbeef, 0), (0xdeadbeef, 1), (0xdeadbeef, 2), and so on. */

class MicrocodeAddress : public Object {
private:
  address_t global;
  address_t local;

public:
  MicrocodeAddress();
  MicrocodeAddress(address_t addr);
  MicrocodeAddress(address_t g, address_t l);
  MicrocodeAddress(const MicrocodeAddress &addr);
  MicrocodeAddress(const MicrocodeAddress &addr, int incr_global, int incr_local);
  ~MicrocodeAddress();
  static MicrocodeAddress null_addr();

  MicrocodeAddress * clone() const;
  address_t getGlobal() const;
  address_t getLocal() const;

  MicrocodeAddress operator++ (int);
  virtual void output_text (std::ostream &out) const ;

  std::size_t hashcode () const;
  bool equals(const MicrocodeAddress &other) const;
  bool lessThan(const MicrocodeAddress &other) const;
  MicrocodeAddress &operator = (const MicrocodeAddress &other);
};

MicrocodeAddress operator +(const MicrocodeAddress &a, int loffset);

#endif /* KERNEL_MICROCODE_MICROCODE_ADDRESS_HH */

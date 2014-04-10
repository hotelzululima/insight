/*
 * Copyright (c) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef SYMBOLICMEMORY_HH
# define SYMBOLICMEMORY_HH


# include <kernel/Memory.hh>
# include <kernel/RegisterMap.hh>
# include <domains/concrete/ConcreteMemory.hh>
# include <domains/symbolic/SymbolicValue.hh>
# include <utils/unordered11.hh>

class SymbolicMemory 
  : public Memory<ConcreteAddress, SymbolicValue>,
    public RegisterMap<SymbolicValue>
{
  address_t minaddr;
  address_t maxaddr;

public:
  typedef std::unordered_map<address_t, SymbolicValue> MemoryMap;
  typedef MemoryMap::const_iterator const_memcell_iterator;
  typedef ConcreteAddress Address;
  typedef SymbolicValue Value;

  SymbolicMemory (const ConcreteMemory *base);

  virtual ~SymbolicMemory();

  virtual SymbolicValue 
  get(const ConcreteAddress &a, int size_in_bytes, 
      Architecture::endianness_t e) const
    throw (UndefinedValueException);

  virtual void put (const ConcreteAddress &a, const SymbolicValue &v, 
		    Architecture::endianness_t e);

  virtual bool is_defined(const ConcreteAddress &a) const;

  virtual SymbolicMemory *clone () const;

  virtual bool is_defined(const RegisterDesc *rdesc) const;
  virtual SymbolicValue get(const RegisterDesc *rdesc) const 
    throw (UndefinedValueException);

  using RegisterMap<SymbolicValue>::put;

  virtual void output_text (std::ostream &out) const;

  virtual bool equals (const SymbolicMemory &mem) const;
  virtual std::size_t hashcode () const;


  void get_address_range (address_t &min, address_t &max) const; 
  virtual const_memcell_iterator begin () const;
  virtual const_memcell_iterator end () const;

private:
  const ConcreteMemory *base;
  MemoryMap memory;
};

#endif /* ! SYMBOLICMEMORY_HH */

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
#ifndef DOMAINS_COMMON_CONCRETE_ADDRESS_MEMORY_HH
#define DOMAINS_COMMON_CONCRETE_ADDRESS_MEMORY_HH

#include <sstream>
#include <iostream>
#include <ext/hash_map>

#include <domains/concrete/ConcreteAddress.hh>

#include <kernel/Architecture.hh>
#include <kernel/Memory.hh>
#include <kernel/Expressions.hh>

template <typename Value>
class ConcreteAddressMemory : public Memory<ConcreteAddress, Value>
{

protected:

  /*! \brief This class represents a value as stored in the hash table.
    We need to keep track of whether the value was partially
    overwritten by some other value. */
  struct ConcreteAddressMemoryValue
  {
    Value value;

    /*! \brief mask where bit n is true if byte n of the value was written to */
    int is_broken;
    Architecture::endianness_t endianness;
  };

  static ConcreteAddressMemoryValue *CAMV_copy(ConcreteAddressMemoryValue *);

  /*! \brief This class represents a byte within a value stored in memory. */
  struct ConcreteAddressMemoryCell
  {
    ConcreteAddressMemoryValue *mvalue;

    /*! offset is the offset in bytes, 0 means the byte is the least significant
      byte of the value */
    int offset;
  };

  typedef __gnu_cxx::hash_map<address_t, ConcreteAddressMemoryCell> memory_type;
  memory_type memory;

public:

  ConcreteAddressMemory();
  ConcreteAddressMemory(const ConcreteAddressMemory &);
  virtual ~ConcreteAddressMemory() {};

  /*! \brief get a value of size bytes at address a with endianness e */
  virtual Value get(const ConcreteAddress &a, int size, 
		    Architecture::endianness_t e) throw (UndefinedValue);

  /*! \brief put a value v at address a with endianness e */
  virtual void put(const ConcreteAddress &a, const Value &v, 
		   Architecture::endianness_t e);

  virtual bool is_undefined(const ConcreteAddress &a) const;

  /*! \brief Tell whether the memory is empty or not */
  bool is_empty() const;

  virtual std::string pp();
  std::string dump();

  /*! \brief Iterator on all the unbroken plain value contained in the
   *  memory. It is used in particular for the merge operation. Let us
   *  note that this class behaves as a filter from the memory: it
   *  enumerates just non broken values, abstracting the byte level. */
  class ValueIterator
  {

  private:
    const ConcreteAddressMemory<Value> * mem;
    typename memory_type::const_iterator p;

    /*! \brief iterate until finding a plain unbroken value. */
    void look_for_value();

  public:
    /*! \brief At the creation of the object, the iterator starts on
        the first pair corresponding to a plain unbroken value. */
    ValueIterator(const ConcreteAddressMemory<Value> *m);

    /*! \brief Copy Conctructor. */
    ValueIterator(const ValueIterator &other);

    /*! \brief Destructor. RAS */
    ~ValueIterator();

    bool end();

    /*! \brief go to the next unbroken plain value */
    ValueIterator operator++(int);

    /*! \brief retrieves the address of the current record pointed by the
	iterator */
    ConcreteAddress get_address();

    /*! \brief retrieves the current value pointed by the iterator */
    Value get_value();

    /*! \brief retrieves the endianness of the current value pointed
        by the iterator */
    Architecture::endianness_t get_endianness();

  };

  /*! \brief Provides an iterator on all the values contained in the
      memory */
  virtual ValueIterator get_value_iterator() const;

};

#include "ConcreteAddressMemory.ii"

#endif /* DOMAINS_COMMON_CONCRETE_ADDRESS_MEMORY_HH */

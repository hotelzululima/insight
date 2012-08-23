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

#ifndef KERNEL_MEMORY_HH
#define KERNEL_MEMORY_HH

#include <kernel/Architecture.hh>

class UndefinedValueException;

/** \brief Abstract class to represent the memory of a program.
 *
 * The memory is architecture agnostic, it is just a container that
 * will hold the values of the memorycells in an efficient manner
 * depending on the selected abstract domain. It is usually used
 * together with an instantiated RegisterMap class through an
 * inheritance link. The final memory object, thus, can address both
 * memorycells and registers. It, therefore, holds the state of the
 * program.
 */
template <typename Address, typename Value>
class Memory : public Object
{
public:
  Memory();
  Memory(const Memory<Address, Value> &);

  virtual ~Memory() {};

  virtual Value get(const Address &, int, Architecture::endianness_t) const
    throw (UndefinedValueException) = 0;

  virtual void put(const Address &, const Value &,
		   Architecture::endianness_t) = 0;

  /** \brief Tells whether a memory cell has been initialized before or not. */
  virtual bool is_defined(const Address &) const = 0;
};

class UndefinedValueException : public std::runtime_error
{
public:
  UndefinedValueException (const std::string &where) :
    std::runtime_error(": Undefined value at " + where) { }
};

#include "Memory.ii"

#endif /* KERNEL_MEMORY_HH */

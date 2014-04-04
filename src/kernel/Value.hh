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

#ifndef KERNEL_VALUE_HH
#define KERNEL_VALUE_HH

#include <utils/Object.hh>
#include <utils/Option.hh>
#include <kernel/microcode/MicrocodeAddress.hh>

/** \brief Abstract class to represent values stored in memory.
 *
 * Implementation of this abstract class will define various abstract
 * domains. Given an operational semantics, the interpreter will be
 * able to run through the program and compute effects. */
class Value : public Object
{
protected:
  /** \brief Size in bits. */
  int size;

  /** \brief Default constructor (note that a value must always store
   *  at least its size). */
  Value(int size);

public:
  virtual ~Value();

  /** \brief Get the value size in bits. */
  int get_size() const;

  virtual Option<bool> to_bool () const  = 0;
  virtual Option<MicrocodeAddress> to_MicrocodeAddress () const  = 0;
};

template <typename V>
class UnknownValueGenerator 
{
public:
  virtual V unknown_value (int size) = 0;
};

#endif /* KERNEL_VALUE_HH */

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

#ifndef DOMAINS_CONCRETE_CONCRETEVALUE_HH
#define DOMAINS_CONCRETE_CONCRETEVALUE_HH

#include <string>

#include <kernel/Architecture.hh>
#include <kernel/Expressions.hh>
#include <kernel/Value.hh>
#include <kernel/microcode/MicrocodeAddress.hh>

#include <utils/Option.hh>

/** \brief This is the base word for memory and register contents.  */
class ConcreteValue : public Value
{
  /** \brief the content of a concrete value is stored here */
  word_t value;

public:

  /* This shouldn't be needed, but hash tables seem to require the
     ability to call this constructor... */
  ConcreteValue();

  /** \brief copy constructor */
  ConcreteValue(const ConcreteValue &);

  /** \brief Construct the ConcreteValue object from a real
      value. Size is given in bits (see Value class) */
  ConcreteValue(int size, word_t w);

  virtual ConcreteValue *clone() const;

  /*! \brief Construct the ConcreteValue object from a real value. */
  ConcreteValue(const Constant *c);

  /** \brief Return the default value. This is used when some read
    access is done to an unknown value */
  static ConcreteValue unknown_value (int size);

  /** \return the actual value stored */
  word_t get() const;

  bool operator==(const ConcreteValue &) const;

  void output_text(std::ostream &out) const;

  MicrocodeAddress to_MicrocodeAddress () const;

  Option<bool> to_bool () const;
};

#endif /* DOMAINS_CONCRETE_CONCRETEVALUE_HH */

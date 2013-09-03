/*-
 * Copyright (C) 2010-2013, Centre National de la Recherche Scientifique,
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
#ifndef DOMAINS_INTERVAL_INTERVAL_VALUE_HH
#define DOMAINS_INTERVAL_INTERVAL_VALUE_HH

#include <string>

#include <utils/Option.hh>

#include <kernel/Architecture.hh>
#include <kernel/Expressions.hh>
#include <kernel/Microcode.hh>
#include <kernel/Value.hh>

class IntervalValue : public Value
{
  word_t min;
  word_t max;
  bool is_top;
public:

  IntervalValue() : Value(0)
  {
    is_top = true;
  };

  IntervalValue(int size) : Value(size)
  {
    is_top = true;
  };

  IntervalValue(int size, word_t one) : Value(size)
  {
    min = max = one;
    is_top = false;
  };

  IntervalValue(int size, word_t min, word_t max) : Value(size)
  {
    this->min = min;
    this->max = max;
    is_top = false;	/*! \todo this requires a test */
  };

  IntervalValue(Constant *c) : Value(c->get_bv_size())
  {
    new(this) IntervalValue(c->get_bv_size(), c->get_val());
  };

  virtual ~IntervalValue() { }

  /*! \brief Return the default value. This is used when some read
    access is done to an unknown value */
  static IntervalValue unknown_value(int size);

  virtual word_t getMin() const
  {
    return min;
  }
  virtual word_t getMax() const
  {
    return max;
  }

  virtual Option<bool> to_bool() const;

  Option<MicrocodeAddress>
  to_MicrocodeAddress() const
  {
    return Option<MicrocodeAddress>();
  }

  virtual IntervalValue *clone() const;

  virtual void of_constant(Constant *c);

  static IntervalValue join(const IntervalValue &v1,
                            const IntervalValue &v2);

  void output_text(std::ostream &out) const;

  virtual bool equals (const IntervalValue &v) const;

private:
  bool operator==(const IntervalValue &o) const;
};

#endif /* DOMAINS_INTERVAL_INTERVAL_VALUE_HH */

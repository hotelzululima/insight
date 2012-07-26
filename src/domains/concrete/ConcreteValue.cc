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

#include "ConcreteValue.hh"

#include <iomanip>
#include <iostream>
#include <sstream>
#include <utils/bv-manip.hh>
#include <kernel/Expressions.hh>

using namespace std;

ConcreteValue::ConcreteValue() : Value(0), value(0) 
{ 
}

ConcreteValue::ConcreteValue(int size, word_t w) : Value(size), value(w) 
{ 
}

ConcreteValue::ConcreteValue(const ConcreteValue &cv) : Value(cv.get_size())
{
  this->value = cv.get();
}

ConcreteValue::ConcreteValue(const Constant *c) : Value(c->get_bv_size())
{
  value = (word_t) c->get_val();
}

ConcreteValue * ConcreteValue::clone() const
{
  return new ConcreteValue(get_size(), this->value);
}

ConcreteValue ConcreteValue::unknown_value(int size)
{
  return ConcreteValue(size, 0);
}

word_t ConcreteValue::get() const
{
  word_t result = BitVectorManip::extract_from_word (value, 0, size);

  return result;
}

bool
ConcreteValue::operator==(const ConcreteValue &v) const
{
  return ((this->size == v.get_size()) && (get () == v.get()));
}

void
ConcreteValue::output_text(std::ostream &os) const
{
  os << (uint64_t)this->value << dec << "{" << this->size << "}";
}

MicrocodeAddress 
ConcreteValue::to_MicrocodeAddress () const
{
  return MicrocodeAddress (get ());
}

Option<bool>
ConcreteValue::to_bool () const
{
  return Option<bool>(get () != 0);
}

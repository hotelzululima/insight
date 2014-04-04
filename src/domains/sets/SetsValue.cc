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

#include "SetsValue.hh"

#include <map>
#include <string>
#include <sstream>
#include <iostream>

SetsValue::SetsValue() :
  Value(BV_DEFAULT_SIZE),
  the_set(),
  is_TOP(false)
{}

SetsValue::SetsValue(int size) :
  Value(size),
  the_set(),
  is_TOP(false)
{}

SetsValue::SetsValue(const SetsValue &other) :
  Value(other.get_size()),
  the_set(other.the_set),
  is_TOP(other.is_TOP)
{}

struct UnknownSetsValue : public UnknownValueGenerator<SetsValue>
{
  SetsValue unknown_value (int size) {
    SetsValue dv (size);
    dv.any ();
    return dv;
  }
};

UnknownValueGenerator<SetsValue> *
SetsValue::unknown_value_generator ()
{
  static UnknownSetsValue gen;

  return &gen;  
}

SetsValue::SetsValue(int size, word_t val) :
  Value(size), the_set(), is_TOP(false)
{
  the_set.insert(ConcreteValue (size, val));
}

SetsValue::SetsValue(Option<ConcreteValue> v) :
  Value(BV_DEFAULT_SIZE),
  the_set(),
  is_TOP(false)
{
  if (v.hasValue())
    {
      the_set.insert(v.getValue());
      size = v.getValue().get_size();
    }
  else
    is_TOP = true;
}

SetsValue::SetsValue(Constant *c) : Value(c->get_bv_size())
{
  new(this) SetsValue(Option<ConcreteValue>(ConcreteValue(c)));
}

SetsValue::~SetsValue() {}

SetsValue::SetsValue(ConcreteValueSet values) :
  Value(BV_DEFAULT_SIZE),  // \todo voir les size en detail
  the_set(values),
  is_TOP(false)
{}

SetsValue *SetsValue::clone() const
{
  return new SetsValue(*this);
}

Option<ConcreteValue> SetsValue::extract_value() const
{

  if (the_set.size() == 1)
    {
      ConcreteValueSet::iterator elt = the_set.begin();
      return Option<ConcreteValue>(*elt);
    }
  else
    return Option<ConcreteValue>();
}

Option< std::list<ConcreteValue> > SetsValue::get_values()
{
  if (is_TOP) return Option< std::list<ConcreteValue> >();
  std::list<ConcreteValue> result;
  for (ConcreteValueSet::iterator elt = the_set.begin(); elt != the_set.end(); elt++)
    result.push_back(*elt);
  return result;
}

bool SetsValue::contains(ConcreteValue v)
{
  if (is_TOP) return true;
  ConcreteValueSet::iterator p = the_set.find(v);
  return (p != the_set.end());
}

bool SetsValue::add_value(Option<ConcreteValue> v)
{
  if (is_TOP) return false;

  if (!(v.hasValue()))
    {
      the_set.clear();
      is_TOP = true;
      return true;
    }

  // \todo : does not work ?
  //std::pair<ConcreteValueSet::iterator, bool> p = the_set.insert(v.getValue());
  //return p.second;

  unsigned int old_card = the_set.size();
  the_set.insert(v.getValue());
  return old_card < the_set.size();
}

#include <iostream>

bool SetsValue::add(SetsValue other)
{

  if (other.is_any())
    {
      if (is_TOP) return false;
      the_set.clear();
      is_TOP = true;
      return true;
    }

  bool modified = false;
  std::list<ConcreteValue> other_values = other.get_values().getValue();
  for (std::list<ConcreteValue>::iterator
       v = other_values.begin();
       v != other_values.end();
       v++)
    {
      bool local_modif = this->add_value(Option<ConcreteValue>(*v));
      modified = modified || local_modif;
    }

  return modified;
}

void SetsValue::any()
{
  the_set.clear();
  is_TOP = true;
}

bool SetsValue::is_any() const
{
  return is_TOP;
}

Option<bool> SetsValue::to_bool() const
{
  if (is_TOP || (the_set.size() == 0)) return Option<bool>();

  // retrieves the first value and checks that all the other ones are equal
  ConcreteValueSet::iterator elt = the_set.begin();
  ConcreteValue v = *elt; // copy the element not to discard qualifier (set iterator are const), \todo the good way should be to make 'to_bool' function const
  bool result = v.to_bool().getValue(); // ConcreteValue always provide a bool value
  elt++;
  for (; elt != the_set.end(); elt++)
    {
      v = *elt;
      if (result != v.to_bool().getValue())
        return Option<bool>();
    }
  return Option<bool>(result);
}

Option<MicrocodeAddress> SetsValue::to_MicrocodeAddress() const
{
  Option<ConcreteValue> addr = this->extract_value();
  if (addr.hasValue ())
    return addr.getValue().to_MicrocodeAddress();
  else
    return MicrocodeAddress ();
}

bool
SetsValue::equals (const SetsValue &v) const
{
  if (is_TOP)
    return v.is_any();

  if (v.is_any())
    return is_TOP;

  if (the_set.size() != v.the_set.size())
    return false;

  ConcreteValueSet::iterator v1 = the_set.begin();
  ConcreteValueSet::iterator v2 = v.the_set.begin();
  while ((v1 != the_set.end()) && (v1->equals (*v2)))
    {
      v1++;
      v2++;
    }

  return (v1 == the_set.end());
}

void
SetsValue::output_text(std::ostream &os) const
{
  if (is_TOP) os << "{TOP}";
  else
    {
      if (the_set.size() == 0)
        {
          os << "{}";
        }
      else
        {
          ConcreteValueSet::iterator elt = the_set.begin();
	  // copy the element not to discard qualifier (set iterator are const),
          ConcreteValue v = *elt;
          // \todo the good way should be to make 'to_bool' function const
          os << "{";
	  v.output_text(os);
          elt++;
          for (; elt != the_set.end(); elt++)
            {
              v = *elt;
              os << ";";
	      v.output_text(os);
            }
          os << "}";
        }
    }
}


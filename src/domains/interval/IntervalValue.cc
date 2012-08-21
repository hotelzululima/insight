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

#include <domains/interval/IntervalValue.hh>
#include <utils/tools.hh>

#include <algorithm>
#include <sstream>
#include <string>

using namespace std;

//const IntervalValue IntervalValue::top(((uword_t)-1 >> 1) + 1,
//	(uword_t)-1 >> 1);

Option<bool>
IntervalValue::to_bool() const
{
  if (min > 0 || max < 0)
    return Option<bool>(true);

  if (max == min)	// implies it's zero given test before
    return Option<bool>(false);

  return Option<bool>();
}

IntervalValue
IntervalValue::join(const IntervalValue &v1, const IntervalValue &v2)
{
  if (v1.get_size() != v2.get_size())
    log::fatal_error("IntervalValue::Join(): values have different size");

  return IntervalValue(v1.get_size(),
                       std::min(v1.getMin(), v2.getMin()),
                       std::max(v1.getMax(), v2.getMax()));
}

IntervalValue *
IntervalValue::clone() const
{
  /* XXX probably doesn't clone top correctly */
  return new IntervalValue(get_size(), getMin(), getMax());
}


IntervalValue IntervalValue::unknown_value(int size)
{
  return IntervalValue (size, 0);
}


void
IntervalValue::of_constant(Constant *c)
{
  min = max = c->get_val();
}

bool
IntervalValue::operator==(const IntervalValue &o) const
{
  return get_size() == o.get_size() &&
         o.getMin() == getMin() && o.getMax() == getMax();
}

string
IntervalValue::pp() const
{
  ostringstream buf;

  if (this->is_top)
    buf << "TOP";
  else
    buf << "[ " << getMin() << ", " << getMax() << "]";

  buf << " (" << get_size() << " bits)";

  return buf.str();
}

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
#ifndef UTILS_OPTION_HH
#define UTILS_OPTION_HH

class OptionNoValueExc {};

template <typename T>
class Option
{
  T stored;
  bool isSome;

public:
  /*! \brief Default constructor, similar to None in ML */
  Option()
  {
    isSome = false;
  }
  /*! \brief Constructor with a value, similar to Some in ML */
  Option(T val)
  {
    stored = val;
    isSome = true;
  }

  /*! \brief Copy constructor */
  Option(const Option &other) :
    stored(other.stored),
    isSome(other.isSome)
  {};

  /*! \brief Check if a value is stored */
  bool hasValue()
  {
    return isSome;
  }

  /*! \brief Get the value if present, throw a dirty exception otherwise */
  T getValue()
  {
    if (!isSome)
      throw OptionNoValueExc();
    return stored;
  }
};

#endif /* UTILS_OPTION_HH */

/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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
#ifndef DOMAINS_SETS_SETS_VALUE_HH
#define DOMAINS_SETS_SETS_VALUE_HH

#include <set>
#include <string>

#include <domains/concrete/ConcreteValue.hh>

#include <kernel/Architecture.hh>
#include <kernel/Value.hh>
#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>

#include <utils/Option.hh>

/*****************************************************************************/

struct ConcreteValueCompare
{
  bool operator()(ConcreteValue v1, ConcreteValue v2) const
  {
    return (v1.get() < v2.get()) ;
  }
};

/*! \brief Set of Microcode Nodes */
typedef std::set<ConcreteValue, ConcreteValueCompare> ConcreteValueSet;

/*****************************************************************************/

/*! \brief Value sets are represented in this class.
 *  This either a set of values, or a full set (top).
 *  It is templated by the type of values. For instance
 *  ConcreteValues. */
class SetsValue : public Value
{

  /*! \brief The set of values, if the set is not TOP. */
  ConcreteValueSet the_set;

  /*! \brief Tells if the value is TOP or not. */
  bool is_TOP;

public:
  /*! \brief size is fixed to BV_DEFAULT_SIZE */
  SetsValue();

  /*! \brief Constructs a value containing just nothing, size is given
   *  in bits */
  SetsValue(int size);
  SetsValue(int size, word_t val);

  SetsValue(const SetsValue &);

  /*! \brief Constructs the singleton containing v, or TOP if v is
   *  None */
  SetsValue(Option<ConcreteValue> v);

  /*! \brief Constructor from the set of values (the set is cloned) */
  SetsValue(ConcreteValueSet values);

  SetsValue(Constant *c);

  /*! \brief Destructor. */
  virtual ~SetsValue();

  /*! \brief Clone the set */
  virtual SetsValue *clone() const;

  Option<MicrocodeAddress> to_MicrocodeAddress() const;

  /*! \brief returns the concrete value if the set is actually a
      singleton, otherwise returns None */
  Option<ConcreteValue> extract_value() const;

  /*! \brief Return the default value. This is used when some read
   *  access is done to an unknown value */
  static UnknownValueGenerator<SetsValue> *unknown_value_generator ();

  /*! \brief None means ANY value, i.e. TOP. Otherwise, this returns
   *  the list of all the possible values.
   *  \todo Optim : avoid the copy of the result */
  Option< std::list<ConcreteValue> > get_values();

  /*! \brief Adds a new value to the set. If the size is different,
   * raise an exception. If the set is empty, then the size is fixed
   * to the size of v. Caution the value maybe TOP.
   * \return true iff v was not in the current set. */
  bool add_value(Option<ConcreteValue> v);

  /*! \brief Tells whether the set contains v or not. */
  bool contains(ConcreteValue v);

  /*! \brief Adds all the value of other to the current one.
   *  \return true iff at least one new value has been added,
   *  i.e. iff there is at least one value in other which was not
   *  in the current set. */
  bool add(SetsValue other);

  /* \brief Sets the value to top, i.e. any element */
  void any();

  /*! \brief Tells whether the value is top or not */
  bool is_any() const;

  /*! \brief Output to text */
  void output_text(std::ostream &out) const;

  /*! \brief extract a bool value from the set; all the value of the
   *  set should produce the same boolean */
  Option<bool> to_bool() const;

  /*! \brief Term-to-term equality */
  virtual bool equals (const SetsValue &v) const;
};

#endif /* DOMAINS_SETS_SETS_VALUE_HH */

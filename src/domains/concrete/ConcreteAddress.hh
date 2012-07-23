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

#ifndef INTERPRETERS_CONCRETE_CONCRETEADDRESS_HH
#define INTERPRETERS_CONCRETE_CONCRETEADDRESS_HH

#include <inttypes.h>

#include <domains/concrete/ConcreteValue.hh>

#include <kernel/Address.hh>
#include <kernel/Architecture.hh>

/** \brief Real Concrete address for memory access */
class ConcreteAddress : public Address
{
  /** \brief Real address. See Architecture.hh for type definition */
  address_t address;

public:
  /** \brief Default constructor without initialization (default
   *  value: null address ) */
  ConcreteAddress() : Address(), address(0) {};

  /** \brief Copy constructor. */
  ConcreteAddress(const ConcreteAddress &a) : Address(), address(a.address) {};

  /** \brief Define the null address */
  static ConcreteAddress null_addr();

  /** \brief Default constructor with an initialization */
  ConcreteAddress(address_t a) : address(a) {};

  ConcreteAddress(ConcreteValue v) :
  Address(), address((address_t) v.get()) {};

  virtual Address *clone() const;

  /** \brief Postfix ++ */
  ConcreteAddress operator++(int);

  /** \brief Prefix ++ */
  ConcreteAddress &operator++();


  /** \brief Retrieves the actual value of the address */
  address_t get_address() const;

  /** \brief Equality */
  bool operator==(const ConcreteAddress &a)
  {
    return address == a.address;
  };

  virtual bool equals(const Address &addr) const;

  void output_text(std::ostream &) const;
};

#endif /* INTERPRETERS_CONCRETE_CONCRETEADDRESS_HH */

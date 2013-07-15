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

#ifndef KERNEL_REGISTERMAP_HH
#define KERNEL_REGISTERMAP_HH

#include <tr1/unordered_map>

#include <kernel/Memory.hh>

/** \brief Templatized class to represent the registers of a program.
 *
 * Used as a default implementation for register storage in any memory
 * (see Memory class for more information). Specialization of this
 * class can be performed by overloading methods get() and put().
 */
template <typename Value>
class RegisterMap : public Object
{
public:
  /** \brief Data structure used to encode the register table */
  typedef std::tr1::unordered_map<const RegisterDesc *,
				  Value, RegisterDesc::Hash > RegisterHashMap;
  typedef typename RegisterHashMap::const_iterator const_reg_iterator;
  typedef typename RegisterHashMap::iterator reg_iterator;

  RegisterMap();

  RegisterMap(const RegisterMap &other);

  virtual ~RegisterMap ();

  /** \brief Retrieve the content of a register */
  virtual Value get(const RegisterDesc *) const 
    throw (UndefinedValueException);

  /** \brief Put the value v into the register */
  virtual void put(const RegisterDesc *, Value);

  /** \brief Tell whether a given register has been set before or not. */
  virtual bool is_defined(const RegisterDesc *) const;

  virtual const_reg_iterator regs_begin () const;
  virtual const_reg_iterator regs_end () const;
  virtual const_reg_iterator regs_find (const RegisterDesc *) const;
  virtual reg_iterator regs_begin ();
  virtual reg_iterator regs_end ();
  virtual reg_iterator regs_find (const RegisterDesc *);
  virtual void clear(const RegisterDesc *);

  /** \brief Text output */
  virtual void output_text(std::ostream &) const;

private:

  /** \brief Register Values Table */
  RegisterHashMap registermap;
};

#include "RegisterMap.ii"

#endif /* KERNEL_REGISTERMAP_HH */

/*
 * Copyright (c) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#ifndef SYMBOLICVALUE_HH
# define SYMBOLICVALUE_HH

# include <kernel/Value.hh>
# include <kernel/Memory.hh>
# include <kernel/Expressions.hh>
# include <domains/concrete/ConcreteAddress.hh>

class UndefinedValueException;

class SymbolicValue : public Value
{
public:
  SymbolicValue ();
  SymbolicValue (const SymbolicValue &sv);
  SymbolicValue (int size, word_t val);
  explicit SymbolicValue (const Expr *e);
  virtual ~SymbolicValue ();

  SymbolicValue &operator= (const SymbolicValue &sv);
  operator ConcreteAddress () const throw (UndefinedValueException);
  virtual const Expr *get_Expr () const;
  virtual Option<bool> to_bool () const;
  virtual Option<MicrocodeAddress> to_MicrocodeAddress () const;
  virtual void output_text (std::ostream &out) const;
  virtual void simplify ();
  virtual bool equals (const SymbolicValue &sv) const;
  static SymbolicValue unknown_value (int size);
private:
  Expr *value;
};

#endif /* ! SYMBOLICVALUE_HH */

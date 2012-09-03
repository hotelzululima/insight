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
#include <cassert>
#include <sstream>
#include <kernel/expressions/exprutils.hh>
#include <kernel/Memory.hh>
#include "SymbolicValue.hh"

SymbolicValue::SymbolicValue () : Value (0)
{
  value = NULL;
}

SymbolicValue::SymbolicValue (const SymbolicValue &sv)
  : Value (sv.get_size ())
{  
  if (sv.value != NULL)
    value = sv.value->ref ();
  else
    value = NULL;  

  assert (value == NULL || get_size () == value->get_bv_size ());
}

SymbolicValue::SymbolicValue (int size, word_t val) : Value (size)
{
  value = Constant::create (val, 0, size);
}

SymbolicValue::SymbolicValue (const Expr *e) 
  : Value (e->get_bv_size ()), value (e->ref ())
{
}

SymbolicValue::~SymbolicValue ()
{
  if (value != NULL)
    value->deref ();
}

SymbolicValue & 
SymbolicValue::operator= (const SymbolicValue &sv)
{
  if (value != NULL)
    value->deref ();
  new (this) SymbolicValue (sv);

  return *this;
}

const Expr *
SymbolicValue::get_Expr () const
{
  return value;
}

Option<bool> 
SymbolicValue::to_bool () const
{
  if (value != NULL)
    return value->try_eval_level0 ();
  return Option<bool> ();
}

Option<MicrocodeAddress> 
SymbolicValue::to_MicrocodeAddress () const
{
  Option<MicrocodeAddress> result;

  if (value != NULL)
    {
      Expr *tmp = value->ref ();
      exprutils::simplify (&tmp);
      Constant *c = dynamic_cast<Constant *> (tmp);
      if (c != NULL)
	result = MicrocodeAddress ((address_t)c->get_val ());
      tmp->deref ();
    }
  return result;
}

void 
SymbolicValue::output_text (std::ostream &out) const
{
  if (value != NULL)
    value->output_text (out);
  else
    out << "<nullexpr>";
}

void
SymbolicValue::simplify ()
{
  if (value != NULL)
    exprutils::simplify (&value);
}

SymbolicValue::operator ConcreteAddress () const
  throw (UndefinedValueException)
{
  ConcreteAddress result;
  
  if (value == NULL)
    throw UndefinedValueException ("NULL symbolic location");    

  Expr *tmp = value->ref ();
  exprutils::simplify (&tmp);
  Constant *c  = dynamic_cast<Constant *> (tmp);
  if (c != NULL)    
    result = ConcreteAddress ((address_t) c->get_val ());    
  else
    {
      tmp->deref ();
      throw UndefinedValueException (value->to_string ());
    }
  tmp->deref ();

  return result;
}

bool 
SymbolicValue ::operator==(const SymbolicValue &sv) const
{
  return value == sv.value;
}

SymbolicValue 
SymbolicValue::unknown_value (int size)
{
  static int vid = 0;
  std::ostringstream oss;
  oss <<  "unkval_" << vid++;
  Expr *var = Variable::create (oss.str (), 0, size);
  
  SymbolicValue result (var);
  var->deref ();

  return result;
}


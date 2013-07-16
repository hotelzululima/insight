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
#include <kernel/expressions/exprutils.hh>
#include "SymbolicMemory.hh"

SymbolicMemory::SymbolicMemory (const ConcreteMemory *base) 
  : Memory<ConcreteAddress, SymbolicValue> (), RegisterMap<SymbolicValue> (),
    base (base), memory ()
{
  base->get_address_range (minaddr, maxaddr);
}

SymbolicMemory::~SymbolicMemory()
{
}

SymbolicValue 
SymbolicMemory::get (const ConcreteAddress &a, int size_in_bytes, 
		     Architecture::endianness_t e) const
  throw (UndefinedValueException)
{
  Expr *result = NULL;

  assert (size_in_bytes > 0);
  
  ConcreteAddress addr (a);

  for (int i = 0; i < size_in_bytes && (i == 0 || result != NULL); i++, addr++)
    {
      Expr *byte = NULL;
      MemoryMap::const_iterator ci = memory.find (addr.get_address ());
      if (ci != memory.end ())
	byte = ci->second.get_Expr ()->ref ();
      else if (base->is_defined (addr))
	{
	  ConcreteValue v = base->get (addr, 1, e);
	  byte = Constant::create (v.get (), 0, 8);
	}

      if (byte != NULL)
	{
	  assert (byte->get_bv_size () == 8);
	  if (result == NULL)
	    result = byte;
	  else
	    {
	      Expr *l;
	      Expr *r;

	      if (e == Architecture::LittleEndian)
		{
		  l = byte;
		  r = result;
		}
	      else
		{
		  l = result; 
		  r = byte;
		}
	      assert (l->get_bv_size () + r->get_bv_size () == 8 * (i + 1));
	      result = BinaryApp::create (BV_OP_CONCAT, l, r, 0, 8 * (i + 1));
	    }
	}
      else if (result != NULL)
	{
	  result->deref ();
	  result = NULL;
	}
    }

  if (result == NULL)
    throw UndefinedValueException ("at address " + addr.to_string ());
  
  SymbolicValue res (result);
  result->deref ();

  return res;
}

void 
SymbolicMemory::put (const ConcreteAddress &a, const SymbolicValue &v, 
		     Architecture::endianness_t e)
{
  int offset, inc;
  int size = v.get_size ();
  assert (size > 0 && size % 8 == 0);

  size /= 8;

  if (e == Architecture::LittleEndian)
    {
      offset = 0;
      inc = 8;
    }
  else
    {
      offset = v.get_size () - 8;
      inc = -8;
    }

  const Expr *value = v.get_Expr ();
  address_t addr = a.get_address ();

  for (int i = 0; i < size; i++, addr++, offset += inc)
    {
      Constant *e_off = Constant::create (offset, 0, BV_DEFAULT_SIZE);
      Constant *e_size = Constant::create (8, 0, BV_DEFAULT_SIZE);
      Expr *tmp  = 
	TernaryApp::create (BV_OP_EXTRACT, value->ref (), e_off, e_size, 0, 8);
      exprutils::simplify (&tmp);

      memory[addr] = SymbolicValue (tmp);
      tmp->deref ();
    }

  if (addr < minaddr)
    minaddr = addr;
  if (maxaddr < addr)
    maxaddr = addr;
}

bool 
SymbolicMemory::is_defined (const ConcreteAddress &a) const
{
  return ((memory.find (a.get_address ()) != memory.end ()) ||
	  base->is_defined (a));
}


SymbolicMemory *
SymbolicMemory::clone () const
{
  SymbolicMemory *result = new SymbolicMemory (base);
  
  for (const_reg_iterator i = regs_begin (); i != regs_end (); i++) {
    result->put (i->first, i->second);
  }

  for (MemoryMap::const_iterator i = memory.begin (); i != memory.end (); i++) {
    result->memory[i->first] = i->second;
  }
  result->minaddr = minaddr;
  result->maxaddr = maxaddr;

  return result;
}

bool 
SymbolicMemory::is_defined (const RegisterDesc *rdesc) const
{
  return (RegisterMap<SymbolicValue>::is_defined (rdesc) ||
	  base->is_defined (rdesc));  
}

SymbolicValue 
SymbolicMemory::get (const RegisterDesc *rdesc) const 
  throw (UndefinedValueException)
{
  SymbolicValue result;

  if (RegisterMap<SymbolicValue>::is_defined (rdesc))
    result = RegisterMap<SymbolicValue>::get (rdesc);
  else
    {
      ConcreteValue cv (base->get (rdesc));
      Expr *ev = Constant::create (cv.get (), 0, cv.get_size ());
      result = SymbolicValue (ev);
      ev->deref ();
    }

  return result;
}

void 
SymbolicMemory::output_text (std::ostream &out) const
{
  out << "MemoryDump: " << std::endl;
  for (MemoryMap::const_iterator i = memory.begin (); i != memory.end (); i++) {
    out << std::hex << i->first << " " << i->second << std::endl;
  }
  
  out << "Registers: " << std::endl;
  RegisterMap<SymbolicValue>::output_text (out);  
}

bool 
SymbolicMemory::equals (const SymbolicMemory &mem) const
{
  if (memory.size () != mem.memory.size () ||
      this->RegisterMap<SymbolicValue>::size () != mem.RegisterMap<SymbolicValue>::size ())
    return false;

  if (base != mem.base)
    return false;

  try 
    {
      for (MemoryMap::const_iterator i = memory.begin (); i != memory.end (); 
	   i++) 
	{
	  SymbolicValue v = mem.get (i->first, 1, Architecture::LittleEndian);
	  if (! i->second.equals (v))
	    return false;
	}

      for (RegisterMap<SymbolicValue>::const_reg_iterator i = regs_begin ();
	   i != regs_end (); i++) 
	{
	  SymbolicValue v = mem.get (i->first);
	  if (! i->second.equals (v))
	    return false;
	}
    } 
  catch (UndefinedValueException&)
    {
      return false;
    }
  return true;
}

std::size_t 
SymbolicMemory::hashcode () const
{
  std::size_t result = 0;
  
  for (MemoryMap::const_iterator i = memory.begin (); i != memory.end (); i++) {
    result = ((result << 3) + 19 * i->first +
	      177 * (intptr_t) i->second.get_Expr ());
  }

  for (RegisterMap<SymbolicValue>::const_reg_iterator i = regs_begin ();
       i != regs_end (); i++) {
    result = ((result << 3) + 19 * (intptr_t) i->first +
	      177 * (intptr_t) i->second.get_Expr ());
  }

  return result;
}

void 
SymbolicMemory::get_address_range (address_t &min, address_t &max) const
{
  min = minaddr;
  max = maxaddr;
}

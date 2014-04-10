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

#include <domains/sets/SetsMemory.hh>

#include <domains/common/ConcreteAddressMemory.hh>
#include <domains/sets/SetsAddress.hh>
#include <domains/sets/SetsValue.hh>
#include <kernel/Memory.hh>

using namespace std;

SetsMemory::SetsMemory() :
  Memory<SetsAddress, SetsValue>(),
  RegisterMap<SetsValue>(),
  mem()
{}

SetsMemory::SetsMemory(const SetsMemory &other) :
  Memory<SetsAddress, SetsValue>(other),
  RegisterMap<SetsValue>(other),
  mem(other.mem)
{}

SetsMemory::~SetsMemory() {}

SetsValue
SetsMemory::get(const SetsAddress &a, int size, 
		Architecture::endianness_t e) const 
  throw (UndefinedValueException)
{

  SetsValue the_value(size * 8);

  if (a.get().is_any())
    {
      logs::warning << "SetsMemory::get: found address with top value" 
		   << std::endl;
      the_value.any();
      return the_value;
    }

  std::list<ConcreteValue> addr = a.get().get_values().getValue();
  for (std::list<ConcreteValue>::iterator v = addr.begin();
       v != addr.end();
       v++)
    the_value.add(mem.get(ConcreteAddress(*v), size, e));

  return the_value;
}

bool
SetsMemory::add_to_cells(const SetsAddress &a, const SetsValue &v, 
			 Architecture::endianness_t e)
{

  if (a.get().is_any())
    {
      logs::warning << "SetsMemory::put: found address with top value" 
		   << std::endl;
      // TODO : ajouter v a toutes les cellules de la memoire ?  pas
      // vraiment: ce serait un peu faux: on ajouterait seulement aux
      // cellules figurant dans la hash_table. En fait, c'est à toute
      // cellule de la memoire. Peut-etre qu'il faut un set global qui
      // donne certaine valeurs comme possible pour toute case memoire.
      return true;
    }

  bool modified = false;
  std::list<ConcreteValue> addrs = a.get().get_values().getValue();
  for (std::list<ConcreteValue>::iterator a = addrs.begin();
       a != addrs.end();
       a++)
    {
      ConcreteAddress addr(*a);
      SetsValue new_v =
        mem.get(addr, v.get_size() / 8, e);
      if (new_v.add(v)) modified = true;
      mem.put(addr, new_v, e);
    }

  return modified;
}

void
SetsMemory::put(const SetsAddress &a, const SetsValue &v, 
		Architecture::endianness_t e)
{
  try
    {
      /* if the address is determined,i.e, there is only one possible
         concrete value for it, then one just replaces the value */
      ConcreteAddress addr(a.get().extract_value().getValue());
      mem.put(addr, v, e);
    }
  catch (OptionNoValueExc &)
    {
      /* if several addresses are possible, then just add the possible values */
      add_to_cells(a, v, e);
    }
}

bool
SetsMemory::is_defined(const SetsAddress &a) const
{

  if (a.get().is_any())
    {
      logs::warning << "SetsMemory::is_memcell_defined: found address with "
		   << "top value" << std::endl;
      return !mem.is_empty();
    }

  std::list<ConcreteValue> addr = a.get().get_values().getValue();
  for (std::list<ConcreteValue>::iterator v = addr.begin();
       v != addr.end();
       v++)
    if (mem.is_defined(ConcreteAddress(*v)))
      return true;
  return false;
}

ConcreteAddressMemory<SetsValue>::ValueIterator
SetsMemory::get_value_iterator() const
{
  return ConcreteAddressMemory<SetsValue>::ValueIterator(&mem);
}

bool SetsMemory::merge(const SetsMemory &other)
{

  bool modified = false;
  ConcreteAddressMemory<SetsValue>::ValueIterator mem_cell = other.get_value_iterator();
  while (!mem_cell.end())
    {
      SetsAddress addr(mem_cell.get_address());
      if (add_to_cells(addr, mem_cell.get_value(), mem_cell.get_endianness()))
        modified = true;
      mem_cell++;
    }

  for (const_reg_iterator rv = other.regs_begin(); rv != other.regs_end(); rv++)
    {
      const RegisterDesc *reg = rv->first;
      if (is_defined(reg))
        {
          SetsValue regv = get(reg);
          bool local_modif = regv.add(rv->second);
          modified = modified || local_modif;
          put(reg, regv);
        }
      else
        {
          modified = true;
          put(reg, rv->second);
        }
    }

  return modified;
}

void SetsMemory::clear(ConcreteAddress addr, int size)
{
  SetsValue v(size / 8);
  mem.put(addr, v, Architecture::LittleEndian);  // TODO why LittleEndian?

  // TODO TODO TODO CHECK
}

std::string SetsMemory::pp()
{
  ostringstream oss;
  oss << "delegate memory: " ;
  oss << mem.pp() << endl;
  oss << "[dump:]\n" << mem.dump();
  oss << "\n";
  RegisterMap<SetsValue>::output_text(oss);
  return oss.str();
}

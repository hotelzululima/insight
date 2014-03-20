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

#include <kernel/SymbolTable.hh>

#include <algorithm>
#include <cassert>
#include <iomanip>
#include <vector>

using namespace std;

SymbolTable::SymbolTable () : symbmap(), addrmap ()
{
}

SymbolTable::~SymbolTable ()
{
}

SymbolTable *
SymbolTable::clone () const
{
  SymbolTable *result = new SymbolTable ();
  result->merge_with (this);

  return result;
}

size_t
SymbolTable::size () const
{
  return symbmap.size ();
}

bool
SymbolTable::empty () const
{
  return size () == 0;
}

void
SymbolTable::add_symbol (const string &id, address_t a)
{
  assert (symbmap.find (id) == symbmap.end ());

  symbmap[id] = a;
  addrmap[a].push_back (id);
}

void
SymbolTable::merge_with (const SymbolTable *table)
{
  for (const_symbol_iterator i = table->begin_symbols ();
       i != table->end_symbols (); i++)
    add_symbol (i->first, i->second);
}

bool
SymbolTable::has (const string &id) const
{
  return (find (id) != end_symbols ());
}

bool
SymbolTable::has (address_t a) const
{
  return (find (a) != end_addresses ());
}

address_t
SymbolTable::get (const string &id) const
{
  assert (has (id));
  return symbmap.find (id)->second;
}

const std::list<std::string> &
SymbolTable::get (address_t a) const
{
  assert (has (a));
  return addrmap.find (a)->second;
}

void
SymbolTable::output_text (ostream &out) const
{
  vector<address_t> addresses;

  for (const_address_iterator i = begin_addresses (); i != end_addresses ();
       i++)
    addresses.push_back (i->first);
  sort (addresses.begin (), addresses.end ());

  for (vector<address_t>::size_type i = 0; i < addresses.size (); i++)
    {
      address_t a = addresses[i];
      const std::list<std::string> &symbols = addrmap.find (a)->second;

      out << std::hex << std::setw (8) << std::setfill ('0') << a << ':';
      bool first = true;
      for (std::list<std::string>::const_iterator s = symbols.begin ();
	   s != symbols.end (); s++)
	{
	  if (first)
	    first = false;
	  else
	    out << ", ";
	  out << *s;
	}
      out << std::endl;
    }
}

SymbolTable::const_address_iterator
SymbolTable::find (address_t a) const
{
  return addrmap.find (a);
}

SymbolTable::const_symbol_iterator
SymbolTable::find (const string &id) const
{
  return symbmap.find (id);
}

SymbolTable::const_symbol_iterator
SymbolTable::begin_symbols () const
{
  return symbmap.begin ();
}

SymbolTable::const_symbol_iterator
SymbolTable::end_symbols () const
{
  return symbmap.end ();
}

SymbolTable::const_address_iterator
SymbolTable::begin_addresses () const
{
  return addrmap.begin ();
}

SymbolTable::const_address_iterator
SymbolTable::end_addresses () const
{
  return addrmap.end ();
}



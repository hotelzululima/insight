#include <cassert>
#include <vector>
#include <algorithm>
#include <iomanip>
#include "SymbolTable.hh"

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
SymbolTable::add_symbol (const std::string &id, address_t a)
{
  assert (symbmap.find (id) == symbmap.end ());
  assert (addrmap.find (a) == addrmap.end ());

  symbmap[id] = a;
  addrmap[a] = id;
}

void 
SymbolTable::merge_with (const SymbolTable *table)
{
  for (const_symbol_iterator i = table->begin_symbols ();
       i != table->end_symbols (); i++)
    add_symbol (i->first, i->second);
}

bool
SymbolTable::has (const std::string &id) const
{
  return (find (id) != end_symbols ());
}
 
bool
SymbolTable::has (address_t a) const
{
  return (find (a) != end_addresses ());
}

address_t
SymbolTable::get (const std::string &id) const
{
  assert (has (id));
  return symbmap.find (id)->second;
}
 
const std::string &
SymbolTable::get (address_t a) const
{
  assert (has (a));
  return addrmap.find (a)->second;
}

void 
SymbolTable::output_text (std::ostream &out) const
{  
  std::vector<address_t> addresses;

  for (const_address_iterator i = begin_addresses (); i != end_addresses (); 
       i++)
    addresses.push_back (i->first);
  sort (addresses.begin (), addresses.end ());
  
  for (std::vector<address_t>::size_type i = 0; i < addresses.size (); i++)
    {
      address_t a = addresses[i];
      out << std::hex << std::setw (8) << std::setfill ('0') << a << ':' 
	  << addrmap.find (a)->second << std::endl;
    }
}

SymbolTable::const_address_iterator 
SymbolTable::find (address_t a) const
{
  return addrmap.find (a);
}

SymbolTable::const_symbol_iterator 
SymbolTable::find (const std::string &id) const
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



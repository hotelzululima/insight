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
#include "ConfigTable.hh"
#include <cstdlib>
#include <sstream>

using namespace std;

ConfigTable::ConfigTable () : Object (), table ()
{
}

ConfigTable::ConfigTable (const ConfigTable &ct) : Object (ct), table (ct.table)
{
}

ConfigTable::~ConfigTable ()
{
}
  
void
ConfigTable::set (const std::string &name, const std::string &value)
{
  table[name] = value;
}

void
ConfigTable::set (const std::string &name, const char *value)
{
  table[name] = string (value);
}

void 
ConfigTable::set (const std::string &name, int value)
{
  ostringstream oss;

  oss << value;
  set (name, oss.str ());
}

void 
ConfigTable::set (const std::string &name, long value)
{
  ostringstream oss;

  oss << value;
  set (name, oss.str ());
}

void 
ConfigTable::set (const std::string &name, bool value)
{
  set (name, value ? "true" : "false");
}

bool 
ConfigTable::has (const std::string &key) const
{
  return table.find (key) != table.end ();
}

void 
ConfigTable::add (const ConfigTable &other)
{
  for (const_iterator i = other.begin (); i != other.end (); i++)
    set (i->first, i->second);
}

std::string 
ConfigTable::get (const std::string &name, const std::string &def) const
{
  std::string result;
  const_iterator i = table.find (name);

  if (i == table.end ())
    result = def;
  else 
    result = i->second;

  return result;
}

long 
ConfigTable::get_integer (const std::string &name, long def) const
{
  long result;

  if (has (name))
    result = strtoll (get (name).c_str (), NULL, 0);
  else
    result = def;
  
  return result;
}

static bool 
eq_nocase (const string &s1, const string &s2)
{
  string::const_iterator p1 = s1.begin ();
  string::const_iterator p2 = s2.begin ();

  while (p1 != s1.end () && p2 != s2.end () && tolower (*p1) == tolower (*p2))
    {
      p1++;
      p2++;
    }
  return p1 == s1.end () && p2 == s2.end ();
}

bool 
ConfigTable::get_boolean (const std::string &name, bool def) const
{
  bool result;

  if (has (name))
    {
      string val = get (name);
      result = ((eq_nocase (val, "true") || get_integer (name) != 0));
    }
  else
    {
      result = def;
    }
  return result;
}

void 
ConfigTable::save (std::ostream &out) const
{
  for (const_iterator i = table.begin (); i != table.end (); i++)
    out << i->first << " = " << i->second << endl;
}

static void
remove_useless_whitespaces (string &s)
{
  string::size_type i;

  for (i = 0; i < s.size () && s[i] == ' '; i++)
    /* empty */;
  if (i == s.size ())
    return;
  s = s.substr (i, string::npos);
  for (i = s.size () - 1; i > 0 && s[i] == ' '; i--)
    /* empty */;
  s = s.substr (0, i + 1);
}

void 
ConfigTable::load (std::istream &in)
{
  while (! in.eof ())
    {
      string line;

      if (getline (in, line) && ! line.empty ())
	{
	  string::size_type i = line.find ('=');
	  if (i == string::npos)
	    {
	      cerr << "warning: bad configuration line '" << line << "'." 
		   << endl;
	      continue;
	    }
	  string name = line.substr (0, i - 1);
	  remove_useless_whitespaces (name);
	  string value = line.substr (i + 1, string::npos);
	  remove_useless_whitespaces (value);

	  set (name, value);
	}      
    }
}

ConfigTable::Store::const_iterator 
ConfigTable::begin () const
{
  return table.begin ();
}

ConfigTable::Store::const_iterator 
ConfigTable::end () const
{
  return table.end ();
}

void 
ConfigTable::output_text (std::ostream &out) const
{
  save (out);
}


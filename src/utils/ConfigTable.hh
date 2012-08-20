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
#ifndef UTILS_CONFIGTABLE_HH
# define UTILS_CONFIGTABLE_HH

# include <tr1/unordered_map>
# include <string>
# include <iostream>
# include <utils/Object.hh>

class ConfigTable : public Object
{
  typedef std::tr1::unordered_map<std::string, std::string> Store;
public:

  typedef Store::const_iterator const_iterator;

  ConfigTable ();
  ConfigTable (const ConfigTable &ct);

  ~ConfigTable ();
  
  void set (const std::string &name, const std::string &value);
  void set (const std::string &name, const char *value);
  void set (const std::string &name, int value);
  void set (const std::string &name, long long value);
  void set (const std::string &name, bool value);

  bool has (const std::string &name) const;

  void add (const ConfigTable &other);

  std::string get (const std::string &name) const;

  long long get_integer (const std::string &name) const;

  bool get_boolean (const std::string &name) const;

  void save (std::ostream &out) const;

  void load (std::istream &in);
  
  const_iterator begin () const;
  const_iterator end () const;

  void output_text (std::ostream &out) const;

private:
  Store table;
};

#endif /* ! UTILS_CONFIGTABLE_HH */

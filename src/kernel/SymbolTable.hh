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

#ifndef SYMBOLTABLE_HH
# define SYMBOLTABLE_HH

# include <string>

# include <kernel/Architecture.hh>
# include <utils/Object.hh>
# include <utils/unordered11.hh>

class SymbolTable : public Object
{
public:
  typedef std::unordered_map<std::string, address_t> SymbolMap;
  typedef SymbolMap::const_iterator const_symbol_iterator;
  typedef std::unordered_map<address_t, std::list<std::string> > AddressMap;
  typedef AddressMap::const_iterator const_address_iterator;

  SymbolTable ();
  virtual ~SymbolTable ();

  virtual SymbolTable *clone () const;
  virtual size_t size () const;
  virtual bool empty () const;
  virtual void add_symbol (const std::string &id, address_t a);
  virtual void merge_with (const SymbolTable *table);

  virtual bool has (const std::string &id) const;
  virtual bool has (address_t a) const;
  virtual address_t get (const std::string &id) const;
  virtual const std::list<std::string> &get (address_t a) const;
  virtual void output_text (std::ostream &out) const;
  virtual const_address_iterator find (address_t a) const;
  virtual const_symbol_iterator find (const std::string &id) const;

  virtual const_symbol_iterator begin_symbols () const;
  virtual const_symbol_iterator end_symbols () const;
  virtual const_address_iterator begin_addresses () const;
  virtual const_address_iterator end_addresses () const;

protected:
  SymbolMap symbmap;
  AddressMap addrmap;
};

#endif /* ! SYMBOLTABLE_HH */

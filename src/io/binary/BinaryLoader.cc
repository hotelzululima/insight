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

#include "BinaryLoader.hh"

using namespace std;

string BinaryLoader::get_filename() const
{
  return filename;
}

string BinaryLoader::get_format() const
{
  return format;
}

const Architecture * BinaryLoader::get_architecture() const
{
  return architecture;
}

ConcreteAddress BinaryLoader::get_entrypoint() const
{
  return entrypoint;
}

Option<ConcreteAddress>
BinaryLoader::get_symbol_value(const std::string) const {
  return Option<ConcreteAddress>();
}

static string flags_to_string(list<string> flags)
{
  stringstream ss;
  string sep = "";

  for (list<string>::iterator it = flags.begin(); it != flags.end(); it++)
    {
      ss << sep << *it;
      sep = ", ";
    }

  return ss.str();
}

static string sections_to_string(list<BinaryLoader::section_t> sections)
{
  stringstream ss;

  for (list<BinaryLoader::section_t>::iterator it = sections.begin();
       it != sections.end(); it++)
    {
      ss << "   * Label: " << it->label << endl
         << "     + Flags: " << flags_to_string(it->flags) << endl
         << "     + Address: " << hex << it->start << dec << endl
         << "     + Size: " << it->size << endl;
    }

  return ss.str();
}

void BinaryLoader::output_text(ostream &out) const
{
  out << "Loader('" << filename << "') :" << endl
      << " - Format: " << format << endl
      << " - Architecture: " << architecture << endl
      << " - Entry point: 0x" << hex << entrypoint << dec << endl
      << " - Flags: " << flags_to_string(flags) << endl
      << " - Sections: " << endl << sections_to_string(sections);
}

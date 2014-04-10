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

#include <cassert>
#include "MicrocodeArchitecture.hh"

MicrocodeArchitecture::MicrocodeArchitecture (const Architecture *arch)
  : Architecture (arch->get_proc (), arch->get_endian (),
		  arch->get_word_size (), arch->get_address_size ()),
    reference_arch (arch)
{
}

MicrocodeArchitecture::~MicrocodeArchitecture ()
{
}

const Architecture *
MicrocodeArchitecture::get_reference_arch () const
{
  return reference_arch;
}

void
MicrocodeArchitecture::add_tmp_register (const std::string &label, int size)
{
  assert (!reference_arch->has_register (label));

  add_register (label, size);
}

bool
MicrocodeArchitecture::has_tmp_register (const std::string &label) const
{
  return has_register (label);
}

const RegisterDesc *
MicrocodeArchitecture::get_register(const std::string &label) const
{
  if (has_register (label))
    return Architecture::get_register (label);

  return reference_arch->get_register (label);
}

const RegisterSpecs *
MicrocodeArchitecture::get_tmp_registers() const
{
  return get_registers ();
}

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

#include "LoaderFactory.hh"

#include <bfd.h>
#include <string.h>

#include <list>

#include <io/binaryloader/BinutilsBinaryLoader.hh>
#include <io/process/ProcessLoader.hh>

using namespace std;

BinaryLoader * LoaderFactory::get_BinaryLoader(const string filename)
{
  return new BinutilsBinaryLoader(filename);
}

/* Returns a list of locally supported executable file formats */
list<string> *get_Binutils_supported_formats()
{
  const char **targets = bfd_target_list();
  list<string> *formats = new list<string>();

  /* Supported formats: ELF, a.out, PEI, ECOFF, Mach-O, PEF, Raw */
  bool elf_support   = false,
       aout_support  = false,
       pei_support   = false,
       ecoff_support = false,
       macho_support = false,
       pef_support   = false,
       raw_support   = false;

  /* FIXME: Too much code duplication, this should be rewritten!!! */
  for (int i = 0; targets[i] != NULL; i++)
    {
      /* Checking for ELF support */
      if ((!elf_support) && (!strncmp("elf", targets[i], 3)))
	{
	  elf_support = true;
	  formats->push_back(string("elf"));
	}

      /* Checking for a.out support */
      if ((!aout_support) && (!strncmp("a.out", targets[i], 5)))
	{
	  aout_support = true;
	  formats->push_back(string("a.out"));
	}

      /* Checking for PEI support */
      if ((!pei_support) && (!strncmp("pei", targets[i], 3)))
	{
	  pei_support = true;
	  formats->push_back(string("pei"));
	}

      /* Checking for ECOFF support */
      if ((!ecoff_support) && (!strncmp("ecoff", targets[i], 5)))
	{
	  ecoff_support = true;
	  formats->push_back(string("ecoff"));
	}

      /* Checking for Mach-O support */
      if ((!macho_support) && (!strncmp("mach-o", targets[i], 6)))
	{
	  macho_support = true;
	  formats->push_back(string("mach-o"));
	}

      /* Checking for PEF support */
      if ((!pef_support) && (!strncmp("pef", targets[i], 3)))
	{
	  pef_support = true;
	  formats->push_back(string("pef"));
	}

      /* Checking for Raw support */
      if ((!raw_support) && (!strncmp("binary", targets[i], 6)))
	{
	  raw_support = true;
	  formats->push_back(string("raw"));
	}
    }

  return formats;
}

list<string> * LoaderFactory::get_BinaryLoader_supported_formats()
{
  return get_Binutils_supported_formats();
}

ProcessLoader * LoaderFactory::get_ProcessLoader(const pid_t)
{
  return NULL;
}

MicrocodeLoader * LoaderFactory::get_MicrocodeLoader()
{
  return new MicrocodeLoader();
}

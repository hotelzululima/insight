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

#include <io/binaryloader/BinutilsBinaryLoader.hh>

#include <cstdlib>
#include <sstream>

#include <domains/concrete/ConcreteMemory.hh>

using namespace std;

/********************* Helper Functions ***********************/

/* We do not care yet about the executable format anyway... */
string BinutilsBinaryLoader::get_BFD_format() const
{
  return string(abfd->xvec->name);
}

/* Translating BFD architecture labels into Insight's ones */
const Architecture * BinutilsBinaryLoader::get_BFD_architecture() const
{
  Architecture::processor_t _processor;
  Architecture::endianness_t _endianness;
  string bfd_architecture = bfd_printable_name(abfd);

  /* Setting architecture */
  if (bfd_architecture == "i386")
    _processor = Architecture::X86_32;

  else if (bfd_architecture == "arm")
    _processor = Architecture::ARM;

  else  if (bfd_architecture == "i386:x86-64")
    _processor = Architecture::X86_64;

  else
    _processor = Architecture::Unknown;

  /* Setting endianness */
  if (bfd_big_endian(abfd))
    _endianness = Architecture::BigEndian;

  else if (bfd_little_endian(abfd))
    _endianness = Architecture::LittleEndian;

  else
    _endianness = Architecture::LittleEndian;

  return Architecture::getArchitecture(_processor, _endianness);
}

/********************* BinutilsBinaryLoader Methods ***********************/

BinutilsBinaryLoader::BinutilsBinaryLoader(const string filename)
{
  bfd *bfd_file; /* BFD file handler */

  /* Initialization of libbfd framework */
  bfd_init();
  bfd_set_default_target("elf32-i386");

  /* Opening of the given file 'filename' */
  bfd_file = bfd_openr(filename.c_str(), NULL);

  if (bfd_file == NULL)
    throw BinaryFileNotFound(filename);

  /* If the file is an archive, throw an exception and stop */
  if (bfd_check_format(bfd_file, bfd_archive))
    throw UnknownBinaryFormat(filename);

  /* Fill the BFD structure with the data of the object file */
  if (! bfd_check_format(bfd_file, bfd_object))
    throw UnknownBinaryFormat(filename);

  /* Initializing the 'BinaryLoader' object */
  this->filename = filename;
  this->abfd = bfd_file;
  this->format = get_BFD_format();
  this->architecture = get_BFD_architecture();

  /* Check if the binary file is executable */
  if (!(bfd_file->flags & EXEC_P) && false)
    {
      throw UnknownBinaryType(filename);
    }

  this->entrypoint = ConcreteAddress(bfd_file->start_address);

  /* Setting binary option flags */
  for (size_t i = 0; bfd_flags[i].value != 0; i++)
    if (bfd_file->flags & bfd_flags[i].value)
      {
        this->flags.push_back(string(bfd_flags[i].label));
      }

  for (struct bfd_section *bfd_section = bfd_file->sections;
       bfd_section != NULL;
       bfd_section = bfd_section->next)
    {
      BinaryLoader::section_t section;

      /* Setting section label */
      section.label = string(bfd_get_section_name(bfd_file, bfd_section));

      /* Setting section start address */
      section.start = ConcreteAddress(bfd_section->vma);

      /* Setting section option flags */
      for (size_t i = 0; bfd_sec_flags[i].value != 0; i++)
	if (bfd_section->flags & bfd_sec_flags[i].value)
	  {
		section.flags.push_back(bfd_sec_flags[i].label);
	  }

      /* Setting section size */
      unsigned int opb = bfd_octets_per_byte(bfd_file);
      bfd_size_type datasize = bfd_get_section_size(bfd_section);
      section.size = (size_t) datasize / opb;

      /* Pushing the section to the loader */
      this->sections.push_back(section);
    }
}

BinutilsBinaryLoader::~BinutilsBinaryLoader()
{
  /* Cleaning properly the BFD data-structures */
  bfd_close(abfd);
}

ConcreteMemory *
BinutilsBinaryLoader::get_memory() const
{
  ConcreteMemory * memory = new ConcreteMemory ();

  /* Loading all sections in memory */
  for (struct bfd_section *bfd_section = abfd->sections;
       bfd_section != NULL;
       bfd_section = bfd_section->next)
    {
      /* Setting section start address */
      ConcreteAddress start(bfd_section->vma);

      /* Setting section size */
      unsigned int opb = bfd_octets_per_byte(abfd);
      bfd_size_type datasize = bfd_get_section_size(bfd_section);
      size_t size = (size_t) datasize / opb;

      /* Getting section data content */
      bfd_byte *data = (bfd_byte *) malloc(datasize);
      bfd_get_section_contents(abfd, bfd_section, data, 0, datasize);

      /* Load section data in memory */
      unsigned char *data_start = (unsigned char *) data;
      ConcreteAddress current(start);

      for (unsigned char *ptr = data_start;
           ((size_t)(ptr - data_start)) < size; ptr++, current++)
        {
	  ConcreteValue val (8, *ptr);
          /* Endianness is irrelevant for 8 bits, choose the best */
	  if (memory->is_defined (current))
	    {
	      ConcreteValue v = memory->get (current, 1,
					     Architecture::BigEndian);
	      if (! (v == val))
		Log::warningln ("address " + current.to_string()
				+ " is reassigned :"
				+ v.to_string() + " -> " + val.to_string(), 2);
	    }
          memory->put(current, ConcreteValue(8, *ptr), Architecture::BigEndian);
        }

      /* Cleaning temporary data storage */
      free(data);
    }

  return memory;
}

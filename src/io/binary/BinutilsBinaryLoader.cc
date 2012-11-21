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

#include "BinutilsBinaryLoader.hh"

#include <cstdlib>
#include <sstream>

#include <unistd.h>

#include <utils/logs.hh>
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
    throw BinaryLoader::BinaryFileNotFound(filename);

  /* If the file is an archive, throw an exception and stop */
  if (bfd_check_format(bfd_file, bfd_archive))
    throw BinaryLoader::UnknownBinaryFormat(filename);

  /* Fill the BFD structure with the data of the object file */
  if (! bfd_check_format(bfd_file, bfd_object))
    throw BinaryLoader::UnknownBinaryFormat(filename);

  /* Initializing the 'BinaryLoader' object */
  this->filename = filename;
  this->abfd = bfd_file;
  this->format = get_BFD_format();
  this->architecture = get_BFD_architecture();

  /* Check if the binary file is executable */
  if (!(bfd_file->flags & EXEC_P) && false)
    {
      throw BinaryLoader::UnknownBinaryType(filename);
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

  /* Read symbols */
  size_t ssyms = bfd_get_symtab_upper_bound(bfd_file);
  if (ssyms > 0) {
    asymbol **syms = (asymbol **) operator new (ssyms);
    long nsyms = bfd_canonicalize_symtab(bfd_file, syms);

    for (long i = 0; i < nsyms; i++) {
      symbols[string(bfd_asymbol_name(syms[i]))] =
	ConcreteAddress(bfd_asymbol_value(syms[i]));
      symbols_addresses[bfd_asymbol_value(syms[i])] = 
	string(bfd_asymbol_name(syms[i]));
    }

    delete syms;
  }
}

BinutilsBinaryLoader::~BinutilsBinaryLoader()
{
  /* Cleaning properly the BFD data-structures */
  bfd_close(abfd);
}

void
BinutilsBinaryLoader::fill_memory_from_sections(ConcreteMemory *memory) const {
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
		logs::warning << "address " << current.to_string()
			     << " is reassigned :"
			     << v.to_string() << " -> " << val.to_string()
			     << std::endl;
	    }
          memory->put(current, ConcreteValue(8, *ptr), Architecture::BigEndian);
        }

      /* Cleaning temporary data storage */
      free(data);
    }
}


/*
 * Ugly hack: this data structure lies in the sources of the binutils,
 * in include/elf/internal.h However this file is not installed by the
 * binutils, and the ELF Phdrs copied by bfd_get_elf_phdrs() obey this
 * structure format.
 *
 * We check that the size returned by bfd_get_elf_phdr_upper_bound()
 * is a multiple of the size of this structure, which is doubly wrong
 * but should prevent obvious mismatches.
 */
struct elf_internal_phdr_from_bfd {
  unsigned long	p_type;
  unsigned long	p_flags;
  bfd_vma p_offset;
  bfd_vma p_vaddr;
  bfd_vma p_paddr;
  bfd_vma p_filesz;
  bfd_vma p_memsz;
  bfd_vma p_align;
};

int
BinutilsBinaryLoader::fill_memory_from_ELF_Phdrs(ConcreteMemory *memory) const {
  long phdr_size = bfd_get_elf_phdr_upper_bound(abfd);
  struct elf_internal_phdr_from_bfd *phdrs;
  int nphdrs;
  int r = 0;

  if (phdr_size == -1 ||
      phdr_size % sizeof (struct elf_internal_phdr_from_bfd) != 0)
    return -1;

  phdrs = (struct elf_internal_phdr_from_bfd *) malloc(phdr_size);
  if (phdrs == NULL)
    return -1;

  nphdrs = bfd_get_elf_phdrs(abfd, phdrs);
  if (nphdrs == -1)
    goto fail;

  for (int hdr = 0; hdr < nphdrs; hdr++) {
    size_t size = phdrs[hdr].p_filesz;
    unsigned char *data = (unsigned char *) malloc(size);
    if (data == NULL)
      goto fail;

    if (bfd_seek(abfd, phdrs[hdr].p_offset, SEEK_SET) == -1) {
      free(data);
      goto fail;
    }

    if (bfd_bread(data, size, abfd) != size) {
      free(data);
      goto fail;
    }

    for (size_t i = 0; i < size; i++) {
      ConcreteAddress addr(phdrs[hdr].p_vaddr + i);
      ConcreteValue val(8, data[i]);

      memory->put(addr, val, Architecture::BigEndian);
    }

    free(data);
  }

  if (0) {
  fail:
    r = -1;
  }

  free(phdrs);
  return r;
}

ConcreteMemory *
BinutilsBinaryLoader::get_memory() const
{
  ConcreteMemory * memory = new ConcreteMemory ();

  /* Prefer reading the ELF Phdr information because it's the authoritative
     information for ELF executables */
  if (bfd_get_flavour(abfd) == bfd_target_elf_flavour && abfd->flags & EXEC_P) {
    if (fill_memory_from_ELF_Phdrs(memory) != -1)
      return memory;
    else
      logs::warning << "Couldn't use ELF Program headers, using sections";
  }

  fill_memory_from_sections(memory);

  return memory;
}

Option<ConcreteAddress>
BinutilsBinaryLoader::get_symbol_value(const std::string s) const {
  tr1::unordered_map<string, ConcreteAddress>::const_iterator it;

  it = symbols.find(s);
  return it == symbols.end()?
    Option<ConcreteAddress>() :
    Option<ConcreteAddress>(it->second);
}

Option<string> 
BinutilsBinaryLoader::get_symbol_name (const address_t a) const
{
  tr1::unordered_map<address_t, string>::const_iterator it;
  Option<string> result;

  it = symbols_addresses.find (a);
  if (it != symbols_addresses.end ()) 
    result = Option<string>(it->second);

  return result;
}

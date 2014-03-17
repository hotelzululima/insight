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
#include "BinutilsBinaryLoader.hh"

#include <cstdlib>
#include <sstream>

#include <unistd.h>

#include <utils/logs.hh>
#include <domains/concrete/ConcreteMemory.hh>
#include "BinutilsStubFactory.hh"

using namespace std;

/********************* Helper Functions ***********************/

/* We do not care yet about the executable format anyway... */
string BinutilsBinaryLoader::get_BFD_format() const
{
  return string(abfd->xvec->name);
}

/* Translating BFD architecture labels into Insight's ones */
const Architecture *
BinutilsBinaryLoader::compute_BFD_architecture(const string machine,
				   Architecture::endianness_t endianness) const
{
  Architecture::processor_t _processor;
  Architecture::endianness_t _endianness;
  string bfd_architecture = machine == ""? bfd_printable_name(abfd) : machine;

  /* Setting architecture */

  if (bfd_architecture.find("x86-64") != string::npos)
    _processor = Architecture::X86_64;

  else if (bfd_architecture.find("i386") != string::npos)
    _processor = Architecture::X86_32;

  else if (bfd_architecture.find("arm") != string::npos)
    _processor = Architecture::ARM;

  else if (bfd_architecture.find("msp430") != string::npos)
    _processor = Architecture::MSP430;

  else if (bfd_architecture.find("sparc") != string::npos)
    _processor = Architecture::SPARC;

  else
    _processor = Architecture::Unknown;

  /* Setting endianness */
  if (endianness == Architecture::BigEndian || bfd_big_endian(abfd))
    _endianness = Architecture::BigEndian;

  else if (endianness == Architecture::LittleEndian || bfd_little_endian(abfd))
    _endianness = Architecture::LittleEndian;

  else
    _endianness = Architecture::UnknownEndian;

  return Architecture::getArchitecture(_processor, _endianness);
}

/********************* BinutilsBinaryLoader Methods ***********************/

BinutilsBinaryLoader::BinutilsBinaryLoader(const string &filename,
					   const string &target,
					   const string &machine,
					   Architecture::endianness_t endianness)
{
  bfd *bfd_file; /* BFD file handler */

  /* Initialization of libbfd framework */
  bfd_init();

  /* Opening of the given file 'filename' */
  bfd_file = bfd_openr(filename.c_str(), target == ""? NULL : target.c_str());

  if (bfd_file == NULL)
    {
      if (bfd_get_error () == bfd_error_invalid_target)
	throw BinaryLoader::UnknownBinaryFormat (target);
      throw BinaryLoader::BinaryFileNotFound(filename);
    }

  /* If the file is an archive, throw an exception and stop */
  if (bfd_check_format(bfd_file, bfd_archive))
    throw BinaryLoader::UnknownBinaryFormat(filename);

  /* Fill the BFD structure with the data of the object file */
  /* TODO: We must be able to extract all object files from an archive */
  if (! bfd_check_format(bfd_file, bfd_object) &&
      ! bfd_check_format(bfd_file, bfd_core))
    throw BinaryLoader::UnknownBinaryFormat(filename);

  /* Initializing the 'BinaryLoader' object */
  this->filename = filename;
  this->abfd = bfd_file;
  this->format = get_BFD_format();
  this->architecture = compute_BFD_architecture(machine, endianness);

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
}

BinutilsBinaryLoader::~BinutilsBinaryLoader()
{
  /* Cleaning properly the BFD data-structures */
  bfd_close(abfd);
}

void
BinutilsBinaryLoader::fill_memory_from_sections (ConcreteMemory *memory) const {

  for (struct bfd_section *bfd_section = abfd->sections;
       bfd_section != NULL;
       bfd_section = bfd_section->next)
    {


      if(((bfd_section->flags & (SEC_DATA|SEC_CODE)) == 0))
	{
	  logs::warning << "ignoring section " 
			<< bfd_section->name
			<<" with bad flag." << hex << bfd_section->flags << endl;
	  continue;
	}
      logs::warning << hex <<  bfd_section->flags  << " "
		    << bfd_section->name 
		    << " " << bfd_get_reloc_upper_bound (abfd, bfd_section)
		    << endl;

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
	      if (! v.equals (val))
		logs::warning << "address " << current.to_string()
			     << " is reassigned :"
			     << v.to_string() << " -> " << val.to_string()
			     << endl;
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

    for (size_t i = 0; i < phdrs[hdr].p_memsz; i++) {
      ConcreteAddress addr(phdrs[hdr].p_vaddr + i);
      ConcreteValue val(8, i < size? data[i] : 0);

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

bool 
BinutilsBinaryLoader::load_symbol_table (SymbolTable *table) const
{
  /* Read symbols */
  size_t ssyms = bfd_get_symtab_upper_bound(abfd);
  bool result = (ssyms > 0);

  if (ssyms > 0) 
    {
      asymbol **syms = (asymbol **) operator new (ssyms);
      long nsyms = bfd_canonicalize_symtab(abfd, syms);

      for (long i = 0; i < nsyms; i++) 
	{
	  if ((syms[i]->flags & BSF_FUNCTION) == 0)
	    continue;

	  string name = bfd_asymbol_name (syms[i]);
	  address_t addr = bfd_asymbol_value(syms[i]);
	  if (table->has (name) && table->get (name) != addr)
	    logs::error << "error: symbol '" << name << "' already defined "
			<< "with a different value." << std::endl;
	  else
	    table->add_symbol (name, addr);
	}
      delete syms;
    }
  return result;
}

bool 
BinutilsBinaryLoader::load_memory (ConcreteMemory *memory) const
{
  /* Prefer reading the ELF Phdr information because it's the authoritative
     information for ELF executables */
  if (bfd_get_flavour(abfd) == bfd_target_elf_flavour && abfd->flags & EXEC_P) {
    if (fill_memory_from_ELF_Phdrs(memory) != -1)
      return true;
    else
      logs::warning << "Couldn't use ELF Program headers, using sections";
  }

  fill_memory_from_sections(memory);

  return true;
}

StubFactory *
BinutilsBinaryLoader::get_StubFactory () const 
{
  StubFactory *result = NULL;
  const Architecture *arch = get_architecture ();

  if (bfd_get_flavour(abfd) == bfd_target_elf_flavour)
    {
      if (arch->get_endian () == Architecture::LittleEndian &&
	  arch->get_proc () == Architecture::X86_32)
	result = BinutilsStubFactory::create_ELF_x86_32_StubFactory (abfd);
    }

  return result;
}

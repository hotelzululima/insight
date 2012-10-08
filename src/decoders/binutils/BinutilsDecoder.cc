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

#if HAVE_CONFIG_H
#include "config.h"
#endif

#include <cstdarg>
#include <cstdlib>

#include <vector>
#include <utility>
#include <cassert>

#include <kernel/annotations/AsmAnnotation.hh>
#include "x86-32/x86_32_decoder.hh"
#include "arm/arm_decoder.hh"

#include "BinutilsDecoder.hh"

using namespace std;

/* A few magic numbers coming from objdump code */
#define INSTR_MAX_SIZE 32
#define DEFAULT_SKIP_ZEROES 8
#define DEFAULT_SKIP_ZEROES_AT_END 3

/* Custom 'sprintf()' function for our decoders */
static int s_binutils_sprintf(stringstream *stream, const char *format, ...);

/* Custom 'read()' function for our decoders */
static int s_binutils_read_memory(bfd_vma memaddr,
                       bfd_byte *myaddr,
                       unsigned int length,
                       struct disassemble_info *info);

/* Custom 'print_address()' function for our decoders */
static void s_binutils_print_address(bfd_vma, struct disassemble_info *);

/* This function return a new _fake_ BFD structure. */
bfd* new_bfd(void)
{
  bfd *nbfd = new bfd;
  if (nbfd == NULL)
    throw (runtime_error("out of memory"));

  nbfd->id = 0;
  nbfd->xvec = new bfd_target;
  nbfd->memory = NULL;
  nbfd->arch_info = NULL;
  nbfd->direction = no_direction;
  nbfd->iostream = NULL;
  nbfd->where = 0;
  if (!bfd_hash_table_init_n (& nbfd->section_htab, NULL, sizeof (void*), 251))
    throw (runtime_error("out of memory"));

  nbfd->sections = NULL;
  nbfd->section_last = NULL;
  nbfd->format = bfd_unknown;
  nbfd->my_archive = NULL;
  nbfd->origin = 0;
  nbfd->opened_once = FALSE;
  nbfd->output_has_begun = FALSE;
  nbfd->section_count = 0;
  nbfd->usrdata = NULL;
  nbfd->cacheable = FALSE;
  nbfd->flags = BFD_NO_FLAGS;
  nbfd->mtime_set = FALSE;

  return nbfd;
}

void delete_bfd(bfd* abfd)
{
  bfd_hash_table_free (&abfd->section_htab);
  delete abfd->xvec;
  delete abfd;
}

/* --------------- */

BinutilsDecoder::BinutilsDecoder(MicrocodeArchitecture *arch, 
				 ConcreteMemory *mem)
  : Decoder(arch, mem)
{
  /* Initializing BFD framework */
  bfd_init();
  bfd_set_default_target("elf32-i386");

  bfd *abfd = new_bfd();

  /* Setting fields of BinutilsDecoder */
  this->instr_buffer = new stringstream();

  /* Initialization of the disassembler parameters */
  this->info = new struct disassemble_info;
  init_disassemble_info(this->info,
			this->instr_buffer,
			(fprintf_ftype) s_binutils_sprintf);

  /* Setting endianness */
  if (arch->get_endian () == Architecture::BigEndian)
    this->info->display_endian = this->info->endian = BFD_ENDIAN_BIG;

  else if (arch->get_endian () == Architecture::LittleEndian)
    this->info->display_endian = this->info->endian = BFD_ENDIAN_LITTLE;

  else
    this->info->display_endian = this->info->endian = BFD_ENDIAN_UNKNOWN;

  /* Setting architecture */
  switch (arch->get_proc ())
    {
    case Architecture::X86_32:
      /* Checking support and setting the disassembler for x86-32 */
      if ((abfd->arch_info = bfd_scan_arch("i386"))  == NULL)
	throw Decoder::DecoderUnexpectedError("x86-32 is not supported on your system");
      /* Setting the decoder function for x86-32 */
      this->decoder = &x86_32_decoder_func;
      break;

    case Architecture::ARM:
      /* Checking support and setting the disassembler for arm */
      if ((abfd->arch_info = bfd_scan_arch("arm"))  == NULL)
	throw Decoder::DecoderUnexpectedError("arm is not supported on your system");
      /* Setting the decoder function for arm */
      this->decoder = &arm_decoder_func;
      break;

    default: /* All other architectures are unsupported yet */
      throw Architecture::UnsupportedArch();
    }

  /* Use libopcodes to find a suitable disassembler function */
  this->disassembler_fn = disassembler(abfd);
  if (!this->disassembler_fn)
  {
      /* Shouldn't occur but trying to make it safe anyway */
        throw Decoder::DecoderUnexpectedError("can't find disassembler function");
  }

  /* Setting all parameters of the disassembler info struct */
  this->info->flavour = bfd_target_unknown_flavour;
  this->info->arch = bfd_get_arch(abfd);
  this->info->mach = bfd_get_mach(abfd);
  this->info->disassembler_options = NULL;
  this->info->octets_per_byte = bfd_octets_per_byte(abfd);
  this->info->skip_zeroes = DEFAULT_SKIP_ZEROES;
  this->info->skip_zeroes_at_end = DEFAULT_SKIP_ZEROES_AT_END;
  this->info->disassembler_needs_relocs = FALSE;

  /* Setting the read function */
  this->info->read_memory_func = s_binutils_read_memory;

  /* Setting the print_address function */
  this->info->print_address_func = s_binutils_print_address;

  /* Disabling the symbols tracking */
  this->info->symbols = NULL;
  this->info->num_symbols = 0;
  this->info->symtab_pos = -1;

  /* Allow the target to customize the info structure */
  /* FIXME: Not sure this step is really useful as this is a fake abfd */
  disassemble_init_for_target (this->info);

  /* Setting the application specific information */
  this->info->application_data = this->memory;

  /* Cleaning memory */
  delete_bfd(abfd);
}

/* --------------- */

BinutilsDecoder::~BinutilsDecoder()
{
  delete this->instr_buffer;
  delete this->info;
}

/* --------------- */

ConcreteAddress
BinutilsDecoder::decode(Microcode *mc, const ConcreteAddress &address)
  throw (Decoder::Exception)
{
  assert(memory->is_defined(address));
  ConcreteAddress result = this->next(address);

  if (this->decoder(arch, mc, instr_buffer->str(), address, result))
    {
      MicrocodeNode *node = 
	mc->get_node (MicrocodeAddress (address.get_address ()));
      node->add_annotation (AsmAnnotation::ID,  
			    new AsmAnnotation (instr_buffer->str ()));
    }
  else
    {
      throw Decoder::DecoderUnexpectedError ("syntax error @" + 
					     address.to_string ());
    }

  return result;
}

/* --------------- */

ConcreteAddress
BinutilsDecoder::next(const ConcreteAddress &address)
{
  /* Clearing out the previous decoded instruction */
  this->instr_buffer->str(string());

  /* Initializing the info structure */
  this->info->buffer = NULL;
  this->info->buffer_vma = (bfd_vma) address.get_address ();
  this->info->buffer_length = (bfd_size_type) INSTR_MAX_SIZE;
  this->info->section = NULL;

  /* Get next instruction address */
  size_t instr_size = (*this->disassembler_fn)(this->info->buffer_vma, 
					       this->info);

  return ConcreteAddress(address.get_address () + instr_size);
}


std::string 
BinutilsDecoder::get_instruction (const ConcreteAddress &addr) 
{
  this->next(addr);

  return instr_buffer->str ();
}

/* --------------- */

struct disassemble_info *
BinutilsDecoder::get_disassembler_info()
{
  return this->info;
}

void
BinutilsDecoder::set_disassembler_info(struct disassemble_info *info)
{
  this->info = info;
}

/* --------------- */

/* Sprintf to a stringstream */
static int
s_binutils_sprintf(stringstream *sstream, const char *format, ...)
{
  va_list args;
  size_t buffer_size = 80;
  char *buffer = new char[buffer_size];

  /* Using the stack is way more efficient in term of speed. That is
   * why it first do an attempt to use the stack and if it fail, it
   * fall back to dynamic allocation using an 'extensible buffer'
   * (xbuffer). */
  bool alloc = false;
  char *xbuffer = NULL;

  /* Decoding the format string and getting the c_string */
  va_start(args, format);
  size_t result = vsnprintf(buffer, buffer_size, format, args);
  va_end(args);

  /* If the original string has been truncated getting it right */
  while (result > buffer_size)
    {
      alloc = true;
      buffer_size *= 2;
      char *tmp = (char *) realloc(xbuffer, buffer_size * sizeof(char));

      /* Checking if 'realloc' worked fine */
      if (tmp == NULL)
        {
          free(xbuffer);
	  free (buffer);
          throw Decoder::DecoderUnexpectedError("out of memory");
        }
      else
        {
          xbuffer = tmp;
        }

      /* Trying again... */
      va_start(args, format);
      result = vsnprintf(xbuffer, buffer_size, format, args);
      va_end(args);
    }

  /* Copying the string in the 'instruction' field of the Decoder */
  if (alloc)
    {
      *sstream << xbuffer;
      free(xbuffer);
    }
  else
    {
      *sstream << buffer;
    }
  delete [] (buffer);

  return result;
}

/* Function used to get bytes to disassemble.
 * - memaddr: Address of the stuff to be disassembled,
 * - myaddr: Address to put the bytes in,
 * - length: Number of bytes to read,
 * - info: Pointer the disassembler parameters.
 *
 * Returns an errno value or 0 for success. */
static int
s_binutils_read_memory(bfd_vma memaddr, bfd_byte *myaddr,
		       unsigned int length, struct disassemble_info *info)
{
  unsigned int opb = info->octets_per_byte;
  unsigned int end_addr_offset = length / opb;
  unsigned int max_addr_offset = info->buffer_length / opb;
  /* The original code was this one */
  //  unsigned int octets = (memaddr - info->buffer_vma) * opb;

  /* Checking if the address is out of bounds */
  if (memaddr < info->buffer_vma
      || memaddr - info->buffer_vma > max_addr_offset
      || memaddr - info->buffer_vma + end_addr_offset > max_addr_offset)
    throw Decoder::DecoderUnexpectedError("Out of bound memory address");

  ConcreteMemory *memory = (ConcreteMemory *) info->application_data;

  /* FIXME: It works but I'm extremely doubtful it is really robust or
   * not... The problem comes from the way libopcodes deals with its
   * sliding window on the memory where the instructions to decode
   * lies. And, more precisely, I really didn't understand the usage
   * of the 'octets' variable. If someone can tell me how to
   * strengthen the code here I would be extremely glad to hear it...
   * Anyway, it seems to work as it is now... dodgy, but working...
   * I'm crossing my fingers ! */
  for (unsigned int i = 0; i < length; i++)
    {
      if (memory->is_defined (memaddr + i))
	myaddr[i] = memory->get(memaddr + i, 1, 
				Architecture::LittleEndian).get();
      else
	throw Decoder::DecoderUnexpectedError("Out of bound memory address");
    }

  /* The original code was this one */
  //  memcpy(myaddr, info->buffer + octets, length);

  return 0;
}

static void
s_binutils_print_address(bfd_vma addr, struct disassemble_info *dinfo)
{
  dinfo->fprintf_func(dinfo->stream, "0x%" BFD_VMA_FMT "x", addr);
}

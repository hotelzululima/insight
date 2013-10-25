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

#ifndef IO_BINUTILSBINARYLOADER_HH
#define IO_BINUTILSBINARYLOADER_HH

#include <config.h>

#include <bfd.h>

#include <list>
#include <stdexcept>

#include <tr1/unordered_map>

#include <domains/concrete/ConcreteAddress.hh>
#include <domains/concrete/ConcreteMemory.hh>
#include <io/binary/BinaryLoader.hh>
#include <io/binary/SymbolTable.hh>

/*************** BinutilsBinaryLoader class definition ****************/

/* BinutilsBinaryLoader is based upon the GNU BFD library. */
class BinutilsBinaryLoader : public BinaryLoader
{
public:

  /********************* Libbfd specific flags **************************/
  /** \brief Store a comprehensive string about libbfd flags */
  /* FIXME: Replace it by a t1::unordered_map */
  typedef struct flag
  {
    int value;
    std::string label;
  } flag_t;

  /******************* BinutilsBinaryLoader Exceptions ******************/
  /** \brief Exception thrown when an error occurs at libbfd level */
  class BFDException: public std::runtime_error
  {
  public:
    BFDException(std::string filename) :
      std::runtime_error("'" + filename + "': libbfd error : " +
			 bfd_errmsg(bfd_get_error())) { }
  };

  BinutilsBinaryLoader(const std::string &filename, const std::string &target,
		       const std::string &machine,
		       Architecture::endianness_t endianness);
  virtual ~BinutilsBinaryLoader();

  virtual bool load_symbol_table (SymbolTable *table) const;
  virtual bool load_memory (ConcreteMemory *memory) const;
  virtual StubFactory *get_StubFactory () const;

  /* BinutilsBinaryLoader specific fields and methods */
protected:
  bfd *abfd;

  std::string get_BFD_format() const;
  const Architecture *compute_BFD_architecture(const std::string machine,
			       Architecture::endianness_t endianness) const;
  void fill_memory_from_sections(ConcreteMemory *) const;
  int fill_memory_from_ELF_Phdrs(ConcreteMemory *) const;
};


static BinutilsBinaryLoader::flag_t bfd_flags[] =
    {
      {EXEC_P, "EXEC_P"},
      {DYNAMIC, "DYNAMIC"},
      {WP_TEXT, "WP_TEXT"},
      {D_PAGED, "D_PAGED"},
      {HAS_SYMS, "HAS_SYMS"},
      {HAS_DEBUG, "HAS_DEBUG"},
      {HAS_RELOC, "HAS_RELOC"},
      {HAS_LOCALS, "HAS_LOCALS"},
      {HAS_LINENO, "HAS_LINENO"},
      {HAS_LOAD_PAGE, "HAS_LOAD_PAGE"},
      {BFD_IN_MEMORY, "BFD_IN_MEMORY"},
      {BFD_IS_RELAXABLE, "BFD_IS_RELAXABLE"},
      {BFD_LINKER_CREATED, "BFD_LINKER_CREATED"},
      {BFD_TRADITIONAL_FORMAT, "BFD_TRADITIONAL_FORMAT"},
#ifdef BFD_DETERMINISTIC_OUTPUT
      {BFD_DETERMINISTIC_OUTPUT, "BFD_DETERMINISTIC_OUTPUT"},
#endif
      {0, ""}
    };

  static BinutilsBinaryLoader::flag_t bfd_sec_flags[] =
    {
      {SEC_ALLOC, "ALLOC"},
      {SEC_LOAD, "LOAD"},
      {SEC_RELOC, "RELOC"},
      {SEC_READONLY, "READONLY"},
      {SEC_CODE, "CODE"},
      {SEC_DATA, "DATA"},
      {SEC_ROM, "ROM"},
      {SEC_CONSTRUCTOR, "CONSTRUCTOR"},
      {SEC_HAS_CONTENTS, "HAS_CONTENTS"},
      {SEC_NEVER_LOAD, "NEVER_LOAD"},
      {SEC_THREAD_LOCAL, "THREAD_LOCAL"},
      {SEC_HAS_GOT_REF, "HAS_GOT_REF"},
      {SEC_IS_COMMON, "IS_COMMON"},
      {SEC_DEBUGGING, "DEBUGGING"},
      {SEC_IN_MEMORY, "IN_MEMORY"},
      {SEC_EXCLUDE, "EXCLUDE"},
      {SEC_SORT_ENTRIES, "SORT_ENTRIES"},
      {SEC_LINK_ONCE, "LINK_ONCE"},
      {SEC_LINK_DUPLICATES, "LINK_DUPLICATES"},
      {SEC_LINK_DUPLICATES_DISCARD, "LINK_DUPLICATES_DISCARD"},
      {SEC_LINK_DUPLICATES_ONE_ONLY, "LINK_DUPLICATES_ONE_ONLY"},
      {SEC_LINK_DUPLICATES_SAME_SIZE, "LINK_DUPLICATES_SAME_SIZE"},
      {SEC_LINKER_CREATED, "LINKER_CREATED"},
      {SEC_KEEP, "KEEP"},
      {SEC_SMALL_DATA, "SMALL_DATA"},
      {SEC_MERGE, "MERGE"},
      {SEC_STRINGS, "STRINGS"},
      {SEC_GROUP, "GROUP"},
#ifdef SEC_COFF_NOREAD
      {SEC_COFF_NOREAD, "COFF_NOREAD"},
#endif
      {SEC_COFF_SHARED, "COFF_SHARED"},
      {SEC_COFF_SHARED_LIBRARY, "COFF_SHARED_LIBRARY"},
      {SEC_TIC54X_BLOCK, "TIC54X_BLOCK"},
      {SEC_TIC54X_CLINK, "TIC54X_CLINK"},
      {0, ""}
    };

#endif /* IO_BINUTILSBINARYLOADER_HH */

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

#ifndef IO_BINARYLOADER_HH
#define IO_BINARYLOADER_HH

#include <string>
#include <stdexcept>

#include <utils/Option.hh>
#include <utils/tools.hh>

#include <kernel/Architecture.hh>
#include <domains/concrete/ConcreteAddress.hh>
#include <domains/concrete/ConcreteMemory.hh>
#include <kernel/Microcode.hh>
#include <io/binary/StubFactory.hh>
#include <io/binary/SymbolTable.hh>

/****************** BinaryLoader class definition *********************/

/* Pure abstract class to group all the binary loader implementations.
 * This class is intended to load any executable or library file.
 *
 * As defined in the Loader class, the initialization of a 'Loader' is
 * done through a call to the static method 'getLoader(filename)'
 * which will issue an appropriate Loader for this file.
 */

class BinaryLoader : public Object
{
public:
  /******************** BinaryLoader Exceptions ***********************/
  /** \brief Exception thrown when the executable file is not found */
  class BinaryFileNotFound : public std::runtime_error
  {
  public:
    BinaryFileNotFound(std::string filename) :
      std::runtime_error("'" + filename + "' : Binary file not found") { };
  };

  /** \brief Exception thrown when user has no sufficient rights to
   *  read the file */
  class BinaryPermissionDenied : public std::runtime_error
  {
  public:
    BinaryPermissionDenied(std::string filename) :
      std::runtime_error("'" + filename + "' : Permission denied") { };
  };

  /** \brief Exception thrown when the binary format (ELF, PE, Mach-O)
   *  is not recognized */
  class UnknownBinaryFormat : public std::runtime_error
  {
  public:
    UnknownBinaryFormat(std::string filename) :
      std::runtime_error("'" + filename +
                       "': Binary format not recognized") { };
  };

  /** \brief Exception thrown when the type of the binary file
   *  (executable, static library, dynamic library) is not
   *  recognized */
  class UnknownBinaryType : public std::runtime_error
  {
  public:
    UnknownBinaryType(std::string filename) :
    std::runtime_error("'" + filename +
                       "': Binary type is not recognized") { };
};

  /** \brief Exception thrown when the binary target architecture
   *  (IA-32, MIPS, ARM) is not recognized. */
  class UnknownBinaryArch : public std::runtime_error
  {
  public:
    UnknownBinaryArch(std::string filename) :
      std::runtime_error("'" + filename +
			 "': Binary architecture is not recognized") { };
  };

  /******************** BinaryLoader Fields ***********************/
  /** \brief Data about binary sections within the binary */
  typedef struct section
  {
    std::string label;              /* Section name */
    std::list <std::string> flags;  /* Section option flags */
    ConcreteAddress start;          /* Start address when relocated */
    size_t size;                    /* Section size (in bytes) */
  } section_t;

  /******************** BinaryLoader Methods ***********************/
  virtual ~BinaryLoader() { };

  void output_text(std::ostream &) const;

  std::string get_filename() const;
  std::string get_format() const;

  const Architecture * get_architecture() const;
  ConcreteAddress get_entrypoint() const;

  virtual bool load_symbol_table (SymbolTable *table) const;
  virtual bool load_memory (ConcreteMemory *memory) const;

  virtual StubFactory *get_StubFactory () const = 0;

protected:
  std::string filename;
  std::string format;

  const Architecture * architecture;
  ConcreteAddress entrypoint;

  std::list <std::string> flags;  /* Flags embedded in the binary */
  std::list <section_t> sections; /* Sections embedded in the binary */
};

#endif /* IO_BINARYLOADER_HH */

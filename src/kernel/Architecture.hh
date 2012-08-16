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

#ifndef KERNEL_ARCHITECTURE_HH
#define KERNEL_ARCHITECTURE_HH

#include <inttypes.h>

#include <list>
#include <sstream>
#include <stdexcept>
#include <string>

#include <utils/Object.hh>
#include <utils/tools.hh>

/** \brief Default numeric type for expressions. */
typedef int64_t word_t;

#define BITS_PER_WORD (8 * sizeof (word_t))

/** \brief Unsigned version of the default numeric type for expressions. */
typedef uint64_t uword_t;

/** \brief Numeric type used in constants. */
typedef word_t constant_t;

/** \brief Type to store memory addresses. */
typedef uint32_t address_t;

/** \brief XXX This define should probably be nuked, don't use */
#define NULL_ADDRESS ((address_t) 0)

/** \brief Default size of a data bit vector (32 bits).
 *  XXX should be much less used. */
#define BV_DEFAULT_SIZE 32

/** \brief Store the description of a register.
 *
 *  Store the description of a register. It contains the name of the
 *  memory array we are in (label) and the size of the register. */
class RegisterDesc : public Object
{
public:
  RegisterDesc(int index, const std::string &label, int regsize);
  RegisterDesc(int index, const std::string &label, int regsize,
	       int winoffset, int winsize);

  virtual void output_text(std::ostream &) const;

  virtual int get_index () const;
  virtual int get_register_size () const;
  virtual int get_window_size () const;
  virtual int get_window_offset () const;
  virtual const std::string &get_label () const;
  virtual int hashcode () const;
  virtual bool is_alias () const;

  struct Hash {
    size_t operator()(const RegisterDesc * const &r) const {
      return r->hashcode ();
    }
  };

private:
  int index;
  std::string label;
  int register_size;
  int window_offset;
  int window_size;
};

/** \brief Data structure used to encode the registers. */
typedef std::tr1::unordered_map<std::string,
				RegisterDesc*,
				std::tr1::hash<std::string> > RegisterSpecs;

/** \brief Abstract class storing the full description of an architecture.
 *
 * Architecture is an abstract class to store the description of
 *  an architecture that will be used by the rest of the framework. */
class Architecture : public Object
{
public:
  /** \brief Supported endianness types. */
  typedef enum {
    LittleEndian,
    BigEndian,
    UnknownEndian
  } endianness_t;

  /** \brief Recognized processors types. */
  typedef enum {
    Alpha,
    ARM,
    IA64,
    M68K,
    MIPS,
    PowerPC,
    Sparc,
    X86_32,
    X86_64,
    Unknown
  } processor_t;

public:

  /******************** Architecture Exceptions ***********************/
  /** \brief Exception thrown when a given architecture is not yet
   *  supported by the framework. */
  class UnsupportedArch : public std::runtime_error
  {
  public:
    UnsupportedArch() :
      std::runtime_error(" : Unsupported architecture") { }
  };

  /** \brief Exception thrown when a register is not found in the
   *   Architecture. */
  class RegisterDescNotFound : public std::runtime_error
  {
  public:
    RegisterDescNotFound(const std::string &regname) :
      std::runtime_error(": " + regname + ": register not found") { }
  };

  /** \brief Exception thrown on a read attempt on an undefined memory
   *  cell or register. */
  class UndefinedValue : public std::runtime_error
  {
  public:
    UndefinedValue(const std::string &where) :
      std::runtime_error(": Undefined value at " + where) { }
  };

  /******************** Architecture Methods ***********************/
  virtual ~Architecture();

  static void init ();
  static void terminate ();

  /** Get the specification of an architecture (instruction sets,
   *  endianness, registers, memory word size, ...) given the
   *  processor name and the endianness. This method is can be used
   *  for any architecture. */
  static const Architecture*getArchitecture (const Architecture::processor_t,
					     const Architecture::endianness_t);

  /** Get the specification of an architecture (instruction sets,
   *  endianness, registers, memory word size, ...) given the
   *  processor name. This method can only be used for processors that
   *  can handle one unique endianness (eg. x86). */
  static const Architecture *getArchitecture (const Architecture::processor_t);
  
  /******************** Architecture Fields ***********************/
  /** \brief Processor type */
  processor_t processor;

  /** \brief Endianness of the architecture. */
  endianness_t endianness;

  /** \brief Size of a memory word. */
  int word_size;

  /** \brief Address range of the memory. */
  int address_range;

  /** \brief Returns true if label is the name of a known register */
  bool has_register(const std::string &label) const;

  /** \brief Returns the specification of the 'label' register. */
  const RegisterDesc *get_register(const std::string &label) const;

  /** \brief Returns a pointer to the table of all registers. */
  const RegisterSpecs *get_registers() const;

protected:
  Architecture ();

  /** \brief Add the specification of a register in the list. */
  void add_register (const std::string &name, int regsize);
  void add_register_alias (const std::string &name, const std::string &refname,
			   int size, int offset);

  static Architecture **architectures;

  /** \brief Specification of all the registers of an architecture.
   *
   *  Store all the register descriptions for a given
   *  architecture. Each register description is stored within a
   *  RegisterDesc. There are two types of registers. The regular
   *  registers, and the alias registers. The regular registers are
   *  defined by the name of a memory array (generally its name), a
   *  size and an offset of zero.  The alias registers, are embedded
   *  within a regular register. It is defined by a name of the memory
   *  array, a size and an offset.
   */
  RegisterSpecs * registerspecs;
};

#endif /* KERNEL_ARCHITECTURE_HH */

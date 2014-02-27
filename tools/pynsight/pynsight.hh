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

#ifndef PYNSIGHT_HH
# define PYNSIGHT_HH

# include <list>
# include <Python.h>

# include <kernel/Architecture.hh>
# include <io/binary/BinaryLoader.hh>
# include <utils/ConfigTable.hh>

namespace pynsight {
  class Module {
  public:
    Module (const char *name, bool (*init) (), bool (*terminate) ());
    virtual ~Module () { }
    inline const char *get_name () const { return name; }
    inline bool init () const { return init_cb (); }
    inline bool terminate () const { return terminate_cb (); }

  private:
    const char *name;
    bool (*init_cb) ();
    bool (*terminate_cb) ();
  };
  
  struct Program {
    PyObject_HEAD
    BinaryLoader *loader;
    ConcreteMemory *concrete_memory;
    SymbolTable *symbol_table;
    StubFactory *stubfactory;
  };


  extern PyObject *load_program (const char *filename, const char *target, 
				 const char *mach, 
				 Architecture::endianness_t endianness);

  enum SimulationDomain {
    SIM_SYMBOLIC,
    SIM_CONCRETE
  };

  extern PyObject *start_simulator (Program *P, address_t start_adddr, 
				    SimulationDomain dom);

  inline PyObject *None () { Py_INCREF (Py_None); return Py_None; }

  extern ConfigTable &configTable ();

  extern PyObject *microcode_object (PyObject *parent, const Microcode *mc);

  /* Exceptions & Errors */
# define PYNSIGHT_EXCEPTIONS			\
  PYNSIGHT_EXC(BFDError)			\
  PYNSIGHT_EXC(NotDeterministicBehaviorError)	\
  PYNSIGHT_EXC(UndefinedValueError)		\
  PYNSIGHT_EXC(BreakpointReached)		\
  PYNSIGHT_EXC(SinkNodeReached)			\
  PYNSIGHT_EXC(ConcretizationException)		\
  PYNSIGHT_EXC(JumpToInvalidAddress) 

# define PYNSIGHT_EXC(e) extern PyObject *e;
  PYNSIGHT_EXCEPTIONS
# undef  PYNSIGHT_EXC
}

#endif /* ! PYNSIGHT_HH */

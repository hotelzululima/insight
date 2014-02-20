/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
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
#include <stdexcept>
#include <domains/concrete/ConcreteMemory.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <decoders/binutils/BinutilsDecoder.hh>

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/SymbolTable.hh>
#include <domains/concrete/ConcreteStepper.hh>
#include <domains/symbolic/SymbolicStepper.hh>

#include "gengen.hh"
#include "pynsight.hh"

struct Simulator {
  PyObject_HEAD
  pynsight::Program *prg;  
  pynsight::SimulationSemantics sem;
  ConcreteAddress start;

  Microcode *mc;
  MicrocodeArchitecture *march;

  void *stepper;
  void *currentState;
};

static void
s_Simulator_dealloc (PyObject *p);

static PyTypeObject SimulatorType = {
  PyObject_HEAD_INIT(NULL)
  0,					/*ob_size*/
  "insight.Simulator",			/*tp_name*/
  sizeof (Simulator),		        /*tp_basicsize*/
  0,					/*tp_itemsize*/
  s_Simulator_dealloc,		        /*tp_dealloc*/
  0,					/*tp_print*/
  0,					/*tp_getattr*/
  0,					/*tp_setattr*/
  0,					/*tp_compare*/
  0,					/*tp_repr*/
  0,					/*tp_as_number*/
  0,					/*tp_as_sequence*/
  0,					/*tp_as_mapping*/
  0,					/*tp_hash */
  0,					/*tp_call*/
  0,					/*tp_str*/
  0,					/*tp_getattro*/
  0,					/*tp_setattro*/
  0,					/*tp_as_buffer*/
  Py_TPFLAGS_DEFAULT,			/*tp_flags*/
  "This type represents a program",	/*tp_doc */
  0
};

static PyMethodDef SimulatorMethods[] = {
  { 
    NULL, NULL, 0, NULL 
  }
};

static bool 
s_init () { 
  SimulatorType.tp_methods = SimulatorMethods;
  if (PyType_Ready (&SimulatorType) < 0)
    return false;
  return true;
}

static bool 
s_terminate () {
  return true;
}

static pynsight::Module SIMULATOR (NULL, s_init, s_terminate);

PyObject * 
pynsight::start_simulator (Program *P, address_t start_addr,
			   SimulationSemantics sem)
{
  Simulator *S = PyObject_New (Simulator, &SimulatorType);

  if (S == NULL)
    return NULL;

  PyObject_Init ((PyObject *) S, &SimulatorType);

  S->prg = P;
  Py_INCREF (P);
  S->start = start_addr;
  S->mc = new Microcode ();
  S->march = new MicrocodeArchitecture (P->loader->get_architecture ());
  
  if (sem == pynsight::SIM_SYMBOLIC) 
    {
      SymbolicStepper *st;
      S->stepper = st = new SymbolicStepper (P->concrete_memory, S->march);
      S->currentState = st->get_initial_state (S->start);
    }
  else 
    {
      ConcreteStepper *st;

      assert (sem == pynsight::SIM_CONCRETE);

      S->stepper = st = new ConcreteStepper (P->concrete_memory, S->march);
      S->currentState = st->get_initial_state (S->start);
    }

  return (PyObject *) S;
}

static void
s_Simulator_dealloc (PyObject *obj) {
  Simulator *S = (Simulator *) obj;

  Py_DECREF (S->prg);
  delete S->mc;
  delete S->march;
  S->ob_type->tp_free (S);
}


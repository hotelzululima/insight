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
#include <cassert>
#include <kernel/insight.hh>
#include "pynsight.hh"

struct Exception {
  const char *name;
  PyObject **p_exception;
}; 
static PyMethodDef Error_Methods[] = {
  { NULL, NULL, 0, NULL }
};

PyObject *pynsight::BFDError = NULL;
PyObject *pynsight::NotDeterministicBehaviorError = NULL;
PyObject *pynsight::UndefinedValueError = NULL;

static Exception ALL_EXCEPTIONS[] = {
  { "BFDError", &pynsight::BFDError },
  { "NotDeterministicBehaviorError", 
    &pynsight::NotDeterministicBehaviorError },
  { "UndefinedValueError", 
    &pynsight::UndefinedValueError },
  { NULL, NULL }
};

static bool 
s_init () 
{
  PyObject *pkg = PyImport_ImportModule (PYNSIGHT_PACKAGE);
  PyObject *error_module = Py_InitModule ("error", Error_Methods);
  PyModule_AddObject (pkg, "error", error_module);
  Py_INCREF (error_module);

  for (Exception *e = ALL_EXCEPTIONS; e->name; e++) {
    std::string name ("error.");
    name += e->name;
    PyObject *o = PyErr_NewException ((char *) name.c_str (), NULL, NULL);
    *(e->p_exception) = o;
    Py_INCREF (o);
    PyModule_AddObject (pkg, "error", o);
  }

  Py_DECREF (pkg);

  return true;
}

static bool 
s_terminate () 
{
  return true;
}

static pynsight::Module ERROR ("error", s_init, s_terminate);


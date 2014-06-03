/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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
#include "pynsight.hh"

#include <cassert>
#include <kernel/insight.hh>

static PyObject *
io_load_bfd (PyObject *, PyObject *args, PyObject *kwds) {
  static const char *kwlists[] =
    { "filename", "target", "architecture", "endianness", NULL };
  const char *c_fname;
  const char *c_bfdtarget = "";
  const char *c_architecture = "";
  const char *c_endianness = NULL;

  if (!PyArg_ParseTupleAndKeywords (args, kwds, "s|sss", (char **) kwlists,
				    &c_fname, &c_bfdtarget, &c_architecture,
				    &c_endianness))
    return NULL;

  Architecture::endianness_t endian = Architecture::UnknownEndian;

  if (c_endianness) {
    if (strcmp (c_endianness, "little") == 0) {
      endian = Architecture::LittleEndian;
    } else if (strcmp (c_endianness, "big") == 0) {
      endian = Architecture::BigEndian;
    } else if (strcmp (c_endianness, "unknown") != 0) {
      PyErr_SetString (PyExc_ValueError, "invalid endianness.");
      return NULL;
    }
  }

  return pynsight::load_program (c_fname, c_bfdtarget, c_architecture, endian);
}

static PyMethodDef IO_Methods[] = {
  { "load_bfd", (PyCFunction) io_load_bfd, METH_VARARGS|METH_KEYWORDS,
    "Load a file with the BFD library" },
  { NULL, NULL, 0, NULL }
};

static bool
s_init () {
  PyObject *pkg = PyImport_ImportModule (PYNSIGHT_PACKAGE);
  PyObject *io_module = Py_InitModule ("io", IO_Methods);
  PyModule_AddObject (pkg, "io", io_module);
  Py_DECREF (pkg);
  Py_INCREF (io_module);

  return true;
}

static bool
s_terminate () {
  return true;
}

static pynsight::Module IO ("io", s_init, s_terminate);


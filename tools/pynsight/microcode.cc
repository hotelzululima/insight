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
#include "gengen.hh"
#include "pynsight.hh"

struct PyMicrocode
{
  PyObject_HEAD
  PyObject *parent;
  const Microcode *mc;
};

static void
s_PyMicrocode_dealloc (PyObject *self);

static PyTypeObject PyMicrocodeType = {
  PyObject_HEAD_INIT(NULL)
  0,					/*ob_size*/
  "insight.PyMicrocode",		/*tp_name*/
  sizeof (PyMicrocode),		        /*tp_basicsize*/
  0,					/*tp_itemsize*/
  s_PyMicrocode_dealloc,		/*tp_dealloc*/
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
  "This type represents a program.",	/*tp_doc */
  0
};

static PyMethodDef PyMicrocodeMethods[] = {
  // { "run", s_PyMicrocode_run, METH_NOARGS, "\n" },
  { NULL, NULL, 0, NULL }
};

static bool 
s_init () 
{ 
  PyMicrocodeType.tp_methods = PyMicrocodeMethods;
  if (PyType_Ready (&PyMicrocodeType) < 0)
    return false;
  return true;
}

static bool 
s_terminate () 
{
  return true;
}

static pynsight::Module MICROCODE (NULL, s_init, s_terminate);

PyObject *
pynsight::microcode_object (PyObject *parent, const Microcode *mc)
{
  PyMicrocode *M = PyObject_New (PyMicrocode, &PyMicrocodeType);

  if (M == NULL)
    return NULL;

  PyObject_Init ((PyObject *) M, &PyMicrocodeType);

  M->parent = parent;
  Py_INCREF (parent);
  M->mc = mc;

  return (PyObject *) M;
}

static void
s_PyMicrocode_dealloc (PyObject *obj) {
  PyMicrocode *M = (PyMicrocode *) obj;

  Py_XDECREF (M->parent);
  M->ob_type->tp_free (M);
}

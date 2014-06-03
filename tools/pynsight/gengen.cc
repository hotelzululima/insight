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
#include "gengen.hh"

#include <stdexcept>


using namespace pynsight;

struct GeneratorObject
{
  PyObject_HEAD
  GenericGenerator *generator;
};

static void
s_GeneratorObject_dealloc (PyObject *p);

static PyObject *
s_GeneratorObject_iter (PyObject *p);

static PyObject *
s_GeneratorObject_iternext (PyObject *p);

static PyTypeObject GeneratorObjectType = {
  PyObject_HEAD_INIT(NULL)
  0,					/*ob_size*/
  "insight.Gengen",			/*tp_name*/
  sizeof (GeneratorObject),		/*tp_basicsize*/
  0,					/*tp_itemsize*/
  s_GeneratorObject_dealloc,		/*tp_dealloc*/
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
  Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_ITER,
  "Internal generic iterator",          /* tp_doc */
  0,                                    /* tp_traverse */
  0,                                    /* tp_clear */
  0,                                    /* tp_richcompare */
  0,                                    /* tp_weaklistoffset */
  s_GeneratorObject_iter,              /* tp_iter: __iter__() method */
  s_GeneratorObject_iternext,          /* tp_iternext: next() method */
  0
};

static bool
s_init ()
{
  GeneratorObjectType.tp_methods = NULL;
  if (PyType_Ready (&GeneratorObjectType) < 0)
    return false;
  return true;
}

static bool
s_terminate ()
{
  return true;
}

static pynsight::Module GENERIC_GENERATOR (NULL, s_init, s_terminate);

static void
s_GeneratorObject_dealloc (PyObject *self)
{
  GeneratorObject *g = (GeneratorObject *) self;

  delete g->generator;

  self->ob_type->tp_free (self);
}

static PyObject *
s_GeneratorObject_iter (PyObject *self)
{
  Py_INCREF (self);
  return self;
}

static PyObject *
s_GeneratorObject_iternext (PyObject *self)
{
  GeneratorObject *g = (GeneratorObject *) self;

  return g->generator->next ();
}

PyObject *
pynsight::generic_generator_new (GenericGenerator *G)
{
  GeneratorObject *result = (GeneratorObject *)
    PyObject_New (GeneratorObject, &GeneratorObjectType);

  if (result == NULL)
    return NULL;

  PyObject_Init ((PyObject *) result, &GeneratorObjectType);

  result->generator = G;

  return (PyObject *) result;
}

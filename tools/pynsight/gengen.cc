

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

#include <stdexcept>


using namespace pynsight;

struct GenericGenerator {
  PyObject_HEAD
  generic_generator_func generator;
  void *generator_data;
  void (*delete_data) (void *);
};

static void
s_GenericGenerator_dealloc (PyObject *p);

static PyObject *
s_GenericGenerator_iter (PyObject *p);

static PyObject *
s_GenericGenerator_iternext (PyObject *p);

static PyTypeObject GenericGeneratorType = {
  PyObject_HEAD_INIT(NULL)
  0,					/*ob_size*/
  "insight.Program",			/*tp_name*/
  sizeof(GenericGenerator),		/*tp_basicsize*/
  0,					/*tp_itemsize*/
  s_GenericGenerator_dealloc,		/*tp_dealloc*/
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
  s_GenericGenerator_iter,              /* tp_iter: __iter__() method */
  s_GenericGenerator_iternext,          /* tp_iternext: next() method */
  0
};

static bool 
s_init () { 
  GenericGeneratorType.tp_methods = NULL;
  if (PyType_Ready (&GenericGeneratorType) < 0)
    return false;
  return true;
}

static bool 
s_terminate () {
  return true;
}

static pynsight::Module GENERIC_GENERATOR (NULL, s_init, s_terminate);

static void
s_GenericGenerator_dealloc (PyObject *self) {
  GenericGenerator *g = (GenericGenerator *) self;

  if (g->delete_data != NULL) {
    g->delete_data (g->generator_data);
  }

  self->ob_type->tp_free (self);
}

static PyObject * 
s_GenericGenerator_iter (PyObject *self)
{
  Py_INCREF (self);
  return self;
}

static PyObject * 
s_GenericGenerator_iternext (PyObject *self)
{
  GenericGenerator *g = (GenericGenerator *) self;

  return g->generator (g->generator_data);
}

PyObject * 
pynsight::generic_generator_new (generic_generator_func G, void *Gdata, 
				 void (*delete_data)(void *data))
{
  GenericGenerator *result = (GenericGenerator *) 
    PyObject_New (GenericGenerator, &GenericGeneratorType);

  if (result == NULL)
    return NULL;

  result->generator = G;
  result->generator_data = Gdata;
  result->delete_data = delete_data;

  return (PyObject *) result;
}

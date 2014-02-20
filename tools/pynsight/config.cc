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
#include "pynsight.hh"

static PyObject *
s_Config_set (PyObject *, PyObject *args)
{
  const char *optname;
  PyObject *optvalue = NULL;
  PyObject *result = NULL;

  if (PyArg_ParseTuple (args, "sO", &optname, &optvalue))
    {
      ConfigTable &cfg = pynsight::configTable ();

      if (PyBool_Check (optvalue)) 
	cfg.set (optname, (optvalue == Py_True));
      else if (PyInt_Check (optvalue)) 
	cfg.set (optname, PyInt_AsLong (optvalue));
      else if (PyString_Check (optvalue)) 
	cfg.set (optname,  PyString_AsString(optvalue));
      else 
	PyErr_SetString (PyExc_TypeError, "invalid value type");
    }
  if (! PyErr_Occurred ())
    result = pynsight::None ();

  return result;
}

static PyObject *
s_Config_get (PyObject *, PyObject *args)
{
  PyObject *result;
  const char *optname = NULL;

  if (!PyArg_ParseTuple (args, "s", &optname))
    return NULL;
  ConfigTable &cfg = pynsight::configTable ();

  if (cfg.has (optname)) 
    result = Py_BuildValue ("s", cfg.get (optname).c_str ());
  else
    result = pynsight::None ();
  return result;
}

static PyMethodDef Config_Methods[] = {
  { 
    "set", (PyCFunction) s_Config_set, METH_VARARGS,
    "Set the value of configuation option"
  }, {
    "get", (PyCFunction) s_Config_get, METH_VARARGS,
    "Get value of a configuration option"
  }, { 
    NULL, NULL, 0, NULL 
  }
};

static bool 
s_init () 
{
  PyObject *pkg = PyImport_ImportModule (PYNSIGHT_PACKAGE);
  PyObject *cfg_module = Py_InitModule ("config", Config_Methods);  
  PyModule_AddObject (pkg, "config", cfg_module);
  Py_DECREF (pkg);
  Py_INCREF (cfg_module);

  return true;
}

static bool 
s_terminate () 
{
  return true;
}

static pynsight::Module CONFIG ("config", s_init, s_terminate);

ConfigTable &
pynsight::configTable () 
{
  static ConfigTable CONFIG;

  return CONFIG;
}

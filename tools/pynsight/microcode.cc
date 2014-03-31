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
#include <io/microcode/asm-writer.hh>
#include <io/microcode/dot-writer.hh>

struct PyMicrocode
{
  PyObject_HEAD
  pynsight::Program *prog;
  const pynsight::MicrocodeReference *mc;
};

static void
s_PyMicrocode_dealloc (PyObject *self);

static PyObject *
s_PyMicrocode_asm (PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
s_PyMicrocode_asmall (PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
s_PyMicrocode_dot (PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
s_PyMicrocode_get_range (PyObject *self, PyObject *);

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
  { "asm", (PyCFunction) s_PyMicrocode_asm, METH_VARARGS|METH_KEYWORDS, 
    "\n" },
  { "asmall", (PyCFunction) s_PyMicrocode_asmall, METH_VARARGS|METH_KEYWORDS, 
    "\n" },
  { "dot", (PyCFunction) s_PyMicrocode_dot, METH_VARARGS|METH_KEYWORDS, 
    "\n" },
  { "get_range", (PyCFunction) s_PyMicrocode_get_range, METH_NOARGS, 
    "\n" },
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
pynsight::microcode_object (Program *prog, 
			    const pynsight::MicrocodeReference *mc)
{
  PyMicrocode *M = PyObject_New (PyMicrocode, &PyMicrocodeType);

  if (M == NULL)
    return NULL;

  PyObject_Init ((PyObject *) M, &PyMicrocodeType);

  M->prog = prog;
  Py_INCREF ((PyObject *) prog);
  M->mc = mc;

  return (PyObject *) M;
}

static void
s_PyMicrocode_dealloc (PyObject *obj) 
{
  PyMicrocode *M = (PyMicrocode *) obj;

  Py_XDECREF (M->prog);
  M->ob_type->tp_free (M);
}

static PyObject *
s_PyMicrocode_asm (PyObject *self, PyObject *args, PyObject *kwds)
{
  static const char *kwlists[] =  
    { "addr", "len", "bytes", "holes", "labels", NULL };
  unsigned long addr;
  unsigned long len;
  unsigned char with_bytes = 0;
  unsigned char with_labels = 0;
  unsigned char with_holes = 0;  
  PyMicrocode *M = (PyMicrocode *) self;

  if (!PyArg_ParseTupleAndKeywords (args, kwds, "kk|bbb", (char **) kwlists, 
				    &addr, &len, 
				    &with_bytes, &with_holes, &with_labels))
    return NULL;

  asm_writer (std::cout, M->mc->get_microcode (), M->prog->concrete_memory, 
	      M->prog->symbol_table, with_bytes, with_holes, with_labels,
	      addr, len);

  return pynsight::None ();  
}

static PyObject *
s_PyMicrocode_asmall (PyObject *self, PyObject *args, PyObject *kwds)
{
  static const char *kwlists[] =  { "bytes", "holes", "labels", NULL };
  unsigned char with_bytes = 0;
  unsigned char with_labels = 0;
  unsigned char with_holes = 0;  
  PyMicrocode *M = (PyMicrocode *) self;

  if (!PyArg_ParseTupleAndKeywords (args, kwds, "|bbb", (char **) kwlists, 
				    &with_bytes, &with_holes, &with_labels))
    return NULL;

  asm_writer (std::cout, M->mc->get_microcode (), M->prog->concrete_memory, 
	      M->prog->symbol_table, with_bytes, with_holes, with_labels);

  return pynsight::None ();  
}

static PyObject *
s_PyMicrocode_dot (PyObject *self, PyObject *args, PyObject *kwds)
{
  static const char *kwlists[] =  { "startpoint", "start", "end", NULL };
  unsigned long ep;
  unsigned long start;
  unsigned long end;
  PyMicrocode *M = (PyMicrocode *) self;

  if (!PyArg_ParseTupleAndKeywords (args, kwds, "kkk", (char **) kwlists, 
				    &ep, &start, &end))
    return NULL;

  std::ostringstream oss;
  ConcreteAddress ca_ep (ep);
  ConcreteAddress ca_start (start);
  ConcreteAddress ca_end (end);

  dot_asm_writer (oss, M->mc->get_microcode (), &ca_start, &ca_end, &ca_ep, 
		  M->prog->symbol_table, true, "");

  return Py_BuildValue ("s", oss.str ().c_str ());
}

static void
s_microcode_addrspace (const Microcode *mc, address_t &minaddr, 
		       address_t &maxaddr)
{ 
  minaddr = MAX_ADDRESS;
  maxaddr = 0;

  Microcode_iterate_nodes (*mc, node)
    {
      address_t addr = (*node)->get_loc ().getGlobal ();
      if (addr < minaddr)
	minaddr = addr;
      if (addr > maxaddr)
	maxaddr = addr;
    }
}

static PyObject *
s_PyMicrocode_get_range (PyObject *self, PyObject *)
{
  PyMicrocode *M = (PyMicrocode *) self;
  address_t minaddr;
  address_t maxaddr;

  s_microcode_addrspace (M->mc->get_microcode (), minaddr, maxaddr);

  return Py_BuildValue ("(k,k)", minaddr, maxaddr);
}

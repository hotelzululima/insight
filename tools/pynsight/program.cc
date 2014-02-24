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

#include <stdexcept>
#include <domains/concrete/ConcreteMemory.hh>
# include <io/binary/BinutilsBinaryLoader.hh>
#include <decoders/binutils/BinutilsDecoder.hh>

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/SymbolTable.hh>
#include <analyses/cfgrecovery/LinearSweep.hh>
#include "gengen.hh"

using pynsight::Program;

static void
s_insight_Program_dealloc (PyObject *p);

static PyObject *
s_insight_Program_info (PyObject *p, PyObject *);

static PyObject *
s_insight_Program_sym (PyObject *p, PyObject *args);

static PyObject *
s_insight_Program_symbols (PyObject *p, PyObject *);

static PyObject *
s_insight_Program_dump_memory (PyObject *p, PyObject *args, PyObject *kwds);

static PyObject *
s_insight_Program_disas (PyObject *p, PyObject *args, PyObject *kwds);

static PyObject *
s_insight_Program_simulate (PyObject *p, PyObject *args, PyObject *kwds);

static PyTypeObject insight_ProgramType = {
  PyObject_HEAD_INIT(NULL)
  0,					/*ob_size*/
  "insight.Program",			/*tp_name*/
  sizeof(struct Program),		/*tp_basicsize*/
  0,					/*tp_itemsize*/
  s_insight_Program_dealloc,		/*tp_dealloc*/
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

static PyMethodDef programMethods[] = {
  {
    "info",
    s_insight_Program_info,
    METH_NOARGS,
    "Return a dictionary containing data related to the program "
    "(e.g entrypoint).\n"
  }, { 
    "sym", 
    s_insight_Program_sym, 
    METH_VARARGS,
    "Symbol table access method.\n"
    "Accepts an address or a string and returns the corresponding other kind."
  }, { 
    "symbols", 
    s_insight_Program_symbols, 
    METH_NOARGS,
    "Return the list of known symbols.\n"
  }, { 
    "dump_memory", 
    (PyCFunction) s_insight_Program_dump_memory, 
    METH_VARARGS|METH_KEYWORDS,
    "Return a list of tuples containing memory bytes.\n"
  }, { 
    "disas", 
    (PyCFunction) s_insight_Program_disas, 
    METH_VARARGS|METH_KEYWORDS,
    "Return an iterator on disassembled instructions."
  }, { 
    "simulator", 
    (PyCFunction) s_insight_Program_simulate, 
    METH_VARARGS|METH_KEYWORDS,
    "Start a step-by-step simulator."
  }, { 
    NULL, NULL, 0, NULL 
  }
};

static bool 
s_init () { 
  insight_ProgramType.tp_methods = programMethods;
  if (PyType_Ready (&insight_ProgramType) < 0)
    return false;
  return true;
}

static bool 
s_terminate () {
  return true;
}

static pynsight::Module PROGRAM (NULL, s_init, s_terminate);

PyObject * 
pynsight::load_program (const char *filename, const char *target, 
			const char *mach, Architecture::endianness_t endian) {
  struct Program *p = PyObject_New (struct Program, &insight_ProgramType);
  if (p == NULL)
    return NULL;

  p->concrete_memory = NULL;
  p->symbol_table = NULL;
  p->loader = NULL;
  p->stubfactory = NULL;

  PyObject_Init ((PyObject *) p, &insight_ProgramType);

  try {
    p->loader = new BinutilsBinaryLoader (filename, target, mach, endian);
    p->concrete_memory = new ConcreteMemory ();
    p->symbol_table = new SymbolTable ();
    p->stubfactory = p->loader->get_StubFactory ();
    p->loader->load_memory (p->concrete_memory);
    p->loader->load_symbol_table (p->symbol_table);
  } catch (std::runtime_error &e) {
    PyErr_SetString (pynsight::BFDError, e.what ());
  } catch (std::bad_alloc &e) {
    PyErr_NoMemory();
  }
  
  if (PyErr_Occurred ()) {
    Py_DECREF (p);
    p = NULL;
  }

  return (PyObject *) p;
}


static void
s_insight_Program_dealloc (PyObject *obj) {
  Program *p = (Program *) obj;
  if (p->concrete_memory != NULL) {
    delete p->concrete_memory;
    p->concrete_memory = NULL;
  }

  if (p->symbol_table != NULL) {
    delete p->symbol_table;
    p->symbol_table = NULL;
  }

  if (p->stubfactory != NULL) {
    delete p->stubfactory;
    p->stubfactory = NULL;
  }

  if (p->loader != NULL) {
    delete p->loader;
    p->loader = NULL;
  }

  p->ob_type->tp_free (p);
}

static PyObject *
s_insight_Program_sym (PyObject *p, PyObject *args) {
  struct Program *self = (struct Program *) p;
  long address;
  const char *symbol;

  if (PyArg_ParseTuple(args, "s", &symbol)) {
    if (self->symbol_table->has(symbol)) {
      address = (long) self->symbol_table->get(symbol);
      return Py_BuildValue("i", address);
    } 
  } else if (PyArg_ParseTuple(args, "i", &address)) {
    PyErr_Clear();
    if (self->symbol_table->has((address_t) address)) {
      symbol = self->symbol_table->get((address_t) address).front().c_str();
      return Py_BuildValue("s", symbol);
    } 
  } else {
    return NULL;
  }

  return pynsight::None ();
}

static PyObject *
s_insight_Program_symbols (PyObject *obj, PyObject *) {
  Program *p = (Program *) obj;
  PyObject *result = PyList_New (0);
  if (result == NULL)
    return NULL;

  SymbolTable::const_symbol_iterator i = p->symbol_table->begin_symbols ();
  SymbolTable::const_symbol_iterator end = p->symbol_table->end_symbols ();
  for (; i != end && !PyErr_Occurred (); i++) {
    PyObject *c = Py_BuildValue ("(s,i)", i->first.c_str (), i->second);
    if (c != NULL) {
      PyList_Append (result, c);
      Py_DECREF (c);
    }
  }

  if (PyErr_Occurred ()) {
    Py_DECREF (result);
    result = NULL;
  } 

  return result;
}

class DumpIterator : public pynsight::GenericGenerator 
{
private:
  Program *p;
  Py_ssize_t current;
  Py_ssize_t len;
  Py_ssize_t step;
  
public:
  DumpIterator (Program *prg, Py_ssize_t addr, Py_ssize_t len, Py_ssize_t step)
    : pynsight::GenericGenerator(), 
      p (prg), current (addr), len (len), step (step) { 
    Py_INCREF ((PyObject *)prg);    
  }

  ~DumpIterator () {
    Py_DECREF ((PyObject *) p);
  }

  PyObject *next () {
    PyObject *result = NULL;

    if (len == 0) 
      PyErr_SetNone (PyExc_StopIteration);
    else 
      {
	PyObject *line_addr = Py_BuildValue ("n", current);
	int max = std::min (step, len);

	if (line_addr != NULL) 
	  {
	    PyObject *tuple = PyTuple_New (step);
	    if (tuple != NULL) 
	      {
		for (Py_ssize_t i = 0; i < step && !PyErr_Occurred (); i++) 
		{
		  PyObject *b = NULL;
		  ConcreteAddress addr ((address_t) current + i);
		  
		  if (i < max && p->concrete_memory->is_defined (addr)) 
		    {
		      ConcreteValue val = 
			p->concrete_memory->get (addr, 1, 
						 Architecture::LittleEndian);
		      b = Py_BuildValue ("b", (unsigned char) val.get ());
		    } else {
		    b = pynsight::None ();
		  }
		  if (b != NULL)		
		    PyTuple_SET_ITEM (tuple, i, b);
		}
		
		if (!PyErr_Occurred ()) 
		  result = PyTuple_Pack (2, line_addr, tuple);
		Py_DECREF (tuple);
	      }
	    Py_DECREF (line_addr);
	  }
	
	if (! PyErr_Occurred ()) 
	  {
	    len -= max;
	    current += max;
	  }
      }

    return result;
  }
};

static PyObject * 
s_insight_Program_dump_memory (PyObject *obj, PyObject *args, PyObject *kwds) 
{
  static const char *kwlists[] =  { "start", "len", "step", NULL };
  Program *p = (Program *) obj;
  address_t s,e;


  p->concrete_memory->get_address_range (s, e);

  Py_ssize_t start = s;
  Py_ssize_t len = e - s + 1;
  Py_ssize_t step = 16;


  if (!PyArg_ParseTupleAndKeywords (args, kwds, "|III", (char **) kwlists, 
				    &start, &len, &step))
    return NULL;

  if (! (s <= start && start <= e)) 
    {    
      PyErr_SetString (PyExc_LookupError, "start address is out of memory");
      return NULL;
    }

  if (step == 0 || len == 0)
    return pynsight::None ();

  if (start + len >= e) 
    len = e - start + 1;

  PyObject *result = 
    pynsight::generic_generator_new (new DumpIterator (p, start, len, step));

  return result;
}

static PyObject *
s_registers (const Architecture *arch) {
  const RegisterSpecs *regspecs = arch->get_registers ();
  PyObject *result = PyDict_New ();

  if (result == NULL)
    return NULL;

  for (RegisterSpecs::const_iterator i = regspecs->begin (); 
       i != regspecs->end () && !PyErr_Occurred (); i++) {
    const char *regname = i->second->get_label ().c_str ();
    PyObject *regsize = Py_BuildValue ("I", i->second->get_window_size ());
    if (regsize == NULL) 
      break;

    PyDict_SetItemString (result, regname, regsize);
    Py_DECREF (regsize);
  }

  if (PyErr_Occurred ()) {
    Py_DECREF (result);
    result = NULL;
  }

  return result;
}

static PyObject *
s_insight_Program_info (PyObject *obj, PyObject *)
{
  Program *p = (Program *) obj;
  PyObject *regs = s_registers (p->loader->get_architecture ());
  if (regs == NULL)
    return NULL;
  address_t start_addr, end_addr;

  p->concrete_memory->get_address_range (start_addr, end_addr);

  PyObject *result = Py_BuildValue 
    ("{s:s, s:s, s:I, s:s, s:s, s:I, s:I, s:I, s:I, s:O}", 
     "inputname", 
     p->loader->get_filename ().c_str (),
     "format", 
     p->loader->get_format ().c_str (),
     "entrypoint", 
     p->loader->get_entrypoint ().get_address (),
     "cpu", 
     p->loader->get_architecture()->get_proc_name(),
     "endianness", 
     p->loader->get_architecture()->get_endian_name(),
     "word_size", 
     p->loader->get_architecture ()->get_word_size (),
     "address_size", 
     p->loader->get_architecture ()->get_address_size (),
     "memory_min_address", 
     start_addr, 
     "memory_max_address", 
     end_addr,
     "registers", 
     regs
     );
  Py_XDECREF (regs);

  return result;
}

class DisasIterator : public pynsight::GenericGenerator 
{
private:
  address_t current_addr;
  address_t max_addr;
  MicrocodeArchitecture *march;
  BinutilsDecoder *decoder;
public:
  DisasIterator (Program *p, address_t start, address_t max) 
    : pynsight::GenericGenerator (), current_addr (start), max_addr (max) {
    march = new MicrocodeArchitecture (p->loader->get_architecture ());
    decoder = new BinutilsDecoder (march, p->concrete_memory);
  }

  virtual ~DisasIterator () {
    delete march;
    delete decoder;
  }

  PyObject *next () {
    PyObject *result = NULL;

    if (current_addr >= max_addr) 
      PyErr_SetNone (PyExc_StopIteration);
    else 
      {
	try 
	  {
	    std::string inst = decoder->get_instruction (current_addr);
	    address_t next = decoder->next (current_addr).get_address ();
	    result = Py_BuildValue ("(i,s)", current_addr, inst.c_str ());
	    current_addr = next;
	  } 
	catch (Decoder::OutOfBounds &e)
	  {
	    PyErr_SetNone (PyExc_StopIteration);
	  }
      }
    
    return (result);
  }
};


static PyObject *
s_insight_Program_disas (PyObject *obj, PyObject *args, PyObject *kwds)
{
  static const char *kwlists[] =  { "start", "len", NULL };
  Program *p = (Program *) obj;
  address_t s,e;

  p->concrete_memory->get_address_range (s, e);

  Py_ssize_t start = s;
  Py_ssize_t len = e - s + 1;

  if (!PyArg_ParseTupleAndKeywords (args, kwds, "|II", (char **) kwlists, 
				    &start, &len))
    return NULL;

  if (! (s <= start && start <= e)) {    
    PyErr_SetString (PyExc_LookupError, "start address is out of memory");
    return NULL;
  }

  if (len == 0)
    return pynsight::None ();

  if (start + len >= e) {
    len = e - start + 1;
  }

  DisasIterator *di = new DisasIterator (p, start, start + len);
  PyObject *result = pynsight::generic_generator_new (di);

  return result;
}

static PyObject *
s_insight_Program_simulate (PyObject *obj, PyObject *args, PyObject *kwds)
{
  static const char *kwlists[] =  { "start", "domain", NULL };
  Program *p = (Program *) obj;

  address_t s,e;

  p->concrete_memory->get_address_range (s, e);

  Py_ssize_t start = p->loader->get_entrypoint ().get_address ();
  const char *domain = "symbolic";

  if (!PyArg_ParseTupleAndKeywords (args, kwds, "|Is", (char **) kwlists, 
				    &start, &domain))
    return NULL;

  if (! (s <= start && start <= e)) {    
    PyErr_SetString (PyExc_LookupError, "start address is out of memory");
    return NULL;
  }

  pynsight::SimulationDomain sem;
  if (strcmp (domain, "symbolic") == 0) sem = pynsight::SIM_SYMBOLIC;
  else if (strcmp (domain, "concrete") == 0) sem = pynsight::SIM_CONCRETE;
  else 
    {
      PyErr_SetString (PyExc_LookupError, "unknown domain");
      return NULL;
    }
  PyObject *result = pynsight::start_simulator (p, start, sem);

  return result;
}

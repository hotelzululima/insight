/*
 * Wrapper glue for python
 */

#include <Python.h>

#include <domains/concrete/ConcreteMemory.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <kernel/insight.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/SymbolTable.hh>

/*
 * Insight Program Type
 */
struct Program {
  PyObject_HEAD
  ConcreteMemory *concrete_memory;
  SymbolTable *symbol_table;
};

static PyTypeObject insight_ProgramType = {
  PyObject_HEAD_INIT(NULL)
  0,					/*ob_size*/
  "insight.Program",			/*tp_name*/
  sizeof(struct Program),		/*tp_basicsize*/
  0,					/*tp_itemsize*/
  0,					/*tp_dealloc*/
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
  "This type represents a program",	/* tp_doc */
  0
};

static PyObject *
insight_Program_new(PyTypeObject *type, PyObject *, PyObject *) {
  struct Program *self;
  self = (struct Program *) type->tp_alloc(type, 0);
  if (self != NULL) {
    self->concrete_memory = NULL;
    self->symbol_table = NULL;
  }

  return (PyObject *) self;
}

static void
insight_Program_reset(struct Program *p) {
  if (p->concrete_memory != NULL) {
    delete p->concrete_memory;
    p->concrete_memory = NULL;
  }
  if (p->symbol_table != NULL) {
    delete p->symbol_table;
    p->symbol_table = NULL;
  }
}

static void
insight_Program_dealloc(PyObject *p) {
  insight_Program_reset((struct Program *) p);
  p->ob_type->tp_free(p);
}

static int
insight_Program_init(PyObject *p, PyObject *, PyObject *) {
  insight_Program_reset((struct Program *) p);
  return 0;
}

static PyObject *program_sym(PyObject *, PyObject *);

static PyMethodDef programMethods[] = {
  { "sym", program_sym, METH_VARARGS,
    "Symbol table access method.\n"
    "Accepts an address or a string and returns the corresponding other kind."
  },
  { NULL, NULL, 0, NULL }
};

static PyObject *
program_sym(PyObject *p, PyObject *args) {
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
  } else
    return NULL;

  PyErr_Clear();
  /* Symbol/Address not found */
  return Py_BuildValue("");
}

/*
 * Insight Module
 */

static PyObject *insight_load_bfd(PyObject *, PyObject *);

static PyMethodDef insightMethods[] = {
  { "load_bfd", insight_load_bfd, METH_VARARGS,
    "Load a file with the BFD library" },
  { NULL, NULL, 0, NULL }
};

static PyObject *
insight_load_bfd(PyObject *, PyObject *fname) {
  const char *c_fname;

  if (!PyArg_ParseTuple(fname, "s", &c_fname))
    return NULL;

  struct Program *p = PyObject_New(struct Program, &insight_ProgramType);
  p = (struct Program *) PyObject_Init((PyObject *) p, &insight_ProgramType);

  BinutilsBinaryLoader loader(c_fname, "", "", Architecture::UnknownEndian);

  p->concrete_memory = new ConcreteMemory();
  loader.load_memory(p->concrete_memory);

  p->symbol_table = new SymbolTable();
  loader.load_symbol_table(p->symbol_table);

  return (PyObject *) p;
}

int
main(void) {
  insight::init();
  Py_Initialize();
  Py_InitModule("insight", insightMethods);
  insight_ProgramType.tp_methods = programMethods;
  insight_ProgramType.tp_new = insight_Program_new;
  insight_ProgramType.tp_init = insight_Program_init;
  insight_ProgramType.tp_dealloc = insight_Program_dealloc;
  PyType_Ready(&insight_ProgramType);
  PyRun_SimpleString("import insight\n");

  PyRun_InteractiveLoop(stdin, "<stdin>");
  Py_Finalize();
  return EXIT_SUCCESS;
}

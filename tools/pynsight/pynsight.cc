/*
 * Wrapper glue for python
 */
#include <kernel/insight.hh>
#include "pynsight.hh"

static PyObject *insight_load_bfd(PyObject *, PyObject *, PyObject *kwds);

static PyMethodDef insightMethods[] = {
  { "load_bfd", (PyCFunction) insight_load_bfd, METH_VARARGS|METH_KEYWORDS,
    "Load a file with the BFD library" },
  { NULL, NULL, 0, NULL }
};

static PyObject *
insight_load_bfd(PyObject *, PyObject *args, PyObject *kwds) {
  static const char *kwlists[] = 
    { "filename", "target", "machine", "endianness", NULL };
  const char *c_fname;
  const char *c_bfdtarget = "";
  const char *c_machine = "";
  const char *c_endianness = NULL;

  if (!PyArg_ParseTupleAndKeywords (args, kwds, "s|sss", (char **) kwlists, 
				    &c_fname, &c_bfdtarget, &c_machine, 
				    &c_endianness))
    return NULL;

  Architecture::endianness_t endian = Architecture::UnknownEndian;

  if (c_endianness) {
    if (strcmp (c_endianness, "little") == 0) { 
      endian = Architecture::LittleEndian;
    } else if (strcmp (c_endianness, "big") == 0) { 
      endian = Architecture::BigEndian;
    } else if (strcmp (c_endianness, "unknown") != 0) { 
      PyErr_SetString (pynsight::Error, "invalid endianness.");
      return NULL;
    }
  }

  return pynsight::load_program (c_fname, c_bfdtarget, c_machine, endian);
}

PyObject *pynsight::Error = NULL;

int
main (int argc, char **argv) {
  int result =  EXIT_SUCCESS;

  insight::init();

  Py_Initialize();
  PyObject *m = Py_InitModule("insight", insightMethods);

  /* Declare general purpose error of the module */
  pynsight::Error = PyErr_NewException ((char *) "insight.error", NULL, NULL);
  Py_INCREF (pynsight::Error);
  PyModule_AddObject (m, "error", pynsight::Error);

  if (pynsight::program_init ())
    {
      PyRun_SimpleString("import insight\n");
      if (Py_Main (argc, argv) != 0)
	result = EXIT_FAILURE;
      pynsight::program_terminate ();
    }
  Py_DECREF (m);
  Py_Finalize();

  insight::terminate ();

  return result;
}

/*
 * Wrapper glue for python
 */

#include <Python.h>

static PyObject *toto(PyObject *, PyObject *);

static PyMethodDef InsightMethods[] = {
  { "toto", toto, METH_VARARGS, "the famous toto function" },
  { NULL, NULL, 0, NULL }
};

static PyObject *
toto(PyObject *, PyObject *) {
  Py_RETURN_NONE;
}

int
main(void) {
  Py_Initialize();
  (void) Py_InitModule("insight", InsightMethods);
  PyRun_SimpleString("from insight import toto\n");

  PyRun_InteractiveLoop(stdin, "<stdin>");
  Py_Finalize();
  return EXIT_SUCCESS;
}

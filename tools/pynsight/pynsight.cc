/*
 * Wrapper glue for python
 */
#include <kernel/insight.hh>
#include <kernel/expressions/ExprSolver.hh>
#include "pynsight.hh"

# ifndef PYNSIGHT_HOME
#  error PYNSIGHT_HOME is not defined
# endif
# ifndef PYNSIGHT_PACKAGE
#  error PYNSIGHT_PACKAGE is not defined
# endif

#define PRE_SCRIPT \
  "import sys\n" \
  "sys.path.append('" PYNSIGHT_HOME "')\n"

#define POST_SCRIPT \
  "import insight\n" \
  "from insight import *\n"


using namespace pynsight;

static std::list<Module *> &
s_get_modules ()
{
  static std::list<Module *> modules;

  return modules;
}

pynsight::Module::Module (const char *name, bool (*i) (), bool (*t) ())
  : name (name), init_cb (i), terminate_cb (t) {
  s_get_modules ().push_back (this);
}

static bool
s_init_package ()
{
  bool result = true;

  if (PyRun_SimpleString (PRE_SCRIPT) < 0)
    return false;

  PyObject *pkg = PyImport_ImportModule (PYNSIGHT_PACKAGE);

  if (pkg == NULL)
    return false;

  /* Declare general purpose error of the module */

  for (std::list<Module *>::const_iterator i = s_get_modules ().begin ();
       i != s_get_modules ().end () && result; i++) {
    result = (*i)->init ();
    if ((*i)->get_name () != NULL) {
      std::string s ("import ");
      s += (*i)->get_name ();
      result = (PyRun_SimpleString (s.c_str ()) >= 0);
    }
  }
  Py_DECREF (pkg);

  if (PyRun_SimpleString (POST_SCRIPT) < 0)
    return false;


  return result;
}

static bool
s_terminate_package () {
  bool result = true;
  for (std::list<Module *>::const_iterator i = s_get_modules ().begin ();
       i != s_get_modules ().end (); i++) {
    if (! (*i)->terminate ())
      result = false;
  }
  return result;
}

int
main (int argc, char **argv) {
  int result =  EXIT_SUCCESS;

  insight::init (pynsight::configTable ());

  Py_Initialize();
  if (s_init_package ())
    {
      if (Py_Main (argc, argv) != 0)
	result = EXIT_FAILURE;
    }
  else if (PyErr_Occurred ())
    {
      PyErr_Print ();
    }
  s_terminate_package ();
  Py_Finalize();

  insight::terminate ();

  return result;
}


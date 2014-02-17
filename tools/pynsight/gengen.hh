#ifndef GENGEN_HH
# define GENGEN_HH

# include <Python.h>
# include "pynsight.hh"

namespace pynsight {
  typedef PyObject * (*generic_generator_func) (void *data);

  extern PyObject *generic_generator_new (generic_generator_func G, 
					  void *Gdata, 
					  void (*delete_data)(void *data));
}

#endif /* ! GENGEN_HH */

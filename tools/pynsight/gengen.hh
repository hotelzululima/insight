#ifndef GENGEN_HH
# define GENGEN_HH

# include <Python.h>
# include "pynsight.hh"

namespace pynsight {
  class GenericGenerator {
  public:
    virtual ~GenericGenerator() { }
    virtual PyObject * next () = 0;
  };

  //  typedef PyObject * (*generic_generator_func) (void *data);

  extern PyObject *generic_generator_new (GenericGenerator *G);
}

#endif /* ! GENGEN_HH */

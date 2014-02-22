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
#include <stdexcept>
# include <kernel/annotations/AsmAnnotation.hh>
# include <kernel/annotations/NextInstAnnotation.hh>
#include <domains/concrete/ConcreteMemory.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <decoders/binutils/BinutilsDecoder.hh>

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/SymbolTable.hh>
#include <domains/concrete/ConcreteStepper.hh>
#include <domains/symbolic/SymbolicStepper.hh>

#include "gengen.hh"
#include "pynsight.hh"

using std::vector;
using std::string;
using pynsight::Program;

class GenericInsightSimulator {
public:
  typedef vector<StmtArrow *> ArrowVector;

  GenericInsightSimulator (Program *prg, address_t start_addr);

  virtual ~GenericInsightSimulator ();

  virtual MicrocodeArchitecture *get_march () const;

  virtual void clear_arrows ();
  virtual size_t get_number_of_arrows () const;
  virtual StmtArrow *get_arrow_at (size_t i) const;

  virtual string state_to_string (void *s) = 0;
  virtual void *get_initial_state () = 0;
  virtual void set_state (void *s) = 0;
  virtual void delete_state (void *s) = 0;
  virtual void *get_state () = 0;
  virtual void *trigger_arrow (void *from, StmtArrow *a) = 0;

  virtual void set_memory (address_t addr, uint8_t val) = 0;
  virtual string get_memory (address_t addr) = 0;
  virtual void set_register (const RegisterDesc *reg, word_t val) = 0;
  virtual string get_register (const RegisterDesc *reg) = 0;
  virtual bool check_memory_range (void *s, address_t addr, size_t len) = 0;
  virtual bool check_register (void *s, const RegisterDesc *reg) = 0;
  virtual MicrocodeAddress get_pc (void *s) = 0;
  virtual MicrocodeAddress get_current_pc () = 0;

protected:
  Program *prg;  
  ConcreteAddress start;
  Decoder *decoder;
  Microcode *mc;
  MicrocodeArchitecture *march;
  ArrowVector *arrows;
};

template <typename Stepper>
class InsightSimulator : public GenericInsightSimulator {
public:
  typedef typename Stepper::State State;
  typedef typename Stepper::ProgramPoint ProgramPoint;

  InsightSimulator (Program *prg, address_t start_addr);
  virtual ~InsightSimulator ();

  virtual string state_to_string (void *s);
  virtual void *get_initial_state ();
  virtual void set_state (void *ptr);
  virtual void delete_state (void *ptr);

  virtual void *get_state ();
  virtual void *trigger_arrow (void *from, StmtArrow *a);

  virtual void set_memory (address_t addr, uint8_t value);
  virtual string get_memory (address_t addr);
  virtual void set_register (const RegisterDesc *reg, word_t value);
  virtual string get_register (const RegisterDesc *reg);
  virtual bool check_memory_range (void *s, address_t addr, size_t len);
  virtual bool check_register (void *s, const RegisterDesc *reg);
  virtual MicrocodeAddress get_pc (void *s);
  virtual MicrocodeAddress get_current_pc ();

protected:
  Stepper *stepper;
  State *current_state;

private:
  void compute_enabled_arrows (State *s, ArrowVector *result);
  MicrocodeNode *get_node (const ProgramPoint *pp);
};

struct Simulator {
  PyObject_HEAD
  GenericInsightSimulator *gsim;
};


static void
s_Simulator_dealloc (PyObject *self);

static PyObject *
s_Simulator_run (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_microstep (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_step (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_print_state (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_set_memory (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_get_memory (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_set_register (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_get_register (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_get_pc (PyObject *self, PyObject *);

static PyObject *
s_Simulator_get_arrows (PyObject *self, PyObject *);

static PyTypeObject SimulatorType = {
  PyObject_HEAD_INIT(NULL)
  0,					/*ob_size*/
  "insight.Simulator",			/*tp_name*/
  sizeof (Simulator),		        /*tp_basicsize*/
  0,					/*tp_itemsize*/
  s_Simulator_dealloc,		        /*tp_dealloc*/
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

#define METHOD(lname, sname, proc, flags, help) \
  { lname, proc, flags, help }, \
  { sname, proc, flags, help } 

static PyMethodDef SimulatorMethods[] = {
  METHOD ("run", "r", s_Simulator_run, METH_NOARGS, 
	  "\n"),
  METHOD ("microstep", "ms", s_Simulator_microstep, METH_VARARGS, 
	  "\n"),
  METHOD ("step", "s", s_Simulator_step, METH_NOARGS, 
	  "\n"),
  METHOD ("print_state", "ps", s_Simulator_print_state, METH_NOARGS, 
	  "\n"),
  METHOD ("set_memory", "sm", s_Simulator_set_memory, METH_VARARGS, 
	  "\n"),
  METHOD ("set_register", "sr", s_Simulator_set_register, METH_VARARGS, 
	  "\n"),
  METHOD ("get_memory", "gm", s_Simulator_get_memory, METH_VARARGS, 
	  "\n"),
  METHOD ("get_register", "gr", s_Simulator_get_register, METH_VARARGS, 
	  "\n"),
  METHOD ("get_pc", "pc", s_Simulator_get_pc, METH_NOARGS,
	  "\n"),
  METHOD ("get_arrows", "a", s_Simulator_get_arrows, METH_NOARGS,
	  "\n"),
  { NULL, NULL, 0, NULL }
};

static bool 
s_init () 
{ 
  SimulatorType.tp_methods = SimulatorMethods;
  if (PyType_Ready (&SimulatorType) < 0)
    return false;
  return true;
}

static bool 
s_terminate () 
{
  return true;
}

static pynsight::Module SIMULATOR (NULL, s_init, s_terminate);

PyObject * 
pynsight::start_simulator (Program *P, address_t start_addr,
			   SimulationDomain dom)
{
  Simulator *S = PyObject_New (Simulator, &SimulatorType);

  if (S == NULL)
    return NULL;

  PyObject_Init ((PyObject *) S, &SimulatorType);

  if (dom == pynsight::SIM_SYMBOLIC)
    S->gsim = new InsightSimulator<SymbolicStepper> (P, start_addr);
  else 
    {
      assert (dom == pynsight::SIM_CONCRETE);
      S->gsim = new InsightSimulator<ConcreteStepper> (P, start_addr);
    }

  return (PyObject *) S;
}

static void
s_Simulator_dealloc (PyObject *obj) {
  Simulator *S = (Simulator *) obj;

  delete S->gsim;
  S->ob_type->tp_free (S);
}

class ArrowsIterator : public pynsight::GenericGenerator
{
private:
  GenericInsightSimulator *gsim;
  size_t current;
public:
  ArrowsIterator (GenericInsightSimulator *gsim) : gsim (gsim), current (0) { }

  virtual ~ArrowsIterator () { }

  PyObject *next () {
    PyObject *result = NULL;
    if (current >= gsim->get_number_of_arrows ())
      PyErr_SetNone (PyExc_StopIteration);
    else
      {
	StmtArrow *a = gsim->get_arrow_at (current);
	current++;
	result = Py_BuildValue ("s", a->pp ().c_str ());
      }

    return result;
  } 
};

static PyObject *
s_Simulator_run (PyObject *p, PyObject *)
{  
  GenericInsightSimulator *S = ((Simulator *) p)->gsim;

  void *is = S->get_initial_state ();
  S->set_state (is);
  S->delete_state (is);

  PyObject *result = 
    pynsight::generic_generator_new (new ArrowsIterator (S));

  return result;  
}

static PyObject *
s_Simulator_microstep (PyObject *self, PyObject *args)
{
  PyObject *result;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  unsigned int aindex;

  if (! PyArg_ParseTuple (args, "I", &aindex))
    return NULL;
  
  if (aindex >= S->get_number_of_arrows ())
    {
      PyErr_SetString (PyExc_IndexError, "invalid microcode-arrow index");
      return NULL;
    }

  StmtArrow *a = S->get_arrow_at (aindex);
  void *st = S->get_state ();
  void *newst = S->trigger_arrow (st, a);
  if (newst != NULL)
    {
      S->set_state (newst);      
      result = pynsight::generic_generator_new (new ArrowsIterator (S));
    }
  else
    {
      result = NULL;
    }
  S->delete_state (st);

  return result;  
}

static PyObject *
s_Simulator_step (PyObject *self, PyObject *x1)
{
  PyObject *result;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  MicrocodeAddress ep = S->get_current_pc ();

  while (ep.getGlobal () == S->get_current_pc ().getGlobal () &&
	 ! PyErr_Occurred ())
    {
      MicrocodeAddress tmp = S->get_current_pc ();
      if (S->get_number_of_arrows () > 1)
	{
	  PyErr_SetNone (pynsight::NotDeterministicBehaviorError);
	  return NULL;
	}
      StmtArrow *a = S->get_arrow_at (0);

      void *st = S->get_state ();
      void *succ = S->trigger_arrow (st, a);
      if (succ != NULL)
	{
	  S->set_state (succ);
	  S->delete_state (succ);	    
	}
      S->delete_state (st);
    }

  if (PyErr_Occurred ())
    result = NULL;
  else
    result = pynsight::generic_generator_new (new ArrowsIterator (S));

  return result;
}

static PyObject *
s_Simulator_print_state (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  void *s = S->get_state ();
  PyObject *result;

  if (s == NULL)
    result = pynsight::None ();
  else
    {
      string sstr = S->state_to_string (s);
      result = Py_BuildValue ("s", sstr.c_str ());
    }			    
  S->delete_state (s);
  
  return result;
}

static PyObject *
s_Simulator_set_memory (PyObject *self, PyObject *args)
{
  Py_ssize_t addr;
  unsigned char byte;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (!PyArg_ParseTuple (args, "Ib", &addr, &byte))
    return NULL;
  S->set_memory (addr, byte);

  return pynsight::None ();
}

static PyObject *
s_Simulator_get_memory (PyObject *self, PyObject *args)
{
  unsigned long addr;
  unsigned long len = 1;
  PyObject *result = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (!PyArg_ParseTuple (args, "k|k", &addr, &len))
    return NULL;

  void *st = S->get_state ();  
  if (S->check_memory_range (st, addr, len)) 
    {
      result = PyTuple_New (len);
      for (unsigned long i = 0; i < len && ! PyErr_Occurred (); i++)
	{
	  string v = S->get_memory (addr + i);
	  PyObject *val = Py_BuildValue ("s", v.c_str ());

	  if (val != NULL) 
	    PyTuple_SetItem (result, i, val);
	  else
	    Py_XDECREF (val);
	}
      if (PyErr_Occurred ())
	{
	  Py_XDECREF (result);
	  result = NULL;
	}
    }
  else
    {
      PyErr_SetString (PyExc_IndexError, "memory range out of bounds");
    }
  S->delete_state (st);

  return result;
}


static PyObject *
s_Simulator_set_register (PyObject *self, PyObject *args)
{
  const char *regname;
  unsigned long regval;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (!PyArg_ParseTuple (args, "sk", &regname, &regval))
    return NULL;

  const RegisterDesc *rd = S->get_march ()->get_register (regname);
  if (rd == NULL)
    PyErr_SetString (PyExc_LookupError, "unknown register");
  else
    S->set_register (rd, regval);

  return pynsight::None ();
}

static PyObject *
s_Simulator_get_register (PyObject *self, PyObject *args)
{
  const char *regname;

  if (!PyArg_ParseTuple (args, "s", &regname))
    return NULL;

  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  PyObject *result = NULL;
  const RegisterDesc *rd = S->get_march ()->get_register (regname);
  if (rd == NULL)
    PyErr_SetString (PyExc_LookupError, "unknown register");
  else 
    {
      void *st = S->get_state ();
      if (!S->check_register (st, rd)) 
	result = pynsight::None ();
      else
	result = Py_BuildValue ("s", S->get_register (rd).c_str ());
    }

  return result;
}

static PyObject *
s_Simulator_get_pc (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  PyObject *result = NULL;
  void *st = S->get_state ();
  if (st == NULL)
    result = pynsight::None ();
  else
    {
      MicrocodeAddress a = S->get_pc (st);
      result = Py_BuildValue ("(k,k)", a.getGlobal (), a.getLocal ());
      S->delete_state (st);
    }

  return result;
}

static PyObject *
s_Simulator_get_arrows (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  return pynsight::generic_generator_new (new ArrowsIterator (S));
}

/*****************************************************************************
 *
 * GenericInsightSimulator
 *
 *****************************************************************************/

GenericInsightSimulator::GenericInsightSimulator (Program *P, 
						  address_t start_addr)
{
  prg = P;
  Py_INCREF (P);
  start = start_addr;
  mc = new Microcode ();
  march = new MicrocodeArchitecture (P->loader->get_architecture ());
  decoder = new BinutilsDecoder (march, P->concrete_memory);
  arrows = new ArrowVector ();
}

GenericInsightSimulator::~GenericInsightSimulator ()
{
  Py_DECREF (prg);
  delete mc;
  delete march;
  delete decoder;
  delete arrows;
}

MicrocodeArchitecture *
GenericInsightSimulator::get_march () const
{
  return march;
}

void 
GenericInsightSimulator::clear_arrows ()
{
  arrows->clear ();
}

size_t 
GenericInsightSimulator::get_number_of_arrows () const
{
  return arrows->size ();
}

StmtArrow *
GenericInsightSimulator::get_arrow_at (size_t i) const
{
  assert (i < arrows->size ());
  return arrows->at (i);
}

/*****************************************************************************
 *
 * InsightSimulator<Stepper>
 *
 *****************************************************************************/

template <typename Stepper> 
InsightSimulator<Stepper>::InsightSimulator (Program *prg, address_t a)
  : GenericInsightSimulator (prg, a)
{
  stepper = new Stepper (prg->concrete_memory, march);
  current_state = NULL;
}

template <typename Stepper> 
InsightSimulator<Stepper>::~InsightSimulator ()
{
  delete stepper;
  if (current_state)
    current_state->deref ();
}

template <typename Stepper> string 
InsightSimulator<Stepper>::state_to_string (void *s) 
{
  return ((State *) s)->to_string ();
}

template <typename Stepper> void *
InsightSimulator<Stepper>::get_initial_state ()
{
  return stepper->get_initial_state (start);
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_state (void *ptr)
{ 
  if (current_state != NULL)
    current_state->deref ();
  current_state = (State *) ptr;
  current_state->ref ();
  clear_arrows ();
  compute_enabled_arrows (current_state, arrows);
}

template <typename Stepper> void 
InsightSimulator<Stepper>::delete_state (void *ptr)
{
  ((State *) ptr)->deref ();
}

template <typename Stepper> void * 
InsightSimulator<Stepper>::get_state ()
{
  current_state->ref ();
  return current_state;
}

template <typename Stepper> void * 
InsightSimulator<Stepper>::trigger_arrow (void *from, StmtArrow *a)
{
  State *result = NULL;
  try 
    {
      typename Stepper::StateSet *succs = 
	stepper->get_successors ((State *) from, a);
  
      if (succs->size () == 1)
	result = *(succs->begin ());
      else if (succs->size () != 0)
	PyErr_SetNone (pynsight::NotDeterministicBehaviorError);
      delete succs;
    }
  catch (UndefinedValueException &e)
    {
      PyErr_SetString (pynsight::UndefinedValueError, e.what ());
    }

  return result;
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_memory (address_t addr, uint8_t value) 
{
  typename Stepper::Value val (8, value);
  typename Stepper::Memory *mem = 
    current_state->get_Context ()->get_memory ();
  mem->put (addr, val, Architecture::LittleEndian);
}

template <typename Stepper> string 
InsightSimulator<Stepper>::get_memory (address_t addr) 
{
  typename Stepper::Memory *mem = 
    current_state->get_Context ()->get_memory ();
  return mem->get (addr, 1, Architecture::LittleEndian).to_string ();
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_register (const RegisterDesc *reg, word_t v)
{
  typename Stepper::Value val (reg->get_window_size (), v);
  typename Stepper::Memory *mem = 
    current_state->get_Context ()->get_memory ();
  const RegisterDesc *areg = march->get_register (reg->get_label ());

  if (val.get_size () != areg->get_register_size ())
    {
      typename Stepper::Value regval;

      if (mem->is_defined (areg))
	regval = mem->get (areg);
      else 
	regval = Stepper::Value::unknown_value (areg->get_register_size ());
      
      val = stepper->embed_eval (regval, val, reg->get_window_offset ());
    }     
  mem->put (areg, val);
}

template <typename Stepper> string 
InsightSimulator<Stepper>::get_register (const RegisterDesc *reg)
{
  typename Stepper::Memory *mem = 
    current_state->get_Context ()->get_memory ();
  const RegisterDesc *areg = march->get_register (reg->get_label ());
  assert (mem->is_defined (areg));
  typename Stepper::Value regval;

  if (reg->get_window_size () == areg->get_register_size ())
    regval = mem->get (areg);
  else
    {      
      Expr *tmp = Expr::createExtract (RegisterExpr::create (areg),
				       reg->get_window_offset (),
				       reg->get_window_size ());
      regval = stepper->eval (current_state->get_Context (), tmp);
      tmp->deref ();
    }     

  return regval.to_string ();
}

template <typename Stepper> bool 
InsightSimulator<Stepper>::check_memory_range (void *p, address_t addr, 
					       size_t len)
{
  State *s = (State *) p;
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
  
  while (len--)
    {
      if (!mem->is_defined (addr)) 
	return false;
      addr++;
    }
  return true;
}

template <typename Stepper> bool 
InsightSimulator<Stepper>::check_register (void *p, const RegisterDesc *reg)
{
  State *s = (State *) p;
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
  const RegisterDesc *areg = march->get_register (reg->get_label ());

  return mem->is_defined (areg);
}

template <typename Stepper> MicrocodeAddress 
InsightSimulator<Stepper>::get_pc (void *p)
{
  return ((State *) p)->get_ProgramPoint ()->to_MicrocodeAddress ();
}

template <typename Stepper> MicrocodeAddress 
InsightSimulator<Stepper>::get_current_pc ()
{
  return get_pc (current_state);
}

template <typename Stepper> void 
InsightSimulator<Stepper>::compute_enabled_arrows (State *s, 
						   ArrowVector *result) 
{
  typename Stepper::State *ns = (typename Stepper::State *) s;
  typename Stepper::ProgramPoint *pp = ns->get_ProgramPoint ();
  address_t addr = pp->to_MicrocodeAddress ().getGlobal ();

  if (! prg->concrete_memory->is_defined (addr))
    return;

  try 
    {
      MicrocodeNode *node = get_node (pp);
      MicrocodeNode_iterate_successors (*node, succ) {
	result->push_back (*succ);
      }
    }
  catch (Decoder::Exception &e)
    {
      logs::warning << "warning: decoder says at "
		    << pp->to_MicrocodeAddress () << ":"
		    << e.what () << std::endl;
    }  
}

template <typename Stepper> MicrocodeNode *
InsightSimulator<Stepper>::get_node (const ProgramPoint *pp) 
{
  MicrocodeAddress ma = pp->to_MicrocodeAddress ();
  bool is_global = (ma.getLocal () == 0);
  MicrocodeNode *result = NULL;

  try
    {
      result = mc->get_node (ma);

      if (is_global && ! result->has_annotation (AsmAnnotation::ID))
	{
	  // result is a node added by the decoder but asm instruction at
	  // pp.to_address () has not yet been decoded.
	  MicrocodeAddress addr = result->get_loc ();
	  assert (addr.getLocal () == 0);
	  ConcreteAddress next =decoder->decode (mc, addr.getGlobal ());
	  MicrocodeAddress nextma (next.get_address ());
	  result->add_annotation (NextInstAnnotation::ID,
				  new NextInstAnnotation (nextma));
	}
    }
  catch (GetNodeNotFoundExc &)
    {
      if (! is_global)
	throw;
      ConcreteAddress next = decoder->decode (mc, ma.getGlobal ());
      MicrocodeAddress nextma (next.get_address ());
      result = mc->get_node (ma);
      result->add_annotation (NextInstAnnotation::ID,
			      new NextInstAnnotation (nextma));
    }
    
  return result;
}

#if 0

static PyObject *
s_state_iterator (void *data)
{
  PyObject *result = NULL;
  vector<string> *states = ((vector<string> *) data);
  
  if (states->empty ())
    PyErr_SetNone (PyExc_StopIteration);
  else
    {
      string s = states->back ();
      states->pop_back ();
      result = Py_BuildValue ("s", s.c_str ());
    }

  return result;
}

static void 
s_delete_state_list (void *data)
{
  delete ((vector<string> *) data);
}

static PyObject *
s_Simulator_microstep (PyObject *p, PyObject *args)
{
  Simulator *S = (Simulator *) p;
  unsigned int aindex;

  if (! PyArg_ParseTuple (args, "I", &aindex))
    return NULL;
  
  if (aindex >= S->arrows->size ())
    {
      PyErr_SetString (PyExc_IndexError, "invalid microcode-arrow index");
      return NULL;
    }

  StmtArrow *a = S->arrows->at (aindex);
  void *s = S->states->at (0);
  vector<void*> *new_states = new vector<void*>;
  S->successors (S, s, a, new_states);
  s_clear_states (S, S->states);
  delete S->states;
  S->states = new_states;

  vector<string> *vs = new vector<string>;

  for (vector<void*>::iterator i = S->states->begin (); i != S->states->end (); 
       i++) 
    vs->push_back (S->state_to_string (*i));
 
  PyObject *result = 
    pynsight::generic_generator_new (s_state_iterator, vs, 
				     s_delete_state_list);
  return result;  
}

template <typename Stepper> void *
s_initial_state (void *stepper, address_t addr)
{
  return ((Stepper *) stepper)->get_initial_state (addr);
}

template <typename Stepper> void 
s_delete_state (void *s)
{
  ((typename Stepper::State *) s)->deref ();
}

template <typename Stepper> string
s_state_to_string (void *s)
{
  return ((typename Stepper::State *) s)->to_string ();
}

template <typename Stepper> void 
s_delete_stepper (void *s)
{
  delete (Stepper *) s;
}

template <typename Stepper> void 
s_successors (Simulator *S, void *s, StmtArrow *a, vector<void *> *result) 
{
  typename Stepper::State *ns = (typename Stepper::State *) s;
  typename Stepper::StateSet *succ = 
    ((Stepper *) S->stepper)->get_successors (ns, a);

  for (typename Stepper::StateSet::iterator i = succ->begin(); 
       i != succ->end ();  i++) 
    result->push_back (*i);

  delete succ;
}

template <typename Stepper> 
void 
s_init_simulator (Simulator *S, ConcreteMemory *mem)
{
  S->initial_state = s_initial_state<Stepper>;
  S->delete_stepper = s_delete_stepper<Stepper>;
  S->delete_state = s_delete_state<Stepper>;
  S->state_to_string = s_state_to_string<Stepper>;
  S->enabled_arrows = s_enabled_arrows<Stepper>;
  S->successors = s_successors<Stepper>;
  S->stepper = new Stepper (mem, S->march);
}
#endif

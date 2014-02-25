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
#include <io/expressions/expr-parser.hh>
#include <decoders/binutils/BinutilsDecoder.hh>

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/SymbolTable.hh>
#include <domains/concrete/ConcreteStepper.hh>
#include <domains/symbolic/SymbolicStepper.hh>

#include "gengen.hh"
#include "pynsight.hh"

using std::vector;
using std::list;
using std::string;
using pynsight::Program;

class GenericInsightSimulator;

class StopCondition : public Object 
{
public:
  StopCondition ();
  virtual ~StopCondition ();

  virtual int get_id () const;
  virtual bool stop (GenericInsightSimulator *S) = 0;
  virtual void output_text (std::ostream &out) const = 0;
  virtual bool equals (const StopCondition *other) const = 0;
  virtual void reset (GenericInsightSimulator *S);

private:
  static int last_id;
  int id;
};

class Breakpoint : public StopCondition
{
public:
  Breakpoint (MicrocodeAddress a);
  virtual ~Breakpoint ();

  virtual bool stop (GenericInsightSimulator *S);
  virtual void set_cond (const Expr *e);
  virtual void reset_cond ();
  virtual void output_text (std::ostream &out) const;
  virtual bool equals (const StopCondition *other) const;

private:
  MicrocodeAddress addr;
  Expr *cond;
};

class Watchpoint : public StopCondition
{
public:
  Watchpoint (const Expr *e);
  virtual ~Watchpoint ();

  virtual bool stop (GenericInsightSimulator *S);
  virtual void output_text (std::ostream &out) const;
  virtual bool equals (const StopCondition *other) const;
  virtual void reset (GenericInsightSimulator *S);

private:
  Expr *cond;
  bool last_value;
};

typedef std::set<StopCondition *> StopConditionSet;

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

  virtual const StopCondition *add_stop_condition (StopCondition *sc);
  virtual const StopConditionSet *get_stop_conditions () const;
  virtual StopCondition *get_stop_condition (int id) const;
  virtual const StopCondition *check_stop_conditions ();
  virtual void reset_stop_conditions ();
  virtual bool del_stop_condition (int id);

  virtual Option<bool> eval (const Expr *e) const = 0;

protected:
  Program *prg;  
  ConcreteAddress start;
  Decoder *decoder;
  Microcode *mc;
  MicrocodeArchitecture *march;
  ArrowVector *arrows;
  StopConditionSet *stop_conditions;
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

  virtual Option<bool> eval (const Expr *e) const;
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

static PyObject *
s_Simulator_get_breakpoints (PyObject *self, PyObject *);

static PyObject *
s_Simulator_add_breakpoint (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_set_cond (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_add_watchpoint (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_del_breakpoint (PyObject *self, PyObject *args);

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

static PyMethodDef SimulatorMethods[] = {
 { "run", s_Simulator_run, METH_NOARGS, 
   "\n" },
 { "microstep", s_Simulator_microstep, METH_VARARGS, 
   "\n" },
 { "step", s_Simulator_step, METH_VARARGS, 
   "\n" },
 { "print_state", s_Simulator_print_state, METH_NOARGS, 
   "\n" },
 { "set_memory", s_Simulator_set_memory, METH_VARARGS, 
   "\n" },
 { "set_register", s_Simulator_set_register, METH_VARARGS, 
   "\n" },
 { "get_memory", s_Simulator_get_memory, METH_VARARGS, 
   "\n" },
 { "get_register", s_Simulator_get_register, METH_VARARGS, 
   "\n" },
 { "get_pc", s_Simulator_get_pc, METH_NOARGS,
   "\n" },
 { "get_arrows", s_Simulator_get_arrows, METH_NOARGS,
   "\n" },
 { "get_breakpoints", s_Simulator_get_breakpoints, METH_NOARGS, 
   "\n" },
 { "add_breakpoint", s_Simulator_add_breakpoint, METH_VARARGS,
   "\n" }, 
 { "set_cond", s_Simulator_set_cond, METH_VARARGS,
   "\n" }, 
 { "add_watchpoint", s_Simulator_add_watchpoint, METH_VARARGS,
   "\n" }, 
 { "del_breakpoint", s_Simulator_del_breakpoint, METH_VARARGS,
   "\n" }, 
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

static PyObject *
s_Simulator_run (PyObject *p, PyObject *)
{  
  GenericInsightSimulator *S = ((Simulator *) p)->gsim;

  void *is = S->get_initial_state ();
  S->set_state (is);
  S->delete_state (is);
  S->reset_stop_conditions ();

  return pynsight::None ();
}

static PyObject *
s_StopConditionReached (const StopCondition *sc)
{
  if (PyErr_Occurred ())
    return NULL;
  if (sc != NULL)
    PyErr_SetObject (pynsight::BreakpointReached,
		     Py_BuildValue ("(k,s)",
				    sc->get_id (), sc->to_string ().c_str ()));
  return NULL;
}

static PyObject *
s_PyMicrocodeAddress (const MicrocodeAddress &addr)
{
  return Py_BuildValue ("(k,k)", addr.getGlobal (), addr.getLocal ());
}
  
static bool
s_trigger_arrow (GenericInsightSimulator *S, StmtArrow *a)
{
  void *st = S->get_state ();
  void *newst = S->trigger_arrow (st, a);

  if (newst != NULL)
    {
      S->set_state (newst); 

      if (S->get_number_of_arrows () == 0)
	{
	  MicrocodeAddress a = S->get_pc (st);
	  PyErr_SetObject (pynsight::SinkNodeReached, s_PyMicrocodeAddress (a));
	}
      else if (! PyErr_Occurred ()) 
	{
	  const StopCondition *bp = S->check_stop_conditions ();
	  if (bp != NULL)
	    s_StopConditionReached (bp);
	}
      S->delete_state (newst);
    }
  S->delete_state (st);

  return ! PyErr_Occurred ();
}

static bool 
s_trigger_arrow_from_index (GenericInsightSimulator *S, unsigned int aindex)
{
  if (aindex >= S->get_number_of_arrows ())
    {
      PyErr_SetString (PyExc_IndexError, "invalid microcode-arrow index");
      return false;
    }

  StmtArrow *a = S->get_arrow_at (aindex);

  return s_trigger_arrow (S, a);
}

static PyObject *
s_Simulator_microstep (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  unsigned int aindex = 0;

  if (! PyArg_ParseTuple (args, "I", &aindex))
    return NULL;
  
  PyObject *result = NULL;

  if (s_trigger_arrow_from_index (S, aindex))
    result = pynsight::None ();

  return result;  
}

static PyObject *
s_Simulator_step (PyObject *self, PyObject *args)
{  
  PyObject *result = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  MicrocodeAddress ep = S->get_current_pc ();
  int aindex = -1;

  if (! PyArg_ParseTuple (args, "|I", &aindex))
    return NULL;

  if (S->get_number_of_arrows () > 1)
    {
      if (aindex >= 0)
	{
	  if (! s_trigger_arrow_from_index (S, aindex))
	    return NULL;
	}
      else
	{
	  PyErr_SetNone (pynsight::NotDeterministicBehaviorError);
	  return NULL;
	}
    }
    
  while (ep.getGlobal () == S->get_current_pc ().getGlobal () &&
	 ! PyErr_Occurred ())
    {
      MicrocodeAddress tmp = S->get_current_pc ();
      if (S->get_number_of_arrows () > 1)
	{
	  PyErr_SetNone (pynsight::NotDeterministicBehaviorError);
	  return NULL;
	}

      if (S->get_number_of_arrows () == 0)
	{
	  PyErr_SetObject (pynsight::SinkNodeReached, 
			   s_PyMicrocodeAddress (ep));
	  return NULL;
	}
      s_trigger_arrow_from_index (S, 0);
    }

  if (! PyErr_Occurred ())
    result = pynsight::None ();

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

  try 
    {
      const RegisterDesc *rd = S->get_march ()->get_register (regname);
      S->set_register (rd, regval);
    }
  catch (Architecture::RegisterDescNotFound &e)
    {
      PyErr_SetString (PyExc_LookupError, "unknown register");
    }

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

  try 
    {
      const RegisterDesc *rd = S->get_march ()->get_register (regname);
      void *st = S->get_state ();
      if (!S->check_register (st, rd)) 
	result = pynsight::None ();
      else
	result = Py_BuildValue ("s", S->get_register (rd).c_str ());
    }
  catch (Architecture::RegisterDescNotFound &e) 
    {
      PyErr_SetString (PyExc_LookupError, "unknown register");
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
      result = s_PyMicrocodeAddress (a);
      S->delete_state (st);
    }

  return result;
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
	std::ostringstream oss;
	StmtArrow *a = gsim->get_arrow_at (current);
	current++;
	Expr *guard = a->get_condition ();
	if (guard)
	  {
	    if (guard->is_Constant())
	      {
		Constant *c = (Constant *) guard;
		if (c->get_val() != 1)
		  oss << "<< False >> ";
	      }
	    else
	      {
		oss << "<< "<<  *guard << " >> ";
	      }
	  }
	
	oss << a->get_stmt()->pp ();
	if (a->is_static ())
	  {
	    oss << " -> " << 
	      dynamic_cast<const StaticArrow *>(a)->get_target ();
	  }

	result = Py_BuildValue ("s", oss.str ().c_str ());
      }

    return result;
  } 
};

static PyObject *
s_Simulator_get_arrows (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  return pynsight::generic_generator_new (new ArrowsIterator (S));
}

class StopConditionsIterator : public pynsight::GenericGenerator
{
private:
  GenericInsightSimulator *gsim;
  StopConditionSet::const_iterator current;
public:
  StopConditionsIterator (GenericInsightSimulator *gsim) 
    : gsim (gsim), current (gsim->get_stop_conditions ()->begin ()) { }

  virtual ~StopConditionsIterator () { }

  PyObject *next () {
    PyObject *result = NULL;
    if (current == gsim->get_stop_conditions ()->end ())
      PyErr_SetNone (PyExc_StopIteration);
    else
      {
	result = Py_BuildValue ("(k, s)", (*current)->get_id (),
				(*current)->to_string ().c_str ());
	current++;
      }

    return result;
  } 
};

static PyObject *
s_Simulator_get_breakpoints (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  return pynsight::generic_generator_new (new StopConditionsIterator (S));

}

static PyObject *
s_Simulator_add_breakpoint (PyObject *self, PyObject *args)
{
  unsigned long gaddr = 0;
  unsigned long laddr = 0;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! PyArg_ParseTuple (args, "k|k", &gaddr, &laddr))
    return NULL;

  PyObject *result = NULL;
  MicrocodeAddress a (gaddr, laddr);
  StopCondition *newbp = new Breakpoint (a);

  const StopCondition *bp = S->add_stop_condition (newbp);
  if (bp == NULL)
    result = pynsight::None ();
  else
    result = Py_BuildValue ("(k,s)", bp->get_id (), bp->to_string ().c_str ());

  return result;
}

static PyObject *
s_Simulator_set_cond (PyObject *self, PyObject *args)
{
  unsigned long id = -1;
  const char *condition = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! PyArg_ParseTuple (args, "k|s", &id, &condition))
    return NULL;

  PyObject *result = NULL;
  Breakpoint *bp = dynamic_cast<Breakpoint *> (S->get_stop_condition (id));
  if (bp == NULL)
    return pynsight::None ();

  if (condition == NULL)
    bp->reset_cond ();
  else
    {
      Expr *e = expr_parser (condition, S->get_march ()); 
      bp->set_cond (e);
      e->deref ();
    }

  result = Py_BuildValue ("(k,s)", bp->get_id (), bp->to_string ().c_str ());

  return result;
}

static PyObject *
s_Simulator_add_watchpoint (PyObject *self, PyObject *args)
{
  const char *condition = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! PyArg_ParseTuple (args, "s", &condition))
    return NULL;

  PyObject *result = NULL;
  Expr *cond = expr_parser (condition, S->get_march ());
  StopCondition *newwp = new Watchpoint (cond);
  cond->deref ();

  const StopCondition *wp = S->add_stop_condition (newwp);
  if (wp == NULL)
    result = pynsight::None ();
  else
    result = Py_BuildValue ("(k,s)", wp->get_id (), wp->to_string ().c_str ());

  return result;
}

static PyObject *
s_Simulator_del_breakpoint (PyObject *self, PyObject *args)
{
  unsigned long id = 0;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! PyArg_ParseTuple (args, "k", &id))
    return NULL;

  if (S->del_stop_condition (id))
    return Py_BuildValue ("i", 1);
  else
    return pynsight::None ();
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
  stop_conditions = new StopConditionSet;
  if (prg->stubfactory)
    prg->stubfactory->add_stubs (prg->concrete_memory, march, mc, 
				 prg->symbol_table);
}

GenericInsightSimulator::~GenericInsightSimulator ()
{
  Py_DECREF (prg);
  delete mc;
  delete march;
  delete decoder;
  delete arrows;
  for (StopConditionSet::iterator i = stop_conditions->begin (); 
       i != stop_conditions->end (); i++) {
    delete (*i);
  }

  delete stop_conditions;
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

const StopCondition * 
GenericInsightSimulator::add_stop_condition (StopCondition *sc)
{
  const StopCondition *result = NULL;

  for (StopConditionSet::iterator i = stop_conditions->begin (); 
       i != stop_conditions->end () && result == NULL; i++) {
    if (sc->equals (*i))
      result = *i;
  }
  stop_conditions->insert (sc);

  return result;
}

const StopConditionSet *
GenericInsightSimulator::get_stop_conditions () const
{
  return stop_conditions;
}

StopCondition *
GenericInsightSimulator::get_stop_condition (int id) const
{
  StopCondition *result = NULL;

  for (StopConditionSet::iterator i = stop_conditions->begin (); 
       i != stop_conditions->end () && result == NULL; i++) {
    if ((*i)->get_id () == id)
      result = (*i);
  }

  return result;
}

const StopCondition *
GenericInsightSimulator::check_stop_conditions ()
{
  const StopCondition *result = NULL;

  for (StopConditionSet::iterator i = stop_conditions->begin (); 
       i != stop_conditions->end () && result == NULL; i++) {
    if ((*i)->stop(this))
      result = (*i);
  }

  return result;
}

void 
GenericInsightSimulator::reset_stop_conditions ()
{
  for (StopConditionSet::iterator i = stop_conditions->begin (); 
       i != stop_conditions->end (); i++) 
    (*i)->reset (this);
}

bool 
GenericInsightSimulator::del_stop_condition (int id)
{
  for (StopConditionSet::iterator i = stop_conditions->begin (); 
       i != stop_conditions->end (); i++) {
    if ((*i)->get_id () == id)
      {
	stop_conditions->erase (i);
	return true;
      }
  }
  return false;
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
	{
	  result = *(succs->begin ());
	  MicrocodeAddress tgt = 
	    result->get_ProgramPoint ()->to_MicrocodeAddress ();
	  if (! check_memory_range (from, tgt.getGlobal (), 1))
	    {
	      PyErr_SetObject (pynsight::JumpToInvalidAddress,
			       s_PyMicrocodeAddress (tgt));
	      result = NULL;
	    }
	}
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

template <typename Stepper> Option<bool> 
InsightSimulator<Stepper>::eval (const Expr *e) const
{
  typename Stepper::Value val = 
    stepper->eval (((State *) current_state)->get_Context (), e);
  return val.to_bool ();
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
      MicrocodeNode_iterate_successors (*node, pa) {	
	typename Stepper::StateSet *succs = NULL;
	try 
	  {
	    succs = stepper->get_successors (ns, *pa);
	  }
	catch (UndefinedValueException e) { }
	if (succs == NULL || succs->size () > 0)
	  result->push_back (*pa);
	if (succs)
	  delete succs;
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

/******************************************************************************
 *
 * STOP CONDITIONS
 *
 ******************************************************************************/

int StopCondition::last_id = 1;

StopCondition::StopCondition () : id (last_id++) 
{
}

StopCondition::~StopCondition ()
{
}

int 
StopCondition::get_id () const 
{
  return id;
}

void
StopCondition::reset (GenericInsightSimulator *)
{
}

Breakpoint::Breakpoint (MicrocodeAddress a) 
  : StopCondition (), addr (a), cond (NULL)
{
}

Breakpoint::~Breakpoint ()
{
  if (cond != NULL)
    cond->deref ();
}

bool 
Breakpoint::stop (GenericInsightSimulator *S)
{
  MicrocodeAddress pc = S->get_current_pc ();

  if (! pc.equals (addr))
    return false;

  if (cond == NULL)
    return true;

  Option<bool> val = S->eval (cond);
  return ! val.hasValue () || val.getValue ();
}

void 
Breakpoint::set_cond (const Expr *e)
{
  assert (e != NULL);
  reset_cond ();
  cond = e->ref ();
}

void 
Breakpoint::reset_cond ()
{
  if (cond != NULL)
    cond->deref ();
  cond = NULL;
}

void 
Breakpoint::output_text (std::ostream &out) const 
{
  out << "breakpoint: " << addr;
  if (cond != NULL)
    {
      out << " cond = ";
      cond->output_text (out);
    }
}

bool 
Breakpoint::equals (const StopCondition *other) const
{
  const Breakpoint *bp = dynamic_cast<const Breakpoint *> (other);

  return bp != NULL && bp->cond == cond && bp->addr.equals (addr);
}

Watchpoint::Watchpoint (const Expr *e) 
  : StopCondition (), cond (e->ref ()), last_value ()
{
}

Watchpoint::~Watchpoint ()
{
  cond->deref ();
}

bool 
Watchpoint::stop (GenericInsightSimulator *S)
{
  Option<bool> oval = S->eval (cond);
  bool val = ! oval.hasValue () || oval.getValue ();
  bool result = (val != last_value);
  
  if (result)
    last_value = val;
  return result;
}

void 
Watchpoint::output_text (std::ostream &out) const 
{
  out << "watchpoint: expr = ";
  cond->output_text (out);
}

bool 
Watchpoint::equals (const StopCondition *other) const
{
  const Watchpoint *wp = dynamic_cast<const Watchpoint *> (other);

  return wp != NULL && wp->cond == cond;
}

void
Watchpoint::reset (GenericInsightSimulator *S) 
{
  Option<bool> oval = S->eval (cond);
  last_value = ! oval.hasValue () || oval.getValue ();
}

/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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
#include <fstream>
#include <kernel/annotations/AsmAnnotation.hh>
#include <kernel/annotations/StubAnnotation.hh>
#include <kernel/annotations/NextInstAnnotation.hh>
#include <domains/concrete/ConcreteMemory.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <io/expressions/expr-parser.hh>
#include <decoders/binutils/BinutilsDecoder.hh>
#include <utils/tools.hh>

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/SymbolTable.hh>
#include <domains/concrete/ConcreteStepper.hh>
#include <domains/symbolic/SymbolicStepper.hh>
#include <io/microcode/xml_microcode_parser.hh>
#include <io/microcode/xml_microcode_generator.hh>

#include "gengen.hh"
#include "pynsight.hh"

using std::vector;
using std::list;
using std::string;
using std::map;
using pynsight::Program;
using pynsight::GenericGenerator;

class GenericInsightSimulator;

class CodeChangedException : public std::runtime_error {
public:
  CodeChangedException (address_t where) 
    : std::runtime_error (""), addr (where) {
  }

  address_t where () { return addr; }
private:
  address_t addr;
};

class StopCondition : public Object 
{
public:
  StopCondition ();
  virtual ~StopCondition ();

  virtual int get_id () const;
  virtual size_t get_number_of_hits () const;
  virtual bool stop (GenericInsightSimulator *S) = 0;
  virtual void output_text (std::ostream &out) const = 0;
  virtual bool equals (const StopCondition *other) const = 0;
  virtual void reset (GenericInsightSimulator *S);
  virtual void hit ();

private:
  static int last_id;
  int id;
  size_t hits;
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

class PyWatchpoint : public StopCondition
{
public:
  PyWatchpoint (PyObject *callable);
  virtual ~PyWatchpoint ();

  virtual bool stop (GenericInsightSimulator *S);
  virtual void output_text (std::ostream &out) const;
  virtual bool equals (const StopCondition *other) const;
  virtual void reset (GenericInsightSimulator *S);

private:
  PyObject *cb;
};

typedef std::set<StopCondition *> StopConditionSet;

struct CmpMicrocodeAddress
{
  bool operator() (const MicrocodeAddress &a1, const MicrocodeAddress &a2) const
  {
    return a1.lessThan (a2);
  }
};

class GenericInsightSimulator : public pynsight::MicrocodeReference {
public:
  typedef vector<StmtArrow *> ArrowVector;
  typedef map<MicrocodeAddress,Expr *,CmpMicrocodeAddress> AssumptionMap;

  class NoStateException { };

  GenericInsightSimulator (Program *prg);

  virtual ~GenericInsightSimulator ();

  virtual MicrocodeArchitecture *get_march () const;
  virtual const Microcode *get_microcode () const;
  virtual Program *get_program () const;

  virtual void clear_arrows ();
  virtual size_t get_number_of_arrows () const;
  virtual StmtArrow *get_arrow_at (size_t i) const;

  virtual string state_to_string (void *s) = 0;
  virtual void *get_initial_state (address_t start) = 0;
  virtual void set_state (void *s) throw (CodeChangedException) = 0;
  virtual void delete_state (void *s) = 0;

  virtual bool has_state () = 0;
  virtual void *get_state () = 0;

  virtual void *trigger_arrow (void *from, StmtArrow *a) = 0;

  virtual string get_memory (address_t addr);
  virtual string get_memory (void *p, address_t addr) = 0;
  virtual bool check_memory_range (address_t addr, size_t len);
  virtual bool check_memory_range (void *s, address_t addr, size_t len) = 0;

  virtual bool abstract_memory (address_t addr, size_t len, bool keep_in_ctx);
  virtual void *abstract_memory (void *p, address_t addr, size_t len, 
				 bool keep_in_ctx) = 0;

  virtual bool concretize_memory (address_t addr, size_t len);
  virtual bool concretize_memory (address_t addr, const ConcreteValue *values, 
				  size_t len);
  virtual void *concretize_memory (void *s, address_t addr, size_t len) = 0;
  virtual void *concretize_memory (void *s, address_t addr, 
				   const ConcreteValue *values,
				   size_t len) = 0;

  virtual string get_register (const RegisterDesc *reg);
  virtual string get_register (void *p, const RegisterDesc *reg) = 0;
  virtual bool check_register (const RegisterDesc *reg);
  virtual bool check_register (void *s, const RegisterDesc *reg) = 0;

  virtual bool abstract_register (const RegisterDesc *reg, bool keep_in_ctx);
  virtual void *abstract_register (void *p, const RegisterDesc *reg, 
				   bool keep_in_ctx) = 0;

  virtual bool concretize_register (const RegisterDesc *reg);
  virtual bool concretize_register (const RegisterDesc *reg, 
				    const ConcreteValue &v);
  virtual void *concretize_register (void *s, const RegisterDesc *reg) = 0;
  virtual void *concretize_register (void *s, const RegisterDesc *reg, 
				     const ConcreteValue &v) = 0;

  virtual MicrocodeAddress get_pc (void *s) = 0;
  virtual MicrocodeAddress get_pc () = 0;

  virtual const StopCondition *add_stop_condition (StopCondition *sc);
  virtual const StopConditionSet *get_stop_conditions () const;
  virtual StopCondition *get_stop_condition (int id) const;
  virtual const StopCondition *check_stop_conditions ();
  virtual void reset_stop_conditions ();
  virtual bool del_stop_condition (int id);

  virtual Option<ConcreteValue> eval (const Expr *e) const = 0;
  virtual Option<bool> eval_condition (const Expr *e) const = 0;
  virtual Option<string> get_instruction (address_t addr);

  virtual bool load_stub (const string &filename, address_t shift,
			  bool fold = false);
  virtual bool load_microcode (const string &filename);
  virtual bool save_microcode (const string &filename);

  virtual void *assume (void *p, const Expr *e) const = 0;
  virtual bool assume (const Expr *e);
  virtual void add_assumption (const MicrocodeAddress &ma, const Expr *e);
  virtual bool apply_assumption ();
  virtual bool detach_assumption (const MicrocodeAddress &addr);
  virtual const AssumptionMap &get_assumptions () const;

  virtual void set_compare_state (bool set) = 0;
  virtual GenericGenerator *compare_states () const = 0;
  virtual GenericGenerator *compare_states (void *s1, void *s2) const = 0;

protected:
  Program *prg;  
  Microcode *mc;
  MicrocodeArchitecture *march;
  ArrowVector *arrows;
  StopConditionSet *stop_conditions;
  AssumptionMap assumptions;
};

template <typename Stepper>
class InsightSimulator : public GenericInsightSimulator, public UnknownValueGenerator<typename Stepper::Value> {
public:
  typedef typename Stepper::State State;
  typedef typename Stepper::Memory Memory;
  typedef typename Stepper::Value Value;
  typedef typename Stepper::ProgramPoint ProgramPoint;

  InsightSimulator (Program *prg);
  virtual ~InsightSimulator ();

  virtual string state_to_string (void *s);
  virtual void *get_initial_state (address_t start);
  virtual void set_state (void *ptr) throw (CodeChangedException);
  virtual void delete_state (void *ptr);

  virtual bool has_state ();
  virtual void *get_state ();
  virtual void *trigger_arrow (void *from, StmtArrow *a);

  virtual void set_memory (void *p, address_t addr, const Value &value);
  virtual void set_memory (void *p, address_t addr, uint8_t value);
  virtual string get_memory (void *p, address_t addr);
  virtual Value get_memory_value (void *p, address_t addr);
  virtual bool check_memory_range (void *s, address_t addr, size_t len);
  virtual void *abstract_memory (void *p, address_t addr, size_t len, 
				 bool keep_in_ctx);
  virtual void *concretize_memory (void *s, address_t addr, size_t len);
  virtual void *concretize_memory (void *s, address_t addr, 
				   const ConcreteValue *values,
				   size_t len);

  virtual void set_register (void *p, const RegisterDesc *reg, 
			     const Value &value);
  virtual void set_register (void *p, const RegisterDesc *reg, word_t value);
  virtual string get_register (void *p, const RegisterDesc *reg);
  virtual Value get_register_value (void *p, const RegisterDesc *reg);
  virtual bool check_register (void *s, const RegisterDesc *reg);

  virtual void* abstract_register (void *p, const RegisterDesc *reg, 
				  bool keep_in_ctx);
  virtual void *concretize_register (void *s, const RegisterDesc *reg);
  virtual void *concretize_register (void *s, const RegisterDesc *reg, 
				     const ConcreteValue &v);

  virtual MicrocodeAddress get_pc (void *s);
  virtual MicrocodeAddress get_pc ();

  virtual Option<ConcreteValue> eval (const Expr *e) const;
  virtual Option<bool> eval_condition (const Expr *e) const;
  virtual Stepper *get_stepper ();

  virtual void *assume (void *p, const Expr *e) const;

  virtual void set_compare_state (bool set);
  virtual GenericGenerator *compare_states () const;
  virtual GenericGenerator *compare_states (void *s1, void *s2) const;

  virtual Value unknown_value (int size);

protected:  
  Stepper *stepper;
  State *current_state;
  State *ref_state;
  BinutilsDecoder *decoder;
  int in_abstraction;

private:
  void compute_enabled_arrows (State *s, ArrowVector *result)
    throw (CodeChangedException);
  MicrocodeNode *get_node (const ProgramPoint *pp)
    throw (CodeChangedException);
};

template <typename Stepper>
class RawBytesReader : public Decoder::RawBytesReader 
{
public:  
  RawBytesReader (InsightSimulator<Stepper> *simulator);
  virtual ~RawBytesReader ();


  virtual void read_buffer (address_t from, uint8_t *dest, size_t length)
    throw (Decoder::Exception);
  
private:
  InsightSimulator<Stepper> *simulator;
};

struct Simulator {
  PyObject_HEAD
  GenericInsightSimulator *gsim;
};

class AbstractCodeException : public Decoder::Exception 
{
public:
  AbstractCodeException (address_t addr) 
    : Decoder::Exception (itos (addr)) {}
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
s_Simulator_state (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_set_memory (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_unset_memory (PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
s_Simulator_concretize_memory (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_get_memory (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_set_register (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_unset_register (PyObject *self, PyObject *args, PyObject *kwds);

static PyObject *
s_Simulator_get_register (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_concretize_register (PyObject *self, PyObject *args);

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
s_Simulator_add_pywatchpoint (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_del_breakpoint (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_eval (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_get_microcode (PyObject *self, PyObject *);

static PyObject *
s_Simulator_get_instruction (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_load_mc (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_save_mc (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_load_stub (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_assume (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_remove_assumption (PyObject *self, PyObject *args);

static PyObject *
s_Simulator_get_assumptions (PyObject *self, PyObject *);

static PyObject *
s_Simulator_set_compare_state (PyObject *self, PyObject *arg);

static PyObject *
s_Simulator_unset_compare_state (PyObject *self, PyObject *);

static PyObject *
s_Simulator_compare_states (PyObject *self, PyObject *);

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
 { "run", s_Simulator_run, METH_VARARGS, 
   "\n" },
 { "microstep", s_Simulator_microstep, METH_VARARGS, 
   "\n" },
 { "step", s_Simulator_step, METH_VARARGS, 
   "\n" },
 { "state", s_Simulator_state, METH_NOARGS, 
   "\n" },
 { "set_memory", s_Simulator_set_memory, METH_VARARGS, 
   "\n" },
 { "unset_memory", 
   (PyCFunction) s_Simulator_unset_memory, METH_VARARGS|METH_KEYWORDS,
   "\n" },
 { "get_memory", s_Simulator_get_memory, METH_VARARGS, 
   "\n" },
 { "concretize_memory", s_Simulator_concretize_memory, METH_VARARGS,
   "\n" }, 
 { "set_register", s_Simulator_set_register, METH_VARARGS, 
   "\n" },
 { "unset_register", 
   (PyCFunction) s_Simulator_unset_register, METH_VARARGS|METH_KEYWORDS, 
   "\n" },
 { "get_register", s_Simulator_get_register, METH_VARARGS, 
   "\n" },
 { "concretize_register", s_Simulator_concretize_register, METH_VARARGS,
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
 { "add_pywatchpoint", s_Simulator_add_pywatchpoint, METH_VARARGS,
   "\n" }, 
 { "del_breakpoint", s_Simulator_del_breakpoint, METH_VARARGS,
   "\n" }, 
 { "eval", s_Simulator_eval, METH_VARARGS,
   "\n" }, 
 { "get_microcode", s_Simulator_get_microcode, METH_NOARGS,
   "\n" }, 
 { "get_instruction", s_Simulator_get_instruction, METH_VARARGS,
   "\n" }, 
 { "load_mc", s_Simulator_load_mc, METH_VARARGS,
   "\n" }, 
 { "save_mc", s_Simulator_save_mc, METH_VARARGS,
   "\n" }, 
 { "load_stub", s_Simulator_load_stub, METH_VARARGS, "\n" }, 
 { "assume", s_Simulator_assume, METH_VARARGS, "\n" }, 
 { "remove_assumption", s_Simulator_remove_assumption, METH_VARARGS, "\n" }, 
 { "get_assumptions", s_Simulator_get_assumptions, METH_NOARGS, "\n" }, 
 { "set_compare_state", s_Simulator_set_compare_state, METH_NOARGS, "\n" }, 
 { "unset_compare_state", s_Simulator_unset_compare_state, METH_NOARGS, "\n" },
 { "compare_states", s_Simulator_compare_states, METH_NOARGS, "\n" }, 
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
pynsight::simulator (Program *P, SimulationDomain dom)
{
  Simulator *S = PyObject_New (Simulator, &SimulatorType);

  if (S == NULL)
    return NULL;

  PyObject_Init ((PyObject *) S, &SimulatorType);

  if (dom == pynsight::SIM_SYMBOLIC)
    S->gsim = new InsightSimulator<SymbolicStepper> (P);
  else 
    {
      assert (dom == pynsight::SIM_CONCRETE);
      S->gsim = new InsightSimulator<ConcreteStepper> (P);
    }

  return (PyObject *) S;
}

static void
s_Simulator_dealloc (PyObject *obj) 
{
  Simulator *S = (Simulator *) obj;
  delete S->gsim;
  S->ob_type->tp_free (S);
}

static PyObject *
s_PyMicrocodeAddress (const MicrocodeAddress &addr)
{
  return Py_BuildValue ("(k,k)", addr.getGlobal (), addr.getLocal ());
}
  
static void
s_CodeChangedException (CodeChangedException &e)
{
  PyObject *ma = s_PyMicrocodeAddress (e.where ());
  PyErr_SetObject (pynsight::CodeChangedException, ma);
}

static PyObject *
s_Simulator_run (PyObject *p, PyObject *args)
{  
  GenericInsightSimulator *S = ((Simulator *) p)->gsim;
  unsigned long start;

  if (! PyArg_ParseTuple (args, "k", &start))
    {
      PyErr_Clear ();
      if (! PyArg_ParseTuple (args, "", args))
	return NULL;
      start = S->get_program ()->loader->get_entrypoint ().get_address ();
    }    
    
  address_t s,e;

  S->get_program ()->concrete_memory->get_address_range (s, e);
  if (! (s <= start && start <= e)) {    
    PyErr_SetString (PyExc_LookupError, "start address is out of memory");
    return NULL;
  }

  S->set_compare_state (false);

  PyObject *result = NULL;
  void *is = S->get_initial_state (start);
  try
    {
      S->set_state (is);
      S->reset_stop_conditions ();
      result = pynsight::None ();
    }
  catch (CodeChangedException &e)
    {
      s_CodeChangedException (e);
    }
  S->delete_state (is);

  return result;
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

static bool
s_check_state (GenericInsightSimulator *S)
{
  if (! S->has_state ())
    {
      PyErr_SetNone (pynsight::SimulationNotStartedException);
      return false;
    }
  return true;
}

static bool
s_trigger_arrow (GenericInsightSimulator *S, StmtArrow *a)
{
  void *st = S->get_state ();
  void *newst = S->trigger_arrow (st, a);

  if (newst != NULL)
    {
      try {
	S->set_state (newst); 	

	if (S->get_number_of_arrows () == 0)
	  {
	    MicrocodeAddress a = S->get_pc (st);
	    PyErr_SetObject (pynsight::SinkNodeReached, 
			     s_PyMicrocodeAddress (a));
	  }
	else if (! PyErr_Occurred ()) 
	  {
	    if (S->apply_assumption ())
	      {
		const StopCondition *bp = S->check_stop_conditions ();
		if (bp != NULL)
		  s_StopConditionReached (bp);
	      }
	  }
      } catch (CodeChangedException &e) {
	s_CodeChangedException (e);
      }

      S->delete_state (newst);
    }
  S->delete_state (st);

  return ! PyErr_Occurred ();
}

static bool 
s_trigger_arrow_from_index (GenericInsightSimulator *S, unsigned int aindex)
  
{
  bool result = false;
  if (aindex >= S->get_number_of_arrows ())
    PyErr_SetString (PyExc_IndexError, "invalid microcode-arrow index");
  else if (s_check_state (S))
    {
      StmtArrow *a = S->get_arrow_at (aindex);
      result = s_trigger_arrow (S, a);
    }
  return result;
}

static PyObject *
s_Simulator_microstep (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  unsigned int aindex = 0;

  if (! s_check_state (S) || ! PyArg_ParseTuple (args, "I", &aindex))
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
  MicrocodeAddress ep = S->get_pc ();
  int aindex = -1;

  if (! s_check_state (S) || ! PyArg_ParseTuple (args, "|I", &aindex))
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
    
  while (ep.getGlobal () == S->get_pc ().getGlobal () &&
	 ! PyErr_Occurred ())
    {
      MicrocodeAddress tmp = S->get_pc ();
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
s_Simulator_state (PyObject *self, PyObject *)
{
  PyObject *result;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! S->has_state ())
    result = pynsight::None ();
  else
    {
      void *s = S->get_state ();
      string sstr = S->state_to_string (s);
      result = Py_BuildValue ("s", sstr.c_str ());
      S->delete_state (s);
    }			    

  return result;
}

static PyObject *
s_Simulator_set_memory (PyObject *self, PyObject *args)
{
  Py_ssize_t addr;
  unsigned char byte;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (! s_check_state (S) || ! PyArg_ParseTuple (args, "kb", &addr, &byte))
    return NULL;

  ConcreteValue v (8, byte);
  if (! S->concretize_memory (addr, &v, 1))
    {
      PyErr_SetNone (pynsight::ConcretizationException);
      return NULL;
    }

  return pynsight::None ();
}

static PyObject *
s_Simulator_unset_memory (PyObject *self, PyObject *args, PyObject *kwds)
{
  static const char *kwlists[] = { "addr", "len", "keep", NULL };
  Py_ssize_t addr;
  Py_ssize_t len;
  unsigned char keep;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (! s_check_state (S) || 
      !PyArg_ParseTupleAndKeywords (args, kwds, "kkb", (char **) kwlists,
				    &addr, &len, &keep))
    return NULL;
  PyObject *result = NULL;
  if (S->check_memory_range (addr, len)) 
    {
      if (! S->abstract_memory (addr, len, keep))
	PyErr_SetNone (PyExc_NotImplementedError);
      else 
	result = pynsight::None ();    
    }
  else
    {
      PyErr_SetString (PyExc_IndexError, "memory range out of bounds");
    }

  return result;
}

static PyObject *
s_Simulator_get_memory (PyObject *self, PyObject *args)
{
  unsigned long addr;
  unsigned long len = 1;
  PyObject *result = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (! s_check_state (S) || !PyArg_ParseTuple (args, "k|k", &addr, &len))
    return NULL;

  if (S->check_memory_range (addr, len)) 
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

  return result;
}

static PyObject *
s_Simulator_concretize_memory (PyObject *self, PyObject *args)
{
  unsigned long addr;
  unsigned long len = 1;
  PyObject *result = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (! s_check_state (S) || !PyArg_ParseTuple (args, "k|k", &addr, &len))
    return NULL;

  if (! S->check_memory_range (addr, len)) 
    PyErr_SetString (PyExc_IndexError, "memory range out of bounds");
  else if (! S->concretize_memory (addr, len))
    PyErr_SetNone (pynsight::ConcretizationException);
  else
    result = pynsight::True ();

  return result;
}

static PyObject *
s_Simulator_set_register (PyObject *self, PyObject *args)
{
  const char *regname;
  unsigned long regval;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (! s_check_state (S) || !PyArg_ParseTuple (args, "sk", &regname, &regval))
    return NULL;

  try 
    {
      const RegisterDesc *rd = S->get_march ()->get_register (regname);
      ConcreteValue v (rd->get_window_size (), regval);

      if (! S->concretize_register (rd, v))
	{
	  PyErr_SetNone (pynsight::ConcretizationException);
	  return NULL;
	}
    }
  catch (Architecture::RegisterDescNotFound &e)
    {
      PyErr_SetString (PyExc_LookupError, "unknown register");
    }

  return pynsight::None ();
}

static PyObject *
s_Simulator_unset_register (PyObject *self, PyObject *args, PyObject *kwds)
{
  static const char *kwlists[] = { "reg", "keep", NULL };
  const char *regname = NULL;
  unsigned char keep;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  
  if (! s_check_state (S) || 
      !PyArg_ParseTupleAndKeywords (args, kwds, "sb", (char **) kwlists,
				    &regname, &keep))
    return NULL;

  PyObject *result= NULL;
  try 
    {
      const RegisterDesc *rd = S->get_march ()->get_register (regname);
      if (! S->abstract_register (rd, keep))
	PyErr_SetNone (PyExc_NotImplementedError);
      else
	result = pynsight::None ();
    }
  catch (Architecture::RegisterDescNotFound &e) 
    {
      PyErr_SetString (PyExc_LookupError, "unknown register");
    }

  return result;
}

static PyObject *
s_Simulator_get_register (PyObject *self, PyObject *args)
{
  const char *regname;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! s_check_state (S) || !PyArg_ParseTuple (args, "s", &regname))
    return NULL;

  PyObject *result = NULL;

  try 
    {
      const RegisterDesc *rd = S->get_march ()->get_register (regname);
      if (!S->check_register (rd)) 
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
s_Simulator_concretize_register (PyObject *self, PyObject *args)
{
  const char *regname;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! s_check_state (S) || !PyArg_ParseTuple (args, "s", &regname))
    return NULL;

  PyObject *result = NULL;

  try 
    {
      const RegisterDesc *rd = S->get_march ()->get_register (regname);

      if (! S->check_register (rd))
	result = pynsight::None ();
      else if (S->concretize_register (rd))
	result = pynsight::True ();
      else 
	PyErr_SetNone (pynsight::ConcretizationException);
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
  PyObject *result = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim; 

  if (s_check_state (S))
    {
      MicrocodeAddress a = S->get_pc ();
      result = s_PyMicrocodeAddress (a);
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
	result = Py_BuildValue ("(k, k, s)", (*current)->get_id (),
				(*current)->get_number_of_hits (),
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

  S->add_stop_condition (newbp);
  result = Py_BuildValue ("(k,s)", newbp->get_id (), 
			  newbp->to_string ().c_str ());

  return result;
}

static PyObject *
s_Simulator_set_cond (PyObject *self, PyObject *args)
{
  unsigned long id = -1;
  const char *condition = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! PyArg_ParseTuple (args, "k|z", &id, &condition))
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
      if (e == NULL)
	{
	  PyErr_SetString(PyExc_SyntaxError, "syntax error");
	  
	  return NULL;
	}
      else
	{
	  bp->set_cond (e);
	  e->deref ();
	}
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
s_Simulator_add_pywatchpoint (PyObject *self, PyObject *args)
{
  PyObject *callable = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! PyArg_ParseTuple (args, "O", &callable))
    return NULL;
  assert (PyCallable_Check (callable));

  PyObject *result = NULL;
  StopCondition *newwp = new PyWatchpoint (callable);

  const StopCondition *wp = S->add_stop_condition (newwp);
  if (wp == NULL)
    result = pynsight::None ();
  else
    result = Py_BuildValue ("(k,s)", wp->get_id (), wp->to_string ().c_str ());
  Py_DECREF (callable);

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

static PyObject *
s_Simulator_eval (PyObject *self, PyObject *args)
{
  const char *condition = NULL;
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  if (! PyArg_ParseTuple (args, "s", &condition))
    return NULL;

  PyObject *result = NULL;
  Expr *expr = expr_parser (condition, S->get_march ());
  if (expr == NULL)
    {
      PyErr_SetString(PyExc_SyntaxError, "syntax error");

      return NULL;
    }
  Option<ConcreteValue> cv = S->eval (expr);
  expr->deref ();

  if (cv.hasValue ())
    result = Py_BuildValue ("k", cv.getValue ().get ());
  else
    result = pynsight::None ();

  return result;
}

PyObject *
s_Simulator_get_microcode (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  return pynsight::microcode_object (S->get_program (), S);
}

PyObject *
s_Simulator_get_instruction (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  unsigned long addr;

  if (! PyArg_ParseTuple (args, "k", &addr))
    return NULL;
  Option<string> instr = S->get_instruction (addr);

  PyObject *result;
  if (instr.hasValue ())
    result = Py_BuildValue ("s", instr.getValue ().c_str ());
  else
    result = pynsight::None ();

  return result;
}

static PyObject *
s_Simulator_load_mc (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  const char *filename;

  if (! PyArg_ParseTuple (args, "s", &filename))
    return NULL;
  
  if (S->load_microcode (filename))
    return pynsight::None ();
  return NULL;
}

static PyObject *
s_Simulator_save_mc (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  const char *filename;

  if (! PyArg_ParseTuple (args, "s", &filename))
    return NULL;
  
  if (S->save_microcode (filename))
    return pynsight::None ();
  return NULL;
}

static PyObject *
s_Simulator_load_stub (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  const char *filename;
  unsigned long addr;
  int fold = 0;

  if (! PyArg_ParseTuple (args, "sk|i", &filename, &addr, &fold))
    return NULL;
  
  if (S->load_stub (filename, addr, fold))
    return pynsight::None ();
  return NULL;
}

static PyObject *
s_Simulator_assume (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  const char *constraint;
  unsigned long g, l = 0;

  if (! PyArg_ParseTuple (args, "ks|k", &g, &constraint, &l))
    return NULL;
  
  Expr *expr = expr_parser (constraint, S->get_march ());
  if (expr == NULL)
    {
      PyErr_SetString(PyExc_SyntaxError, "syntax error");

      return NULL;
    }

  PyObject *result = NULL;
  MicrocodeAddress ma (g, l);
  S->add_assumption (ma, expr);
  expr->deref ();

  if (ma.equals (S->get_pc ()))
    {
      if (S->apply_assumption ())
	result = pynsight::None ();
    }
  else
    {
      result = pynsight::None ();
    }

  return result;
}

static PyObject *
s_Simulator_remove_assumption (PyObject *self, PyObject *args)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  PyObject *result = NULL;
  unsigned long g, l = 0;

  if (PyArg_ParseTuple (args, "k|k", &g, &l))
    {
      MicrocodeAddress ma (g,l);
      if (S->detach_assumption (ma))
	result = pynsight::None ();
      else
	PyErr_SetString(PyExc_ValueError, "no assumption here");
    }

  return result;
}

class AssumptionsIterator : public pynsight::GenericGenerator
{
private:
  GenericInsightSimulator *gsim;
  GenericInsightSimulator::AssumptionMap::const_iterator current;
  
public:
  AssumptionsIterator (GenericInsightSimulator *gsim) 
    : gsim (gsim), current (gsim->get_assumptions ().begin ()) { }

  virtual ~AssumptionsIterator () { }

  PyObject *next () {
    PyObject *result = NULL;
    if (current == gsim->get_assumptions ().end ())
      PyErr_SetNone (PyExc_StopIteration);
    else
      {
	result = Py_BuildValue ("(k, k, s)", 
				current->first.getGlobal (),
				current->first.getLocal (),
				current->second->to_string ().c_str ());
	current++;
      }

    return result;
  } 
};

static PyObject *
s_Simulator_get_assumptions (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  return pynsight::generic_generator_new (new AssumptionsIterator (S));
}

static PyObject *
s_Simulator_set_compare_state (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  S->set_compare_state (true);

  return pynsight::None ();
}

static PyObject *
s_Simulator_unset_compare_state (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;

  S->set_compare_state (false);

  return pynsight::None ();
}

static PyObject *
s_Simulator_compare_states (PyObject *self, PyObject *)
{
  GenericInsightSimulator *S = ((Simulator *) self)->gsim;
  GenericGenerator *gg = S->compare_states ();
  PyObject *result;
  if (gg != NULL)
    result = generic_generator_new (gg);
  else
    result = pynsight::None ();
  return result;
}

/*****************************************************************************
 *
 * GenericInsightSimulator
 *
 *****************************************************************************/

GenericInsightSimulator::GenericInsightSimulator (Program *P)
{
  prg = P;
  Py_INCREF (P);
  mc = new Microcode ();
  march = new MicrocodeArchitecture (P->loader->get_architecture ());
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

  delete arrows;
  for (StopConditionSet::iterator i = stop_conditions->begin (); 
       i != stop_conditions->end (); i++) {
    delete (*i);
  }
  delete stop_conditions;  

  for (AssumptionMap::iterator i = assumptions.begin (); 
       i != assumptions.end (); i++) {
    i->second->deref ();
  }
}

MicrocodeArchitecture *
GenericInsightSimulator::get_march () const
{
  return march;
}

const Microcode * 
GenericInsightSimulator::get_microcode () const
{
  return mc;
}

Program * 
GenericInsightSimulator::get_program () const
{
  return prg;
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

string 
GenericInsightSimulator::get_memory (address_t addr)
{
  void *s = get_state ();
  assert (s != NULL);

  string result = get_memory (s, addr);
  delete_state (s);  
  return result;
}

bool 
GenericInsightSimulator::check_memory_range (address_t addr, size_t len)
{
  void *s = get_state ();
  assert (s != NULL);
  bool result = check_memory_range (s, addr, len);
  delete_state (s);  

  return result;
}

static bool
s_try_set_state (GenericInsightSimulator *S, void *s)
{
  try { 
    S->set_state (s); 
    return true;
  } catch (CodeChangedException &e) { 
    s_CodeChangedException (e);
    return false;
  }
}

bool 
GenericInsightSimulator::abstract_memory (address_t addr, size_t len, 
					  bool keep_in_ctx)
{
  void *s = get_state ();
  void *ns = abstract_memory (s, addr, len, keep_in_ctx);
  if (ns != NULL)
    {
      s_try_set_state (this, ns); 
      delete_state (ns);  
    }
  delete_state (s);  

  return (ns != NULL) && !PyErr_Occurred ();
}

bool 
GenericInsightSimulator::concretize_memory (address_t addr, size_t len)
{
  void *s = get_state ();
  void *ns = concretize_memory (s, addr, len);
  if (ns != NULL)
    {
      s_try_set_state (this, ns); 
      delete_state (ns);  
    }
  delete_state (s);  

  return (ns != NULL) && !PyErr_Occurred ();
}

bool 
GenericInsightSimulator::concretize_memory (address_t addr, 
					    const ConcreteValue *values, 
					    size_t len)
{
  void *s = get_state ();
  void *ns = concretize_memory (s, addr, values, len);
  if (ns != NULL)
    {
      s_try_set_state (this, ns); 
      delete_state (ns);  
    }
  delete_state (s);  

  return (ns != NULL) && !PyErr_Occurred ();
}

string 
GenericInsightSimulator::get_register (const RegisterDesc *reg)
{
  void *s = get_state ();
  string result = get_register (s, reg);
  delete_state (s);  

  return result;
}

bool 
GenericInsightSimulator::check_register (const RegisterDesc *reg)
{
  void *s = get_state ();
  bool result = check_register (s, reg);
  delete_state (s);  

  return result;
}

bool 
GenericInsightSimulator::abstract_register (const RegisterDesc *reg, 
					    bool keep_in_ctx)
{
  void *s = get_state ();
  void *ns = abstract_register (s, reg, keep_in_ctx);
  if (ns != NULL)
    {
      s_try_set_state (this, ns);
      delete_state (ns);  
    }
  delete_state (s);  
  return (ns != NULL) && !PyErr_Occurred ();
}

bool
GenericInsightSimulator::concretize_register (const RegisterDesc *reg)
{
  void *s = get_state ();
  void *ns = concretize_register (s, reg);
  if (ns != NULL)
    {
      s_try_set_state (this, ns);
      delete_state (ns);  
    }
  delete_state (s);  
  return (ns != NULL) && !PyErr_Occurred ();
}

bool
GenericInsightSimulator::concretize_register (const RegisterDesc *reg, 
					      const ConcreteValue &v)
{
  void *s = get_state ();
  void *ns = concretize_register (s, reg, v);
  if (ns != NULL)
    {
      s_try_set_state (this, ns);
      delete_state (ns);  
    }
  delete_state (s);  
  return (ns != NULL) && !PyErr_Occurred ();
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

Option<string> 
GenericInsightSimulator::get_instruction (address_t addr)
{
  MicrocodeAddress ma (addr);
  Option<string> result;

  try
    {
      MicrocodeNode *node = mc->get_node (ma);
      assert (node != NULL);
      AsmAnnotation *aa = (AsmAnnotation *) 
	node->get_annotation (AsmAnnotation::ID);
      if (aa != NULL)
	result = aa->get_value ();
      else
	result = node->pp ();
    } 
  catch (GetNodeNotFoundExc &) { }

  return result;
}

bool 
GenericInsightSimulator::load_microcode (const string &filename)
{
  try
    {
      Microcode *newmc = xml_parse_mc_program (filename, march);
      delete mc;
      mc = newmc;
    }
  catch (XmlParserException &e)
    {
      PyErr_SetString (PyExc_IOError, e.what ());
      return false;
    }
  return true;
}

bool 
GenericInsightSimulator::load_stub (const string &filename, address_t shift,
				    bool fold)
{
  try
    {
      Microcode *newmc = xml_parse_mc_program (filename, march);

      for (Microcode::const_node_iterator i = newmc->begin_nodes ();
	   i != newmc->end_nodes (); i++)
	{
	  if (!(*i)->has_annotation (StubAnnotation::ID))
	    (*i)->add_annotation (StubAnnotation::ID,
				  new StubAnnotation ("insight-stub/" + 
						      filename));
	}

      mc->merge (newmc, shift, fold);
      delete newmc;
    }
  catch (XmlParserException &e)
    {
      PyErr_SetString (PyExc_IOError, e.what ());
      return false;
    }
  return true;  
}

bool 
GenericInsightSimulator::save_microcode (const string &filename)
{
  std::ofstream output (filename.c_str ());
  if (! output.is_open ())
    {
      PyErr_SetFromErrno (PyExc_IOError);
      return false;
    }
  
  xml_of_microcode (output, mc, march);
  output.flush ();
  output.close ();

  return true;
}

bool 
GenericInsightSimulator::assume (const Expr *e)
{
  void *s = get_state ();
  void *ns = assume (s, e);
  if (ns == NULL)
    PyErr_SetNone (PyExc_ValueError);
  else
    {
      s_try_set_state (this, ns);
      delete_state (ns);  
    }
  delete_state (s);  
  return (ns != NULL) && !PyErr_Occurred ();
}

void 
GenericInsightSimulator::add_assumption (const MicrocodeAddress &ma, 
					 const Expr *e)
{
  detach_assumption (ma);
  assumptions[ma] = e->ref ();
}

bool 
GenericInsightSimulator::apply_assumption ()
{
  MicrocodeAddress pc = get_pc ();
  AssumptionMap::const_iterator i = assumptions.find (pc);

  if (i == assumptions.end ())
    return true;
  return assume (i->second);
}

bool 
GenericInsightSimulator::detach_assumption (const MicrocodeAddress &addr)
{
  AssumptionMap::iterator i = assumptions.find (addr);
  if (i == assumptions.end ())
    return false;
  i->second->deref ();
  assumptions.erase (i);

  return true;
}

const GenericInsightSimulator::AssumptionMap &
GenericInsightSimulator::get_assumptions () const
{
  return assumptions;
}

/*****************************************************************************
 *
 * InsightSimulator<Stepper>
 *
 *****************************************************************************/

template <typename Stepper> 
InsightSimulator<Stepper>::InsightSimulator (Program *prg)
  : GenericInsightSimulator (prg)
{  
  stepper = new Stepper (prg->concrete_memory, march);
  stepper->set_map_dynamic_jumps_to_memory (true);
  stepper->set_unknown_value_generator (this);
  current_state = NULL;
  ref_state = NULL;
  decoder = new BinutilsDecoder (march, 
				 new RawBytesReader<Stepper>(this));
  in_abstraction = 0;
}

template <typename Stepper> 
InsightSimulator<Stepper>::~InsightSimulator ()
{
  delete stepper;
  if (current_state)
    current_state->deref ();
  if (ref_state)
    ref_state->deref ();
  delete decoder;
}

template <typename Stepper> string 
InsightSimulator<Stepper>::state_to_string (void *s) 
{
  return ((State *) s)->to_string ();
}

template <typename Stepper> void *
InsightSimulator<Stepper>::get_initial_state (address_t start)
{
  return stepper->get_initial_state (start);
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_state (void *ptr)
  throw (CodeChangedException)
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

template <typename Stepper> bool
InsightSimulator<Stepper>::has_state ()
{
  return (current_state != NULL);
}

template <typename Stepper> void * 
InsightSimulator<Stepper>::get_state ()
{
  assert (current_state != NULL);
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
	  
	  if (mc->has_node_at (tgt) || 
	      check_memory_range (from, tgt.getGlobal (), 1))
	    {
	      DynamicArrow *da = dynamic_cast<DynamicArrow *> (a);
	      if (da != NULL)
		{
		  MicrocodeAddress a =
		    result->get_ProgramPoint ()->to_MicrocodeAddress ();
		  da->add_solved_jump (a);
		}
	      result->ref ();
	    }
	  else
	    {
	      PyErr_SetObject (pynsight::JumpToInvalidAddress,
			       s_PyMicrocodeAddress (tgt));
	      result = NULL;
	    }
	}
      else if (succs->size () != 0)
	PyErr_SetNone (pynsight::NotDeterministicBehaviorError);
      stepper->destroy_state_set (succs);
    }
  catch (UndefinedValueException &e)
    {
      PyErr_SetString (pynsight::UndefinedValueError, e.what ());
    }

  return result;
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_memory (void *p, address_t addr, 
				       const typename Stepper::Value &value) 
{
  assert (value.get_size () == 8);
  typename Stepper::State *s = (typename Stepper::State *) p;
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
  mem->put (addr, value, Architecture::LittleEndian);
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_memory (void *p, address_t addr, uint8_t value) 
{
  typename Stepper::Value val (8, value);
  set_memory (p, addr, val);
}

template <typename Stepper> string 
InsightSimulator<Stepper>::get_memory (void *p, address_t addr) 
{
  return get_memory_value (p, addr).to_string ();
}

template <typename Stepper> typename Stepper::Value
InsightSimulator<Stepper>::get_memory_value (void *p, address_t addr) 
{
  typename Stepper::State *s = (typename Stepper::State *) p;
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
  return mem->get (addr, 1, Architecture::LittleEndian);
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

template <> void *
InsightSimulator<SymbolicStepper>::abstract_memory (void *p, address_t addr, 
						    size_t len, bool keep)
{
  State *s = (State *) p;
  Memory *mem = s->get_Context ()->get_memory ();
  Value *newvals = new Value[len];
  Expr *cond = keep ? Constant::True () : NULL;

  in_abstraction++;
  Value newval (stepper->unknown_value (8 * len));
  in_abstraction--;

  for (size_t i = 0; i < len; i++) 
    {
      Expr *v = Expr::createExtract (newval.get_Expr ()->ref(), 8 * i, 8);

      newvals[i] = Value (v);
      if (mem->is_defined (addr + i) && keep)
	{
	  Value val = get_memory_value (p, addr + i);
	  Expr *eq = 
	    Expr::createEquality (val.get_Expr ()->ref (), 
				  newvals[i].get_Expr ()->ref ());
	  cond = Expr::createLAnd (cond, eq);    
	}
      v->deref ();
    }
  if (keep)
    {
      s = stepper->restrict_state_to_condition (s, cond);
      cond->deref ();
    }
  else
    s = s->clone ();
      
  if (s != NULL)
    {
      for (size_t i = 0; i < len; i++)
	set_memory (s, addr + i, newvals[i]);
    }
  delete[] newvals;

  return s;   
}

template <> void *
InsightSimulator<ConcreteStepper>::abstract_memory (void *, address_t, 
						    size_t, bool)
{
  return NULL;
}

template <> void *
InsightSimulator<SymbolicStepper>::concretize_memory 
(void *p, address_t addr, const ConcreteValue *values, size_t len)
{
  SymbolicStepper::State *s = (SymbolicStepper::State *) p;
  SymbolicMemory *mem = s->get_Context ()->get_memory ();
  Expr *cond = Constant::True ();

  for (size_t i = 0; i < len; i++) 
    {
      if (! mem->is_defined (addr + i))
	continue;

      SymbolicStepper::Value val = get_memory_value (p, addr + i);
      Expr *eq = 
	Expr::createEquality (val.get_Expr()->ref (),
			      Constant::create (values[i].get (), 0, 8));
      cond = Expr::createLAnd (cond, eq);    
    }

  s = stepper->restrict_state_to_condition (s, cond);
  cond->deref ();
  if (s != NULL)
    {
      for (size_t i = 0; i < len; i++)
	set_memory (s, addr + i, values[i].get ());
    }

  return s;  
}

template <> void *
InsightSimulator<ConcreteStepper>::concretize_memory
(void *p, address_t addr, const ConcreteValue *values, size_t len)
{
  ConcreteStepper::State *s = (ConcreteStepper::State *) p;
  ConcreteMemory *mem = s->get_Context ()->get_memory ();
  bool eq = true;

  for (size_t i = 0; eq && i < len; i++) 
    {
      if ((eq = mem->is_defined (addr + i)))
	{
	  ConcreteValue v = get_memory_value (p, addr + i);
	  eq = values[i].equals (v);
	}
    }

  if (eq)
    s->ref ();
  else
    s = NULL;

  return s;  
}

template <typename Stepper> void *
InsightSimulator<Stepper>::concretize_memory (void *p, address_t addr, 
					      size_t len)
{
  typename Stepper::State *s = (typename Stepper::State *) p;
  ConcreteValue *cvalues = new ConcreteValue[len];

  for (size_t i = 0; i < len; i++) 
    {
      typename Stepper::Value val = get_memory_value (p, addr + i);
      cvalues[i] = stepper->value_to_ConcreteValue (s->get_Context (), val,
						    NULL);
    }
  s = (typename Stepper::State *) concretize_memory (s, addr, cvalues, len);
  delete [] cvalues;

  return s;
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_register (void *p, const RegisterDesc *reg, 
					 const typename Stepper::Value &value) 
{
  assert (value.get_size () == reg->get_window_size ());
  typename Stepper::State *s = (typename Stepper::State *) p;
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
  const RegisterDesc *areg = march->get_register (reg->get_label ());
  typename Stepper::Value val (value);

  if (val.get_size () != areg->get_register_size ())
    {
      typename Stepper::Value regval;

      if (mem->is_defined (areg))
	regval = mem->get (areg);
      else 
	{
	  in_abstraction++;
	  regval = stepper->unknown_value (areg->get_register_size ());
      	  in_abstraction--;
	}
      val = stepper->embed_eval (regval, val, reg->get_window_offset ());
    }     
  mem->put (areg, val);
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_register (void *p, const RegisterDesc *reg, 
					 word_t v)
{  
  typename Stepper::Value val (reg->get_window_size (), v);
  set_register (p, reg, val);
}

template <typename Stepper> string
InsightSimulator<Stepper>::get_register (void *p, const RegisterDesc *reg)
{
  return get_register_value (p, reg).to_string ();
}

template <typename Stepper> typename Stepper::Value
InsightSimulator<Stepper>::get_register_value (void *p, const RegisterDesc *reg)
{
  typename Stepper::State *s = (typename Stepper::State *) p;
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
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
      regval = stepper->eval (s->get_Context (), tmp);
      tmp->deref ();
    }     
  return regval;
}

template <typename Stepper> bool 
InsightSimulator<Stepper>::check_register (void *p, const RegisterDesc *reg)
{
  State *s = (State *) p;
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
  const RegisterDesc *areg = march->get_register (reg->get_label ());

  return mem->is_defined (areg);
}

template <> void *
InsightSimulator<SymbolicStepper>::abstract_register (void *p, 
						      const RegisterDesc *reg, 
						      bool keep_in_ctx)
{
  SymbolicStepper::State *s = (SymbolicStepper::State *) p;
  in_abstraction++;
  SymbolicStepper::Value newval = 
    stepper->unknown_value (reg->get_window_size ());
  in_abstraction--;
  if (check_register (p, reg) && keep_in_ctx)
    {
      SymbolicStepper::Value val = get_register_value (p, reg);
      Expr *cond = Expr::createEquality (val.get_Expr ()->ref (), 
					 newval.get_Expr ()->ref ());
      s = stepper->restrict_state_to_condition (s, cond);
      cond->deref ();
    }
  else
    {
      s = s->clone ();
    }

  if (s != NULL)
    set_register (s, reg, newval);

  return s;
}

template <> void *
InsightSimulator<ConcreteStepper>::abstract_register (void *, 
						      const RegisterDesc *, 
						      bool)
{
  return NULL;
}

template <typename Stepper> void *
InsightSimulator<Stepper>::concretize_register (void *p, 
						const RegisterDesc *reg)
{
  typename Stepper::State *s = (typename Stepper::State *) p;
  typename Stepper::Value regval = get_register_value (p, reg);
  ConcreteValue v = 
    stepper->value_to_ConcreteValue (s->get_Context (), regval, NULL);
  s = (typename Stepper::State *) concretize_register (s, reg, v);

  return s;
}

template <> void *
InsightSimulator<SymbolicStepper>::concretize_register
(void *p, const RegisterDesc *reg, const ConcreteValue &v)
{
  SymbolicStepper::State *s = (SymbolicStepper::State *) p;
  if (check_register (s, reg))
    {
      SymbolicStepper::Value regval = get_register_value (p, reg);
      Expr *cond = 
	Expr::createEquality (regval.get_Expr ()->ref (), 
			      Constant::create (v.get (), 0, 
						reg->get_window_size ()));
      s = stepper->restrict_state_to_condition (s, cond);
      cond->deref ();
    }
  else
    {
      s = dynamic_cast<SymbolicStepper::State *> (s->clone ());
    }
  if (s != NULL)
      set_register (s, reg, v.get ());
  return s;
}

template <> void *
InsightSimulator<ConcreteStepper>::concretize_register
(void *p, const RegisterDesc *reg, const ConcreteValue &v)
{
  ConcreteStepper::State *s = (ConcreteStepper::State *) p;

  s = s->clone ();
  set_register (s, reg, v.get ());

  return s;
}

template <typename Stepper> MicrocodeAddress 
InsightSimulator<Stepper>::get_pc (void *p)
{
  return ((State *) p)->get_ProgramPoint ()->to_MicrocodeAddress ();
}

template <typename Stepper> MicrocodeAddress 
InsightSimulator<Stepper>::get_pc ()
{
  void *s = get_state ();
  MicrocodeAddress res (get_pc (s));
  delete_state (s);

  return res;
}

template <typename Stepper> Option<ConcreteValue> 
InsightSimulator<Stepper>::eval (const Expr *e) const
{
  typename Stepper::Context *ctx = ((State *) current_state)->get_Context ();
  typename Stepper::Value val = stepper->eval (ctx, e);
  bool is_unique = false;
  ConcreteValue cv = stepper->value_to_ConcreteValue (ctx, val, &is_unique);

  if (! is_unique)
    return Option<ConcreteValue> ();  
  
  return Option<ConcreteValue> (cv);
}

template <typename Stepper> Option<bool> 
InsightSimulator<Stepper>::eval_condition (const Expr *e) const
{
  typename Stepper::Value val = 
    stepper->eval (((State *) current_state)->get_Context (), e);
  return val.to_bool ();
}

template <typename Stepper> Stepper *
InsightSimulator<Stepper>::get_stepper ()
{
  return stepper;
}

template <typename Stepper> void 
InsightSimulator<Stepper>::compute_enabled_arrows (State *s, 
						   ArrowVector *result) 
  throw (CodeChangedException)
{
  typename Stepper::State *ns = (typename Stepper::State *) s;
  typename Stepper::ProgramPoint *pp = ns->get_ProgramPoint ();
  address_t addr = pp->to_MicrocodeAddress ().getGlobal ();

  if (! prg->concrete_memory->is_defined (addr) && !mc->has_node_at (addr))
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
	  stepper->destroy_state_set (succs);
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
  throw (CodeChangedException)
{
  MicrocodeAddress ma = pp->to_MicrocodeAddress ();
  bool is_global = (ma.getLocal () == 0);
  MicrocodeNode *result = NULL;

  if (mc->has_node_at (ma))
    {
      result = mc->get_node (ma);
      if (!is_global || result->has_annotation (StubAnnotation::ID))
	return result;

      if (result->has_annotation (AsmAnnotation::ID))
	{
	  AsmAnnotation *aa = (AsmAnnotation *)
	    result->get_annotation (AsmAnnotation::ID);
	  string instr = decoder->get_instruction (ma.getGlobal ());
	  if (!(instr == aa->get_value ()))
	    throw CodeChangedException (ma.getGlobal ());
	}
      else
	{
	  // result is a node added by the decoder but asm instruction at
	  // pp.to_address () has not yet been decoded.
	  MicrocodeAddress addr = result->get_loc ();
	  assert (addr.getLocal () == 0);
	  ConcreteAddress next = decoder->decode (mc, addr.getGlobal ());
	  MicrocodeAddress nextma (next.get_address ());
	  result->add_annotation (NextInstAnnotation::ID,
				  new NextInstAnnotation (nextma));
	}
    }
  else
    {
      if (! is_global)
	throw GetNodeNotFoundExc();
      ConcreteAddress next = decoder->decode (mc, ma.getGlobal ());
      MicrocodeAddress nextma (next.get_address ());
      result = mc->get_node (ma);
      result->add_annotation (NextInstAnnotation::ID,
			      new NextInstAnnotation (nextma));
    }
    
  return result;
}

template <typename Stepper> void *
InsightSimulator<Stepper>::assume (void *p, const Expr *e) const 
{
  return stepper->restrict_state_to_condition ((State *) p, e);
}

template <typename Stepper>
class StateComparator : public GenericGenerator
{
public: 
  typedef typename Stepper::State State;
  typedef typename Stepper::Value Value;
  typedef typename Stepper::Memory Memory;
  typedef typename Memory::const_memcell_iterator cell_iterator;


  StateComparator (State *ref, State *other, const Architecture *arch) 
    : GenericGenerator (), arch (arch)
  {
    st1 = ref;
    st1->ref ();
    st2 = other;
    st2->ref ();
    m1 = ref->get_Context ()->get_memory ();
    m2 = other->get_Context ()->get_memory ();
    startmem = m2->begin ();
    endmem = m2->end ();
    startreg = arch->get_registers()->begin ();
    endreg = arch->get_registers()->end ();
  }

  virtual ~StateComparator () {
    st1->deref ();
    st2->deref ();
  }

  virtual bool are_different (Option<Value> &v1, Option<Value> &v2,
			      string &s1, string &s2) 
  {
    if (!(v1.hasValue () || v2.hasValue ()))
      return false;
    
    bool result = true;
    if (v1.hasValue ())
      s1 = v1.getValue ().to_string ();
    else
      s1 = "undefined";
    if (v2.hasValue ())
      s2 = v2.getValue ().to_string ();
    else
      s2 = "undefined";

    if (v1.hasValue () && v2.hasValue () && 
	values_are_equals (v1.getValue (), v2.getValue ()))
      result = false;

    return result;
  }
			      
  virtual PyObject *next () {
    PyObject *result = NULL;
    Option<Value> v1;
    Option<Value> v2;
    bool diff = false;
    const RegisterDesc *reg = NULL;
    address_t addr;
    string s1, s2;

    while (! diff && startmem != endmem) 
      {
	if (m1->is_defined (startmem->first))
	  v1 = m1->get (startmem->first, 1, arch->get_endian ());
	if (m2->is_defined (startmem->first))
	  v2 = m2->get (startmem->first, 1, arch->get_endian ());
	diff = are_different (v1, v2, s1, s2);
	if (diff)
	  addr = startmem->first;
	startmem++;
      }

    while (! diff && startreg != endreg) 
      {
	if (startreg->second->is_alias ())
	  {
	    startreg++;
	    continue;
	  }

	Option<Value> v1;
	Option<Value> v2;
	if (m1->is_defined (startreg->second))
	  v1 = m1->get (startreg->second);
	if (m2->is_defined (startreg->second))
	  v2 = m2->get (startreg->second);
	diff = are_different (v1, v2, s1, s2);
	if (diff)
	  reg = startreg->second;
	startreg++;
      }

    if (diff)
      {
	if (reg != NULL)
	  {
	    result = Py_BuildValue ("(s,s,s)", 
				    reg->get_label ().c_str (),
				    s1.c_str (),
				    s2.c_str ());
	  }
	else
	  {
	    result = Py_BuildValue ("(k,s,s)", addr, s1.c_str (), s2.c_str ());
	  }
      }

    return result;
  }

  virtual bool values_are_equals (const Value &v1, const Value &v2) const;

private:
  const Architecture *arch;
  Memory *m1;
  Memory *m2;
  State *st1;
  State *st2;
  cell_iterator startmem;
  cell_iterator endmem;
  RegisterSpecs::const_iterator startreg;
  RegisterSpecs::const_iterator endreg;
};

template <> bool 
StateComparator<ConcreteStepper>::values_are_equals (const ConcreteValue &v1, 
						     const ConcreteValue &v2) 
  const
{
  return v1.get () == v2.get ();
}

template <> bool 
StateComparator<SymbolicStepper>::values_are_equals (const SymbolicValue &v1, 
						     const SymbolicValue &v2) 
  const
{
  return v1.get_Expr () == v2.get_Expr ();
}


template <typename Stepper> GenericGenerator *
InsightSimulator<Stepper>::compare_states (void *s1, void *s2) const
{
  return new StateComparator<Stepper>((State *) s1, (State *) s2,
				      march->get_reference_arch ());
}

template <typename Stepper> void 
InsightSimulator<Stepper>::set_compare_state (bool set)
{
  if (ref_state != NULL)
    delete_state (ref_state);

  if (set)
    {
      ref_state = current_state;
      ref_state->ref ();
    }
  else
    ref_state = NULL;    
}

template <typename Stepper> GenericGenerator *
InsightSimulator<Stepper>::compare_states () const
{
  if (ref_state == NULL)
    return NULL;

  return compare_states (ref_state, current_state);
}

template <> SymbolicValue 
InsightSimulator<SymbolicStepper>::unknown_value (int size) 
{
  static unsigned int unique = 0;
  assert (current_state != NULL);
  std::ostringstream oss;
  MicrocodeAddress ma =
    current_state->get_ProgramPoint ()->to_MicrocodeAddress ();

  oss << (in_abstraction ? "abs" : "uv") << "_" << unique++ << "_0x" << std::hex
      << ma.getGlobal ();
  if (ma.getLocal () != 0)
    oss << "_" << std::dec << ma.getLocal ();
  oss << "_" << std::dec << size << "b";

  Expr *ev = Variable::create (oss.str (), size);
  SymbolicValue val (ev);
  ev->deref ();

  return val;
}

template <typename Stepper> typename Stepper::Value 
InsightSimulator<Stepper>::unknown_value (int size) 
{
  return 
    Stepper::Value::unknown_value_generator ()->unknown_value (size);
}

/******************************************************************************
 *
 * STOP CONDITIONS
 *
 ******************************************************************************/

int StopCondition::last_id = 1;

StopCondition::StopCondition () : id (last_id++), hits (0) 
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

size_t
StopCondition::get_number_of_hits () const 
{
  return hits;
}

void
StopCondition::reset (GenericInsightSimulator *)
{
  hits = 0;
}

void 
StopCondition::hit ()
{
  hits++;
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
  MicrocodeAddress pc = S->get_pc ();

  if (! pc.equals (addr))
    return false;

  hit ();
  if (cond == NULL)
    return true;

  Option<bool> val = S->eval_condition (cond);
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
  hit ();

  Option<bool> oval = S->eval_condition (cond);
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
  this->StopCondition::reset (S);
  Option<bool> oval = S->eval_condition (cond);
  last_value = ! oval.hasValue () || oval.getValue ();
}

PyWatchpoint::PyWatchpoint (PyObject *callable) 
  : StopCondition (), cb (callable)
{
  Py_INCREF (cb);
}

PyWatchpoint::~PyWatchpoint ()
{
  Py_DECREF (cb);
}

bool 
PyWatchpoint::stop (GenericInsightSimulator *)
{
  PyObject *res = PyObject_CallObject (cb, NULL);
  if (res == NULL)
    return false;
  hit ();
  bool result = (res != Py_None);
  Py_DECREF (res);
  return result;
}

void 
PyWatchpoint::output_text (std::ostream &out) const
{
  out << "callable object @" << std::hex << cb;
}

bool 
PyWatchpoint::equals (const StopCondition *other) const
{
  const PyWatchpoint *pw = dynamic_cast<const PyWatchpoint *> (other);
  return pw != NULL && pw->cb == cb;
}

void 
PyWatchpoint::reset (GenericInsightSimulator *S)
{
  this->StopCondition::reset (S);
}

/******************************************************************************
 *
 * RAW BYTES READERS
 *
 ******************************************************************************/

template <typename Stepper>
RawBytesReader<Stepper>::RawBytesReader (InsightSimulator<Stepper> *simulator)
  : simulator (simulator)
{
  
}

template <typename Stepper>
RawBytesReader<Stepper>::~RawBytesReader ()
{
}

template <typename Stepper> void
RawBytesReader<Stepper>::read_buffer (address_t from, uint8_t *dest, 
				      size_t length)
  throw (Decoder::Exception)
{
  typename Stepper::State *s = 
    (typename Stepper::State *) simulator->get_state ();
  typename Stepper::Memory *mem = s->get_Context ()->get_memory ();
  Stepper *stepper = simulator->get_stepper ();

  for (size_t i = 0; i < length; i++)
    {
      if (mem->is_defined (from + i))
	{
	  bool is_unique = true;
	  typename Stepper::Value val = 
	    mem->get(from + i, 1, Architecture::LittleEndian);

	  ConcreteValue cval = 
	    stepper->value_to_ConcreteValue (s->get_Context (), val, 
					     &is_unique);
	  if (! is_unique)
	    throw AbstractCodeException (from + i);
	  dest[i] = cval.get ();
	}
      else
	throw Decoder::OutOfBounds (from + i);
    }
  simulator->delete_state (s);
}


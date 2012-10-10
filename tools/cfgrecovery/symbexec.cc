#include <domains/common/ConcreteAddressMemory.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/ExprSolver.hh>
#include "SymbolicSimulator.hh"
#include "symbexec.hh"
#include <utils/map-helpers.hh>
#include <tr1/unordered_set>
#include <tr1/unordered_map>
#include <list>

using namespace std::tr1;
using namespace std;

typedef unordered_set<SymbolicState *, HashPtrFunctor<SymbolicState>, 
		      EqualsPtrFunctor<SymbolicState> > StateBag;
typedef unordered_map<address_t,int> CellCounterSet;
  
const std::string SYMSIM_X86_32_INIT_ESP_PROP =
  "disas.symsim.x86_32.init-esp";
const std::string SYMSIM_NB_VISITS_PER_ADDRESS =
  "disas.symsim.nb-visits-per-address";
const std::string SYMSIM_DEBUG_SHOW_STATES =
  "disas.symsim.debug.show-states";
const std::string SYMSIM_DYNAMIC_JUMP_THRESHOLD =
  "disas.symsim.dynamic-jump-threshold";
const std::string SYMSIM_MAP_DYNAMIC_JUMP_TO_MEMORY =
  "disas.symsim.map-dynamic-jump-to-memory";

Microcode *
symbexec (const ConcreteAddress *entrypoint, ConcreteMemory *memory,
	  Decoder *decoder)
{
  SymbolicSimulator *symsim = NULL;
  Microcode *result = new Microcode ();
  try
    {
      symsim = new SymbolicSimulator (memory, decoder, result);
    }
  catch (ExprSolver::SolverException &e)
    {
      logs::error << e.what () << endl;
      delete result;

      return NULL;
    }

  list< SymbolicState *> todo;
  SymbolicState *s = symsim->init (*entrypoint);
  StateBag visited;
  CellCounterSet ccs;

  bool show_states = 
    CFGRECOVERY_CONFIG->get_boolean (SYMSIM_DEBUG_SHOW_STATES, false);

  if (decoder->get_arch ()->get_proc () == Architecture::X86_32 && 
      CFGRECOVERY_CONFIG->has (SYMSIM_X86_32_INIT_ESP_PROP))
    {
      long valesp = 
	CFGRECOVERY_CONFIG->get_integer (SYMSIM_X86_32_INIT_ESP_PROP);
      if (verbosity)
	logs::warning << "warning: setting %esp to " << hex << "0x" 
		      << valesp << endl;

      Constant *c = Constant::create (valesp, 0, 32);
      
      s->get_memory ()->put (decoder->get_arch ()->get_register ("esp"), 
			     SymbolicValue (c));
      c->deref ();
    }

  int max_nb_visits =
    CFGRECOVERY_CONFIG->get_integer (SYMSIM_NB_VISITS_PER_ADDRESS, 0);

  if (max_nb_visits > 0 && verbosity)
    {
      logs::warning << "warning: restrict number of visits per program point "
		    << "to " << dec << max_nb_visits << " visits." << endl;
    }

  BEGIN_DBG_BLOCK ("Symbolic Simulation");
  todo.push_back (s);
  while (! todo.empty ())
    {
      s = todo.back ();
      todo.pop_back ();     

      if (visited.find (s) != visited.end ())
	{
	  delete s;
	  continue;
	}

      MicrocodeAddress ma (s->get_address ());
      if (max_nb_visits > 0 && ma.getLocal() == 0)
	{
	  address_t a = ma.getGlobal ();

	  if (ccs.find (a) == ccs.end ())
	    ccs[a] = 1;
	  else
	    {
	      int count = ccs[a];
	      ccs[a] = count +1;
	    }
	  if (ccs[a] > max_nb_visits)
	    visited.insert (s);
	}

      if (visited.find (s) == visited.end ())
	{
	  visited.insert (s);
	  assert (visited.find (s) != visited.end ());

	  if (ma.getLocal () == 0 && ! memory->is_defined (ma.getGlobal ()))
	    {
	      logs::warning << "warning: try to jump to undefined address 0x" 
			    << hex << ma.getGlobal () << endl;
	    }
	  else
	    {
	      if (show_states)
		s->output_text (logs::debug);

	      try
		{
		  SymbolicSimulator::ArrowSet arrows = symsim->get_arrows (s);
		  SymbolicSimulator::ArrowSet::const_iterator a = 
		    arrows.begin (); 
      
		  for (; a != arrows.end (); a++)
		    {
		      BEGIN_DBG_BLOCK ("trigger " + (*a)->pp ());
		      vector<SymbolicState *> *newstates = symsim->step (s, *a);

		      if (newstates->empty ())
			logs::debug << "no new context" << endl;
		      else
			{
			  logs::debug << "context has " << newstates->size ()
				      << " successors. " << endl;
			  for (size_t i = 0; i < newstates->size (); i++)
			    todo.push_back (newstates->at (i));
			}
		      delete newstates;

		      END_DBG_BLOCK ();
		    }
		}
	      catch (Decoder::Exception &e)
		{
		  if (verbosity > 0)
		    logs::warning << e.what () << endl;
		}
	      catch (UndefinedValueException &e) 
		{
		  logs::warning << e.what () << endl;
		}
	    }
	}
    }

  for (StateBag::iterator i = visited.begin (); i != visited.end (); i++)
    delete *i;

  END_DBG_BLOCK ();

  delete symsim;

  return result;
}

#include <domains/common/ConcreteAddressMemory.hh>
#include <kernel/Expressions.hh>
#include "SymbolicSimulator.hh"
#include "symbexec.hh"
#include <utils/map-helpers.hh>
#include <tr1/unordered_set>
#include <list>

using namespace std::tr1;
using namespace std;

typedef unordered_set<MicrocodeAddress, HashFunctor<MicrocodeAddress>, 
		      EqualsFunctor<MicrocodeAddress> > AddrBag;
typedef unordered_set<SymbolicState *, HashPtrFunctor<SymbolicState>, 
		      EqualsPtrFunctor<SymbolicState> > StateBag;

Microcode *
symbexec (const ConcreteAddress *entrypoint, ConcreteMemory *memory,
	  Decoder *decoder)
{
  Microcode *result = new Microcode ();
  SymbolicSimulator symsim (memory, decoder, result);
  list< SymbolicState *> todo;
  SymbolicState *s = symsim.init (*entrypoint);
  StateBag visited;

  BEGIN_DBG_BLOCK ("Symbolic Simulation");
  todo.push_back (s);
  while (! todo.empty ())
    {
      s = todo.back ();
      todo.pop_back ();     

      MicrocodeAddress ma (s->get_address ());

      //      if (visited.find (ma) == visited.end ())
      if (visited.find (s) == visited.end ())
	{
	  //	  visited.insert (ma);
	  visited.insert (s);

	  if (ma.getLocal () == 0 && ! memory->is_defined (ma.getGlobal ()))
	    {
	      logs::warning << "warning: try to jump to undefined address 0x" 
			    << hex << ma.getGlobal () << endl;
	    }
	  else
	    {
	      s->output_text (logs::debug);

	      try
		{
		  SymbolicSimulator::ArrowSet arrows = symsim.get_arrows (s);
		  SymbolicSimulator::ArrowSet::const_iterator a = 
		    arrows.begin (); 
      
		  for (; a != arrows.end (); a++)
		    {
		      BEGIN_DBG_BLOCK ("trigger " + (*a)->pp ());
		      SymbolicState *c = symsim.step (s, *a);
		      if (c != NULL)
			todo.push_back (c);
		      else
			logs::debug << "no new context" << endl;
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
      else
	{
	  delete s;
	}
    }
  for (StateBag::iterator i = visited.begin (); i != visited.end (); i++)
    delete *i;

  END_DBG_BLOCK ();

  return result;
}

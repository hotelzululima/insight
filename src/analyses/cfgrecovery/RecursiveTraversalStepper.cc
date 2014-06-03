#include <kernel/annotations/CallRetAnnotation.hh>
#include <kernel/annotations/NextInstAnnotation.hh>
#include "FloodTraversal.hh"
#include "RecursiveTraversal.hh"

using namespace std;

RecursiveTraversal::Stepper::Stepper (ConcreteMemory *memory,
				      const Architecture *arch)
  : AbstractStepper<State>(), memory (memory), arch (arch)
{
}

RecursiveTraversal::Stepper::~Stepper ()
{
}

RecursiveTraversal::Stepper::State *
RecursiveTraversal::Stepper::get_initial_state (const ConcreteAddress &ep)
{
  MicrocodeAddress ma (ep.get_address ());

  return new State (new ProgramPoint (ma), new Context ());
}

RecursiveTraversal::Stepper::StateSet *
RecursiveTraversal::Stepper::get_successors (const State *s,
					     const StmtArrow *arrow)
{
  ProgramPoint *pp = s->get_ProgramPoint ();
  Context *ctx = s->get_Context ();
  MicrocodeNode *src = arrow->get_src ();
  StateSet *result = new StateSet ();

  if (! src->has_annotation (CallRetAnnotation::ID))
    {
      list<MicrocodeAddress> successors;

      FloodTraversal::Stepper::compute_successors (memory, arch, arrow,
						   false, successors);
      for (list<MicrocodeAddress>::iterator i = successors.begin ();
	   i != successors.end (); i++)
	{
	  State *new_s = new State (pp->next (*i), ctx->clone ());
	  result->insert (new_s);
	}
    }
  else
    {
      CallRetAnnotation *an = (CallRetAnnotation *)
	src->get_annotation (CallRetAnnotation::ID);

      if (an->is_call ())
	{
	  const Expr *tgt = an->get_target ();
	  ConcreteAddress ctgt;
	  bool ctgt_is_defined = false;
	  if (tgt->is_Constant ())
	    {
	      const Constant *c = dynamic_cast<const Constant *> (tgt);
	      ctgt = ConcreteAddress (c->get_val ());
	      ctgt_is_defined = true;
	    }
	  else if (tgt->is_MemCell ())
	    {
	      const MemCell *mc = dynamic_cast<const MemCell *> (tgt);

	      if (mc != NULL && mc->get_addr ()->is_Constant ())
		{
		  Constant *cst = dynamic_cast<Constant *> (mc->get_addr ());
		  ConcreteAddress a (cst->get_val());

		  if (memory->is_defined(a))
		    {
		      ConcreteValue val =
			memory->get (a, arch->get_address_size (),
				     arch->get_endian ());
		      ctgt = ConcreteAddress (val.get ());
		      ctgt_is_defined = true;
		    }
		}
	    }

	  if (ctgt_is_defined && memory->is_defined (ctgt))
	    {
	      vector<MicrocodeNode *> parents = src->get_global_parents ();
	      list<Context *> newctxs;

	      for (vector<MicrocodeNode *>::iterator i = parents.begin ();
		   i != parents.end (); i++)
		{
		  MicrocodeNode *p = *i;
		  if (! p->has_annotation (NextInstAnnotation::ID))
		    continue;

		  NextInstAnnotation *nia = (NextInstAnnotation *)
		    p->get_annotation (NextInstAnnotation::ID);
		  MicrocodeAddress ma = nia->get_value ();
		  assert (ma.getLocal () == 0);
		  ConcreteAddress next (ma.getGlobal ());
		  newctxs.push_back (ctx->push (next));
		}

	      if (newctxs.empty ())
		newctxs.push_back (ctx->clone ());

	      while (! newctxs.empty ())
		{
		  Context *newctx = newctxs.front ();
		  newctxs.pop_front ();
		  MicrocodeAddress tgt (ctgt.get_address ());
		  State *succ =
		    new State (s->get_ProgramPoint ()->next (tgt), newctx);
		  result->insert (succ);
		}
	    }
	}
      else if (! ctx->empty ())
	{
	  MicrocodeAddress ret (ctx->top ().get_address ());
	  Context *newctx = ctx->pop ();
	  State *succ = new State (s->get_ProgramPoint ()->next (ret), newctx);
	  result->insert (succ);
	}
      else
	{
	  logs::error << src->get_loc ()
		      << ": error: ret without matching call" << endl;
	}
    }

  return result;
}

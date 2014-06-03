#include "FloodTraversal.hh"

using namespace std;

FloodTraversal::Stepper::Stepper (ConcreteMemory *memory,
				  const Architecture *arch)
  : LinearSweep::Stepper (), memory (memory), arch (arch)
{
}

FloodTraversal::Stepper::~Stepper ()
{
}

void
FloodTraversal::Stepper::compute_successors (ConcreteMemory *memory,
					     const Architecture *arch,
					     const StmtArrow *arrow,
					     bool with_next,
					     list<MicrocodeAddress> &result)
{
  MicrocodeAddress next;

  if (with_next && LinearSweep::Stepper::compute_successor (arrow, next))
    result.push_back (next);

  const StaticArrow *sa = dynamic_cast<const StaticArrow *> (arrow);
  MicrocodeAddress tgt;
  bool tgt_is_defined = false;

  if (sa == NULL)
    {
      const DynamicArrow *da = dynamic_cast<const DynamicArrow *> (arrow);
      MemCell *mc = dynamic_cast<MemCell *> (da->get_target ());

      if (mc != NULL && mc->get_addr ()->is_Constant ())
	{
	  Constant *cst = dynamic_cast<Constant *> (mc->get_addr ());
	  word_t addr = cst->get_val();
	  bool isdef = true;

	  for (int i = 0; i < arch->get_address_size () / 8 && isdef; i++)
	    {
	      ConcreteAddress a (addr + i);
	      isdef = memory->is_defined(a);
	    }

	  if (isdef)
	    {
	      ConcreteAddress a (addr);
	      ConcreteValue val =
		memory->get (a, arch->get_address_size () / 8,
			     arch->get_endian ());
	      tgt = MicrocodeAddress (val.get ());
	      tgt_is_defined = true;
	    }
	}
    }
  else
    {
      tgt = sa->get_target ();
      tgt_is_defined = true;
    }

  if (tgt_is_defined)
    {
      if (result.empty () || ! tgt.equals (next))
	result.push_back (tgt);
    }
}

FloodTraversal::Stepper::StateSet *
FloodTraversal::Stepper::get_successors (const State *s,
					 const StmtArrow *arrow)
{
  StateSet *result = new StateSet ();
  list<MicrocodeAddress> successors;
  ProgramPoint *pp = s->get_ProgramPoint ();
  Context *ctx = s->get_Context ();

  compute_successors (memory, arch, arrow, true, successors);

  for (list<MicrocodeAddress>::iterator i = successors.begin ();
       i != successors.end (); i++)
    {
      ctx->ref ();
      State *new_s = new State (pp->next (*i), ctx);
      result->insert (new_s);
    }

  return result;
}

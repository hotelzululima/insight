#include <kernel/annotations/NextInstAnnotation.hh>
#include "LinearSweep.hh"

LinearSweep::Stepper::Stepper ()
  : AbstractStepper<State> ()
{
}

LinearSweep::Stepper::~Stepper () 
{ 
}

LinearSweep::State * 
LinearSweep::Stepper::get_initial_state (const ConcreteAddress &entrypoint) 
{
  MicrocodeAddress ma (entrypoint.get_address ());

  return new State (new ProgramPoint (ma), new Context ());
}

    
LinearSweep::Stepper::StateSet *
LinearSweep::Stepper::get_successors (const State *s, const StmtArrow *arrow) 
{
  StateSet *result = new StateSet ();
  ProgramPoint *pp = s->get_ProgramPoint ();
  MicrocodeAddress ma = pp->to_MicrocodeAddress ();
  if (ma.getLocal () != 0)
    return result;
  
  if (compute_successor (arrow, ma))
    {
      Context *ctx = s->get_Context ();
      ctx->ref ();
      State *new_s = new State (pp->next (ma), ctx);
      result->insert (new_s);
    }
  return result;
}

bool
LinearSweep::Stepper::compute_successor (const StmtArrow *arrow,
					 MicrocodeAddress &result)
{
  MicrocodeNode *src = arrow->get_src ();
  if (! src->has_annotation (NextInstAnnotation::ID))
    return false;

  NextInstAnnotation *an = (NextInstAnnotation *) 
    src->get_annotation (NextInstAnnotation::ID);
  result = an->get_value ();

  return true;
}

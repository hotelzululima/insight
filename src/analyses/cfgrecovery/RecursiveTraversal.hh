#ifndef RECURSIVETRAVERSAL_HH
# define RECURSIVETRAVERSAL_HH

# include <cassert>
# include <list>
# include <tr1/unordered_map>
# include <analyses/cfgrecovery/MicrocodeAddressProgramPoint.hh>
# include <analyses/cfgrecovery/AbstractStepper.hh>
# include <analyses/cfgrecovery/SingleContextStateSpace.hh>
# include <analyses/cfgrecovery/AbstractMemoryTraversal.hh>

class RecursiveTraversal
{
public:
  typedef MicrocodeAddressProgramPoint ProgramPoint;

  class Context : public AbstractContext {   
  public:
    typedef std::list<ConcreteAddress> CallStack;

    Context ();
    Context (const CallStack &cs);

    virtual ~Context ();
    
    virtual bool equals (const AbstractContext *other) const;
    virtual bool empty () const;
    virtual Context *push (const ConcreteAddress &retaddr)const;
    virtual ConcreteAddress top () const;
    virtual Context *pop () const;
    virtual Context *clone () const;
    virtual std::size_t hashcode () const;
    virtual void output_text (std::ostream &out) const;

  private:
    CallStack stack;
    std::size_t hvalue;

    void compute_hvalue ();
  };

  typedef AbstractState<ProgramPoint, Context> State;

  typedef SingleContextStateSpace<State> StateSpace;

  class Stepper : public AbstractStepper<State> {
  public:
    typedef RecursiveTraversal::Context Context;

    Stepper (ConcreteMemory *memory, const Architecture *arch);

    virtual ~Stepper ();

    virtual State *get_initial_state (const ConcreteAddress &entrypoint);

    virtual StateSet *get_successors (const State *s, const StmtArrow *arrow);
    
  private:        
    ConcreteMemory *memory; 
    const Architecture *arch;
  };

  typedef AbstractMemoryTraversal<RecursiveTraversal> Traversal;
};

#endif /* ! RECURSIVETRAVERSAL_HH */

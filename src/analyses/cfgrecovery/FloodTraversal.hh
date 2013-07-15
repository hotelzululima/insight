#ifndef FLOODTRAVERSAL_HH
# define FLOODTRAVERSAL_HH

# include <list>
# include <analyses/cfgrecovery/LinearSweep.hh>

class FloodTraversal : public LinearSweep
{
public:
  class Stepper : public LinearSweep::Stepper {
  public:
    Stepper (ConcreteMemory *memory, const Architecture *arch);
    virtual ~Stepper ();

    virtual StateSet *get_successors (const State *s, const StmtArrow *arrow);

    static void
    compute_successors (ConcreteMemory *memory, const Architecture *arch, 
			const StmtArrow *arrow, 
			bool with_next, std::list<MicrocodeAddress> &result);

  protected:
    ConcreteMemory *memory;
    const Architecture *arch;
  };

  typedef AbstractMemoryTraversal<FloodTraversal> Traversal;
};

#endif /* ! FLOODTRAVERSAL_HH */

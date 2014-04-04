#ifndef ABSTRACTDOMAINSTEPPER_HH
# define ABSTRACTDOMAINSTEPPER_HH

# include <analyses/cfgrecovery/MicrocodeAddressProgramPoint.hh>
# include <analyses/cfgrecovery/SingleContextStateSpace.hh>
# include <analyses/cfgrecovery/AbstractState.hh>
# include <analyses/cfgrecovery/AbstractStepper.hh>

template <typename PP, typename CTX>
class AbstractDomainStepper 
  : public AbstractStepper<AbstractState <PP, CTX> > 
{  
protected:
  AbstractDomainStepper (const Architecture *arch);

public:
  typedef AbstractState<PP, CTX> State;
  typedef typename State::Context Context;
  typedef typename State::ProgramPoint ProgramPoint;
  typedef typename AbstractStepper<State>::StateSet StateSet;
  typedef typename Context::Memory Memory;
  typedef typename Memory::Value Value;
  typedef typename Memory::Address Address;
  typedef UnknownValueGenerator<Value> UnknownGenerator;

  virtual ~AbstractDomainStepper  ();

  virtual State *get_initial_state (const ConcreteAddress &entrypoint) = 0;

  virtual StateSet *get_successors (const State *s, const StmtArrow *arrow)
    throw (UndefinedValueException);

  virtual ConcreteValue 
  value_to_ConcreteValue (const Context *ctx, const Value &v, 
			  bool *is_unique)
    throw (UndefinedValueException) = 0;

  virtual Address 
  value_to_address (const Context *ctx, const Value &v) 
    throw (UndefinedValueException) = 0;
    
  virtual std::vector<address_t> * 
  value_to_concrete_addresses (const Context *ctx, const Value &v) 
    throw (UndefinedValueException) = 0;
    
  virtual Value eval (const Context *ctx, const Expr *e) = 0;

  virtual Value embed_eval (const Value &v1, const Value &v2, 
			    int off) const = 0;

  void set_map_dynamic_jumps_to_memory (bool value);

  void set_dynamic_jump_threshold (int value);

  virtual State * 
  restrict_state_to_condition (const State *s, const Expr *cond);

  virtual void destroy_state_set (StateSet *s);

  virtual Value unknown_value (int size);
  virtual UnknownGenerator *get_unknown_value_generator ();
  virtual void set_unknown_value_generator (UnknownGenerator *gen);

protected:
  const Architecture *arch;
  UnknownGenerator *unkgen;
  bool map_dynamic_jumps_to_memory;
  int dynamic_jump_threshold;

  virtual Context * 
  restrict_to_condition (const Context *ctx, const Expr *cond) = 0;

  virtual void exec (Context *newctx, const Statement *st);
};

# include <analyses/cfgrecovery/AbstractDomainStepper.ii>

#endif /* ! ABSTRACTDOMAINSTEPPER_HH */

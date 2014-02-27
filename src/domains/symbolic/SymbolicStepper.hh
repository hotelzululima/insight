#ifndef SYMBOLICSTEPPER_HH
# define SYMBOLICSTEPPER_HH

# include <analyses/cfgrecovery/AbstractDomainStepper.hh>
# include <analyses/cfgrecovery/MicrocodeAddressProgramPoint.hh>

# include <domains/symbolic/SymbolicMemory.hh>
# include <domains/symbolic/SymbolicContext.hh>
# include <domains/symbolic/SymbolicExprSemantics.hh>


class SymbolicStepper : 
  public AbstractDomainStepper<MicrocodeAddressProgramPoint, SymbolicContext>
{
private:
  class ExprSolver *solver;

public:
  typedef AbstractDomainStepper<MicrocodeAddressProgramPoint,
				SymbolicContext> Super;

  typedef Super::Address Address;
  typedef Super::Value Value;
  typedef Super::State State;

  SymbolicStepper (ConcreteMemory *memory, const MicrocodeArchitecture *arch);
  virtual ~SymbolicStepper ();

  virtual ConcreteValue 
  value_to_ConcreteValue (const Context *ctx, const Value &v) 
    throw (UndefinedValueException);

  virtual Address 
  value_to_address (const Context *ctx, const Value &v) 
    throw (UndefinedValueException);

  virtual std::vector<address_t> * 
  value_to_concrete_addresses (const Context *ctx, const Value &v) 
    throw (UndefinedValueException);
  
  virtual Value eval (const Context *ctx, const Expr *e)
    throw (UndefinedValueException);  

  virtual Value embed_eval (const Value &v1, const Value &v2, int off) const;

  virtual State *get_initial_state (const ConcreteAddress &entrypoint);

protected:
  virtual Context * 
  restrict_to_condition (const Context *ctx, const Expr *cond);

  ConcreteMemory *memory;
};

#endif /* ! SYMBOLICSTEPPER_HH */

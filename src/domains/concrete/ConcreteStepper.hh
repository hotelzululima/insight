#ifndef CONCRETESTEPPER_HH
# define CONCRETESTEPPER_HH

# include <analyses/cfgrecovery/AbstractDomainStepper.hh>
# include <analyses/cfgrecovery/MicrocodeAddressProgramPoint.hh>

# include <domains/concrete/ConcreteMemory.hh>
# include <domains/concrete/ConcreteContext.hh>
# include <domains/concrete/ConcreteExprSemantics.hh>


class ConcreteStepper : 
  public AbstractDomainStepper<MicrocodeAddressProgramPoint, ConcreteContext>
{
public:
  typedef AbstractDomainStepper<MicrocodeAddressProgramPoint, 
				ConcreteContext> Super;

  typedef Super::Address Address;
  typedef Super::Value Value;
  typedef Super::State State;

  ConcreteStepper (ConcreteMemory *memory, const MicrocodeArchitecture *arch);
  virtual ~ConcreteStepper ();

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

#endif /* ! CONCRETESTEPPER_HH */

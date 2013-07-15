#ifndef ABSTRACTCONTEXT_HH
# define ABSTRACTCONTEXT_HH

# include <utils/Object.hh>

class AbstractContext : public Object 
{
private:
  mutable int refcount;

protected:
  AbstractContext ();

  virtual ~AbstractContext ();

public:

  void ref () const;

  void deref ();

  virtual bool equals (const AbstractContext *) const = 0;

  virtual std::size_t hashcode () const = 0;

  virtual void output_text (std::ostream &) const = 0;
};

#endif /* ! ABSTRACTCONTEXT_HH */

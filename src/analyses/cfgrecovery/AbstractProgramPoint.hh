#ifndef ABSTRACTPROGRAMPOINT_HH
# define ABSTRACTPROGRAMPOINT_HH

# include <utils/Object.hh>
# include <kernel/Microcode.hh>

template<typename PP>
class AbstractProgramPoint : public Object
{
protected:
  AbstractProgramPoint ();
  virtual ~AbstractProgramPoint ();

public:
  void ref () const;

  void deref ();

  virtual MicrocodeAddress to_MicrocodeAddress () const = 0;

  virtual PP *next (const MicrocodeAddress &addr) const = 0;

  virtual bool equals (const PP *) const = 0;
  virtual bool equals (const PP &) const = 0;
  virtual bool lessThan(const PP &other) const = 0;
  virtual std::size_t hashcode () const = 0;

  virtual void output_text (std::ostream &) const = 0;

private:
  mutable int refcount;
};

# include <analyses/cfgrecovery/AbstractProgramPoint.ii>

#endif /* ! ABSTRACTPROGRAMPOINT_HH */

#ifndef DUMMYSTATESPACE_HH
# define DUMMYSTATESPACE_HH

# include <analyses/cfgrecovery/AbstractStateSpace.hh>

template <typename State>
class DummyStateSpace : public AbstractStateSpace<State>
{

public:
  DummyStateSpace () { }

  virtual ~DummyStateSpace () { }

  virtual const State *find_or_add_state (State *s) { return s; }
  virtual std::size_t size () const { return 1; }
};

#endif /* ! DUMMYSTATESPACE_HH */

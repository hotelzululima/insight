#ifndef SINGLECONTEXTSTATESPACE_HH
# define SINGLECONTEXTSTATESPACE_HH

# include <tr1/unordered_set>
# include <set>
# include <utils/map-helpers.hh>
# include <analyses/cfgrecovery/AbstractStateSpace.hh>

template <typename State>
class SingleContextStateSpace : public AbstractStateSpace<State>
{

public:
  SingleContextStateSpace ();

  virtual ~SingleContextStateSpace ();

  virtual State *find_or_add_state (State *s);
  virtual std::size_t size () const;

private:
  typedef std::tr1::unordered_set<State *, HashPtrFunctor<State>, 
  				  EqualsPtrFunctor<State> > StateTable;

  StateTable states;
};

# include <analyses/cfgrecovery/SingleContextStateSpace.ii>

#endif /* ! SINGLECONTEXTSTATESPACE_HH */

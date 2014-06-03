#ifndef ABSTRACTSTATESPACE_HH
# define ABSTRACTSTATESPACE_HH

# include <utils/Object.hh>

template <typename S>
class AbstractStateSpace : public Object
{
protected:
  virtual ~AbstractStateSpace () { }
public:
  typedef S State;

  virtual State *find_or_add_state (State *s) = 0;
};

#endif /* ! ABSTRACTSTATESPACE_HH */

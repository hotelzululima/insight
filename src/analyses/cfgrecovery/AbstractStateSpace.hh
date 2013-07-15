#ifndef ABSTRACTSTATESPACE_HH
# define ABSTRACTSTATESPACE_HH

template <typename S>
class AbstractStateSpace : public Object 
{
protected:
  virtual ~AbstractStateSpace () { }
public:
  typedef S State;

  virtual const State *find_or_add_state (State *s) = 0;
};

#endif /* ! ABSTRACTSTATESPACE_HH */

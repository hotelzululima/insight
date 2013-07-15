#ifndef MICROCODEADDRESSPROGRAMPOINT_HH
# define MICROCODEADDRESSPROGRAMPOINT_HH

# include <analyses/cfgrecovery/AbstractProgramPoint.hh>

class MicrocodeAddressProgramPoint 
  : public AbstractProgramPoint<MicrocodeAddressProgramPoint>
{
public:
  MicrocodeAddressProgramPoint (const MicrocodeAddress &ma);

  virtual ~MicrocodeAddressProgramPoint ();

  virtual MicrocodeAddress to_MicrocodeAddress () const;

  virtual MicrocodeAddressProgramPoint *next (const MicrocodeAddress &addr) 
    const;

  virtual bool equals (const MicrocodeAddressProgramPoint *pp) const;

  virtual std::size_t hashcode () const;

  virtual void output_text (std::ostream &out) const;

private: 
  MicrocodeAddress address;
};

#endif /* ! MICROCODEADDRESSPROGRAMPOINT_HH */

#include "MicrocodeAddressProgramPoint.hh"


MicrocodeAddressProgramPoint::
 MicrocodeAddressProgramPoint (const MicrocodeAddress &ma) 
   : AbstractProgramPoint<MicrocodeAddressProgramPoint>(), address (ma) 
{ 
}

MicrocodeAddressProgramPoint::~MicrocodeAddressProgramPoint ()
{ 
}

MicrocodeAddress MicrocodeAddressProgramPoint::to_MicrocodeAddress () const
{ 
  return address; 
}

MicrocodeAddressProgramPoint *
MicrocodeAddressProgramPoint::next (const MicrocodeAddress &addr) const
{
  return new MicrocodeAddressProgramPoint (addr);
}

bool 
MicrocodeAddressProgramPoint::equals (const MicrocodeAddressProgramPoint *pp) 
  const
{
  return pp->to_MicrocodeAddress ().equals (address);
}

bool 
MicrocodeAddressProgramPoint::equals (const MicrocodeAddressProgramPoint &pp) 
  const
{
  return pp.to_MicrocodeAddress ().equals (address);
}

bool 
MicrocodeAddressProgramPoint::lessThan(const MicrocodeAddressProgramPoint &pp) 
  const
{
  return pp.to_MicrocodeAddress ().lessThan (address);
}

std::size_t 
MicrocodeAddressProgramPoint::hashcode () const
{
  return address.hashcode ();
}

void 
MicrocodeAddressProgramPoint::output_text (std::ostream &out) const 
{
  out << address;
}

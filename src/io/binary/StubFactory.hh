#ifndef STUBFACTORY_HH
# define STUBFACTORY_HH

# include <domains/concrete/ConcreteMemory.hh>
# include <io/binary/SymbolTable.hh>
# include <kernel/Microcode.hh>
# include <kernel/microcode/MicrocodeArchitecture.hh>

class StubFactory 
{
public:
  virtual ~StubFactory () { }

  virtual void add_stubs (ConcreteMemory *memory, 
			  MicrocodeArchitecture *arch, Microcode *dest,
			  SymbolTable *symtab) = 0;
};

#endif /* ! STUBFACTORY_HH */

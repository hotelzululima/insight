#ifndef BINUTILSSTUBFACTORY_HH
# define BINUTILSSTUBFACTORY_HH

# include <io/binary/StubFactory.hh>

class BinutilsStubFactory : public StubFactory 
{
protected:
  BinutilsStubFactory (struct bfd *abf);

public:
  virtual ~BinutilsStubFactory ();
  
  virtual void add_stubs (ConcreteMemory *memory, MicrocodeArchitecture *arch, 
			  Microcode *dest, SymbolTable *symtab) = 0;

  static BinutilsStubFactory *create_ELF_x86_32_StubFactory (bfd *abfd);
};

#endif /* ! BINUTILSSTUBFACTORY_HH */

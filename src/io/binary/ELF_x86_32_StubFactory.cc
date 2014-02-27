/*-
 * Copyright (C) 2010-2013, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS AND CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include "BinutilsStubFactory.hh"

#include <bfd.h>
#include <config.h>

#include <cstdlib>
#include <map>
#include <string>

#include <kernel/annotations/AsmAnnotation.hh>
#include <kernel/annotations/CallRetAnnotation.hh>

using namespace std;

#define R_386_JUMP_SLOT 7

class ELF_x86_32_StubFactory : public BinutilsStubFactory 
{
public:
  ELF_x86_32_StubFactory (bfd *abfd);

  virtual ~ELF_x86_32_StubFactory ();

  virtual void add_stubs (ConcreteMemory *memory, MicrocodeArchitecture *arch,
			  Microcode *dest, SymbolTable *symtab);

  string dynamic_symbol_name (arelent *e, int &symcounter);

private:
  typedef map<string, address_t> SlotMap;
  SlotMap slots;
};


BinutilsStubFactory *
BinutilsStubFactory::create_ELF_x86_32_StubFactory (bfd *abfd)
{
  return new ELF_x86_32_StubFactory (abfd);
}

static asymbol **
s_build_dynamic_symbols_table (bfd *abfd)
{
  asymbol **result = NULL;
  size_t sysize = bfd_get_dynamic_symtab_upper_bound (abfd);

  if (sysize > 0)
    {
      asymbol **tmp = (asymbol **) malloc (sysize);
     
      if (bfd_canonicalize_dynamic_symtab (abfd, tmp) < 0)
	{
	  logs::error << "error: after bfd_canonicalize_dynamic_symtab" 
		      << endl;
	  free (tmp);
	}
      else
	{
	  result = tmp;
	}
    }
  return result;
}


ELF_x86_32_StubFactory::ELF_x86_32_StubFactory (bfd *abfd) 
  : BinutilsStubFactory (abfd)
{
  asymbol **dynsymbols;
  arelent **relpp;
  long relcount;
  int undefsymbolidx;
  long relsize = bfd_get_dynamic_reloc_upper_bound (abfd);
   
  if (relsize <= 0)
    return;

  dynsymbols = s_build_dynamic_symbols_table (abfd);
  relpp = (arelent **) malloc (relsize);

  if (relpp == NULL)
    goto end;
  relcount = bfd_canonicalize_dynamic_reloc (abfd, relpp, dynsymbols);
  if (relcount < 0)
    {
      logs::error << "error: after bfd_canonicalize_dynamic_reloc" << endl;
      goto end;
    }
  undefsymbolidx = 0;
  for (int i = 0; i < relcount; i++)
    {
      if (relpp[i]->howto == NULL)
	continue;

      int type = relpp[i]->howto->type;
      if (type != R_386_JUMP_SLOT)
	{
	  logs::warning << "warning: ignoring EL32 relocation type R_386_" 
			<< relpp[i]->howto->name 
			<< " (" << type << ")" << endl;
	  continue;
	}
      string sname = dynamic_symbol_name (relpp[i], undefsymbolidx);
      address_t addr = relpp[i]->address + relpp[i]->addend;
      assert (slots.find (sname) == slots.end ());
      slots[sname] = addr;
    }

 end:
  if (relpp != NULL)
    free (relpp);
  if (dynsymbols != NULL)
    free (dynsymbols);
}

ELF_x86_32_StubFactory::~ELF_x86_32_StubFactory () 
{
  
}

static void
s_jump_to_top_of_stack (MicrocodeAddress &start, Microcode *prog,
			const Architecture *arch)
{
  RegisterExpr *esp = RegisterExpr::create (arch->get_register ("esp"), 0, 32);
  Expr *retaddr = 
    MemCell::create (BinaryApp::create (BV_OP_ADD, esp, 
					Constant::create (4, 0, 32)),
		     0, esp->get_bv_size ());
  prog->add_jump (start, retaddr); 
}

static void 
s_randomize_register (MicrocodeAddress &start, Microcode *prog,
		      const Architecture *arch, const char *regname)
{
  const RegisterDesc *reg = arch->get_register (regname);
  int regsize = reg->get_register_size ();
  prog->add_assignment (start, 
			RegisterExpr::create (reg, 0, regsize),
			RandomValue::create (regsize));
}

static void
s_sink_node (MicrocodeAddress &start, Microcode *prog)
{
  prog->get_or_create_node (start);
}

static void
s_add_return (MicrocodeAddress &start, Microcode *prog, 
	      const Architecture *arch)
{
  RegisterExpr *esp = RegisterExpr::create (arch->get_register ("esp"), 0, 32);

  /* esp <- esp + 4 */
  prog->add_assignment (start, esp->ref (),
			BinaryApp::create (BV_OP_ADD, esp->ref (), 4));

  MicrocodeNode *start_node = prog->get_node (start);
  start_node->add_annotation (CallRetAnnotation::ID,
			      CallRetAnnotation::create_ret ());
  /* jmp -4(%esp) */
  prog->add_jump (start, 
		  MemCell::create (BinaryApp::create (BV_OP_SUB, 
						      esp->ref (), 4),
				   0, 32)
		  );
  esp->deref ();
}

void
ELF_x86_32_StubFactory::add_stubs (ConcreteMemory *memory, 
				   MicrocodeArchitecture *arch,
				   Microcode *dest,
				   SymbolTable *)
{
  address_t dummy;
  address_t dest_slot;
  const Architecture *rarch = arch->get_reference_arch ();

  memory->get_address_range (dummy, dest_slot);

  for (SlotMap::const_iterator s = slots.begin (); s != slots.end (); s++)
    {     
      const string &name = s->first;
      address_t slot = slots[s->first];

      assert (memory->is_defined (slot));

      memory->put (ConcreteAddress (slot), ConcreteValue (32, dest_slot), 
		   rarch->get_endian ());
      memory->put (ConcreteAddress (dest_slot), ConcreteValue (32, dest_slot), 
		   rarch->get_endian ());

      MicrocodeAddress start (dest_slot);

      if (name == "__libc_start_main")
	s_jump_to_top_of_stack (start, dest, rarch);
      else if (name == "exit")
	s_sink_node (start, dest);
      else
	{
	  s_randomize_register (start, dest, rarch, "eax");
	  s_randomize_register (start, dest, rarch, "ecx");
	  s_randomize_register (start, dest, rarch, "edx");
	  s_add_return (start, dest, rarch);
	}
      
      MicrocodeNode *start_node = dest->get_node (dest_slot);
      if (start_node != NULL)
	{
	  string a("insight-stub/");
	  a += name;
	  start_node->add_annotation (AsmAnnotation::ID, new AsmAnnotation (a));
	}
      dest_slot += 4;
    }
}

string
ELF_x86_32_StubFactory::dynamic_symbol_name (arelent *e, int &symcounter)
{
  string result;
  if (e->sym_ptr_ptr == NULL || *e->sym_ptr_ptr == NULL)
    {
      do 
	{
	  ostringstream oss;
	  oss << "insight_stub_" << symcounter++;
	  result = oss.str ();
	} 
      while (slots.find (result) != slots.end ());
    }
  else
    {
      result = bfd_asymbol_name (*e->sym_ptr_ptr);
      assert (slots.find (result) == slots.end ());
    }

  return result;
}


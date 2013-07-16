/*
 * Copyright (c) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 * 
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#include <sstream>
#include <kernel/annotations/NextInstAnnotation.hh>
#include <kernel/annotations/AsmAnnotation.hh>
#include "asm-writer.hh"

static std::string 
s_instruction_bytes (const BinaryLoader *loader, const ConcreteAddress &start,
		     const ConcreteAddress &next)
{
  std::ostringstream result;
  ConcreteMemory *m = loader->get_memory ();

  for (ConcreteAddress a = start; ! a.equals (next); a++)
    result << std::hex << std::setfill('0') << std::setw (2) 
	   << m->get (a, 1, Architecture::LittleEndian).get () << ' ';
  return result.str ();
}

void 
asm_writer (std::ostream &out, const Microcode *mc, const BinaryLoader *loader,
	    bool with_bytes)
{
  for (Microcode::node_iterator N = mc->begin_nodes (); N != mc->end_nodes (); 
       N++)
    {
      if (! (*N)->has_annotation (AsmAnnotation::ID))
	continue;
      MicrocodeAddress ma ((*N)->get_loc ());

      if (loader && ma.getLocal () == 0)
	{
	  Option<std::string> fun = loader->get_symbol_name (ma.getGlobal ());

	  if (fun.hasValue ())
	    {
	      out << std::right << std::hex << std::setfill ('0') 
		  << std::setw (8) 
		  << ma.getGlobal () 
		  << std::setw (0) 
		  << " <" << fun.getValue () << ">: " << std::endl;
	    }
	}
      AsmAnnotation *a = (AsmAnnotation *) 
	(*N)->get_annotation (AsmAnnotation::ID);

      out << std::right << std::hex << std::setw (8) << std::setfill (' ')
	  << (*N)->get_loc ().getGlobal () << ":\t";
      if (with_bytes)
	{
	  std::string bytes;

	  if ((*N)->has_annotation (NextInstAnnotation::ID))
	    {
	      ConcreteAddress next;
	      NextInstAnnotation *nia = (NextInstAnnotation *)
		(*N)->get_annotation (NextInstAnnotation::ID);
	      next = nia->get_value ().getGlobal ();
	      bytes = s_instruction_bytes (loader, ma.getGlobal (), next);
	    }
	  else
	    {
	      bytes = "(unknown)";
	    }
	  out << std::left << std::setw (24) << std::setfill (' ') 
	      << bytes << "\t";
	}
      out << a->get_value ();
      out << std::endl;
    }
}

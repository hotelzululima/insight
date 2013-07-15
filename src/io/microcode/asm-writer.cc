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
#include <kernel/annotations/AsmAnnotation.hh>
#include "asm-writer.hh"

void 
asm_writer (std::ostream &out, const Microcode *mc, const BinaryLoader *loader)
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
	      out << std::hex << std::setfill ('0') << std::setw (8) 
		  << ma.getGlobal () 
		  << std::setw (0) 
		  << " <" << fun.getValue () << ">: " << std::endl;
	    }
	}
      AsmAnnotation *a = (AsmAnnotation *) 
	(*N)->get_annotation (AsmAnnotation::ID);

      out << std::right << std::hex << std::setw (8) << std::setfill (' ')
	  << (*N)->get_loc ().getGlobal () << ":\t" 
	  << a->get_value () << std::endl;
    }
}

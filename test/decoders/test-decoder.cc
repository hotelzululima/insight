/*-
 * Copyright (C) 2010-2012, Centre National de la Recherche Scientifique,
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

#include <iostream>
#include <cstdlib>

#include <decoders/binutils/BinutilsDecoder.hh>
#include <kernel/Insight.hh>
#include <loaders/LoaderFactory.hh>

using namespace std;
using namespace binutils;

int 
main (int argc, char **argv)
{
  int result = EXIT_SUCCESS;

  Insight::init ();
  Log::add_listener (Log::STD_STREAM_LOG);

  if (argc != 2)
    {
      cerr << "wrong # of arguments" << endl;
      cerr << "USAGE: " << argv[0] << " binary-filename" << endl;
      result = EXIT_FAILURE;
    }
  else
    {
      const char *filename = argv[1];
      BinaryLoader *loader = LoaderFactory::get_BinaryLoader (filename);
      ConcreteMemory *memory = loader->get_memory();
      MicrocodeArchitecture arch (loader->get_architecture ());
      BinutilsDecoder *decoder = new BinutilsDecoder (&arch, memory);
      ConcreteAddress start (loader->get_entrypoint());

      while (memory->is_defined (start) && result == EXIT_SUCCESS)
	{
	  Microcode *mc = new Microcode ();
	  
	  try
	    {
	      cout << "**** Decode instruction: " 
		   << decoder->get_instruction (start) 
		   << endl;
	      start = decoder->decode (mc, start);

	      mc->sort ();
	      cout << mc->pp () << endl;
	    }
	  catch (std::runtime_error &e)
	    {
	      cerr << e.what() << endl;
	      result = EXIT_FAILURE;
	    }
	  
	  delete mc;
	}

      delete loader;
      delete decoder;
      delete memory;
    }
  Insight::terminate ();

  return result;
}

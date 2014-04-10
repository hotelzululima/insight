/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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

#include <cstdlib>
#include <iostream>

#include <kernel/insight.hh>
#include <kernel/Microcode.hh>
#include <utils/logs.hh>
#include <io/microcode/xml_microcode_parser.hh>
#include <io/microcode/xml_microcode_generator.hh>


using namespace std;

int 
main (int argc, char **argv)
{
  int result = EXIT_SUCCESS;
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);

  if (argc != 3)
    {
      logs::error << "wrong # of arguments" << endl
		  << "USAGE: " << argv[0] << " bfdtarget xml-file" << endl;
      result = EXIT_FAILURE;
    }
  else
    {
      const string archname (argv[1]);
      const char *filename = argv[2];

      try
	{
	  const Architecture *arch;

	  if (archname == "x86_32")
	    arch = Architecture::getArchitecture (Architecture::X86_32);
	  else if (archname == "x86_64")
	    arch = Architecture::getArchitecture (Architecture::X86_64);
	  else
	    throw Architecture::UnsupportedArch ();

	  MicrocodeArchitecture march (arch);
	  Microcode *program = xml_parse_mc_program (filename, &march);
          xml_of_microcode (logs::display, program, &march);
          delete program;
	}
      catch (runtime_error e)
	{
	  logs::error << e.what () << endl;
	  result = EXIT_FAILURE;
	}
    }
  insight::terminate ();

  return result;
}

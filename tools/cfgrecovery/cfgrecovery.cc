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

#include <fstream>
#include <iostream>
#include <map>

#include <tr1/unordered_map>

#include <getopt.h>
#include <libgen.h>
#include <stdlib.h>

#include <decoders/binutils/BinutilsDecoder.hh>
#include <kernel/Insight.hh>
#include <io/binaryloaders/BinutilsBinaryLoader.hh>
#include <io/microcodewriters/xml_microcode_generator.hh>

#include "linearsweep.hh"
#include "recursivetraversal.hh"

#include "cfgrecovery.hh"

using namespace std;
using namespace binutils;

typedef
  tr1::unordered_map < string, string, tr1::hash<string> > disas_t;

/* Global options */
int verbosity = 0;	           /* verbosity level */
ostream * output;                  /* output stream */
ofstream output_file;              /* output file */

/* usage(status): Display the usage of the program and quit with
 * 'status' as return value. */
static void
usage (int status)
{
  if (status != EXIT_SUCCESS)
    {
      cerr << "Try `" << prog_name << " --help' for more information."
	<< endl;
    }
  else
    {
      cout << "Usage: " << prog_name << " [OPTION] EXECFILE..." << endl;

      cout << "Rebuild the CFG based on the analysis of the binary." << endl
	<< endl
	<< "  -d, --disas TYPE\tselect disassembler type" << endl
	<< "  -l, --list\t\tlist all disassembler types" << endl
	<< "  -e, --entrypoint ADDR\tforce entry point" << endl
	<< "  -f, --format FMT\toutput format mc|dot|xml (default: mc)" << endl
	<< "  -o, --output FILE\twrite output to FILE" << endl
	<< "  -h, --help\t\tdisplay this help" << endl
	<< "  -v, --verbose\t\tincrease verbosity level" << endl
	<< "  -V, --version\t\tdisplay version and exit" << endl;
    }

  exit (status);
}


/* version(): Display the version number and quit with success. */
static void
version ()
{
  cout << prog_name << " " << CFG_RECOVERY_VERSION << endl;

  cout << endl
    << "This software tries to rebuild the original CFG based only" << endl
    << "on an analysis performed on the executable file. It provides" << endl
    << "several ways of recovering the CFG of a binary. It is" << endl
    << "programmed for investigation purpose and has no pretention" << endl
    << "to be exhaustive or trustable for now." << endl;

  exit (EXIT_SUCCESS);
}

int
main (int argc, char *argv[])
{
  /* Various option values */
  int optc;
  string output_filename;

  /* Default output format (_mc_, dot, xml) */
  string output_format = "mc";

  /* Long options struct */
  struct option const
    long_opts[] = {
    {"disas", required_argument, NULL, 'd'},
    {"list", no_argument, NULL, 'l'},
    {"entrypoint", required_argument, NULL, 'e'},
    {"format", required_argument, NULL, 'f'},
    {"output", required_argument, NULL, 'o'},
    {"help", no_argument, NULL, 'h'},
    {"verbose", no_argument, NULL, 'v'},
    {"version", no_argument, NULL, 'V'},
    {NULL, 0, NULL, 0}
  };

  /* Setting the list of disassembly types */
  disas_t disassemblers;

  disassemblers["linear"] = "linear sweep";
  disassemblers["recursive"] = "recursive traversal";
  disassemblers["predicate"] = "path predicate validation";
  disassemblers["dare"] = "directed automated random exploration";
  disassemblers["kinder1"] = "CFG reconstruction by abstract interpretation";
  disassemblers["kinder2"] = "alternating CFG reconstruction";

  /* Setting default disassembly type */
  string disassembler = "linear";

  /* Setting entrypoint */
  ConcreteAddress * entrypoint = NULL;

  /* Parsing options */
  while ((optc =
	  getopt_long (argc, argv, "ld:e:f:o:hvV", long_opts, NULL)) != -1)
    switch (optc)
      {
      case 'd':		/* Select disassembly type */
	disassembler = string(optarg);
	break;

      case 'l':		/* List disassembly types */
	cout << "Disassembler types ('value to pass' = description):" << endl;
	/* FIXME: Should order the displayed list to get a better output */
	for (disas_t::iterator it = disassemblers.begin ();
	     it != disassemblers.end (); ++it)
	  {
	    cout << "  '" << it->first << "' = " << it->second << endl;
	  }
	exit (EXIT_SUCCESS);
	break;

      case 'e':		/* Force entrypoint */
	entrypoint = new ConcreteAddress(strtoul (optarg, NULL, 0));
	break;

      case 'f':		/* Output file format */
	output_format = string(optarg);

	/* Checking if the format is known */
	if ((output_format != "mc")  &&
	    (output_format != "dot") &&
	    (output_format != "xml"))
	  {
	    cerr << prog_name
		 << ": error: '" << output_format << "' unknown format" << endl;
	    usage(EXIT_FAILURE);
	  }
	break;

      case 'o':		/* Output file name */
	output_filename = string(optarg);
	break;

      case 'h':		/* Display usage and exit */
	usage (EXIT_SUCCESS);
	break;

      case 'v':		/* Verbosity */
	verbosity += 1;
	break;

      case 'V':		/* Display version number and exit */
	version ();
	break;

      default:
	usage (EXIT_FAILURE);
      }

  /* Checking that an input file is given */
  if (!(optind <= argc - 1))
    {
      cerr << prog_name << ": error: no executable given" << endl;
      usage (EXIT_FAILURE);
    }

  /* Setting the output */
  streambuf * buffer;

  if (output_filename != "")
    {
      output_file.open(output_filename.c_str());
      if (!output_file.is_open())
	{
	  string err_msg =
	    prog_name + ": error opening file '" + output_filename + "'";
	  perror(err_msg.c_str());
	  exit(EXIT_FAILURE);
	}
      buffer = output_file.rdbuf();
    }
  else
    {
      buffer = cout.rdbuf();
    }

  output =  new ostream(buffer);

  /* Getting the execfile from command line */
  string execfile_name = argv[optind];

  /* Starting insight and initializing the needed objects */
  Insight::init();

  /* Getting the loader */
  BinaryLoader * loader;
  try {
    loader = new BinutilsBinaryLoader(execfile_name);
  } catch (BinaryLoader::UnknownBinaryFormat) {
    cerr << prog_name
	 << ": error: unsupported binary format" << endl;
    exit (EXIT_FAILURE);
  } catch (Architecture::UnsupportedArch) {
    cerr << prog_name
	 << ": error: unsupported architecture" << endl;
    exit (EXIT_FAILURE);
  }

  if (verbosity > 0)
    cout << "Binary format: " << loader->get_format() << endl;

  /* Getting the ConcreteMemory */
  ConcreteMemory * memory = loader->get_memory();

  /* Setting the entrypoint */
  if (entrypoint == NULL)
    entrypoint = new ConcreteAddress(loader->get_entrypoint());

  if (verbosity > 0)
    cout << "Entrypoint: 0x" << hex << *entrypoint << dec << endl;

  /* Getting the decoder */
  MicrocodeArchitecture arch(loader->get_architecture());
  BinutilsDecoder * decoder = new BinutilsDecoder(&arch, memory);

  /* Initializing Microcode program */
  Microcode * mc = NULL;

  /* Starting disassembly with proper disassembler */
  if (disassembler == "linear")
    {
      if (verbosity > 0)
	cout << "Starting linear sweep disassembly" << endl;

      mc = linearsweep(entrypoint, memory, decoder);
    }
  else if (disassembler == "recursive")
    {
      if (verbosity > 0)
	cout << "Starting recursive traversal disassembly" << endl;

      mc = recursivetraversal(entrypoint, memory, decoder);
    }
  else if (disassembler == "predicate")
    {
      cerr << prog_name
	   << ": error: '" << disassembler << "' disassembler is not yet implemented" << endl;
      usage(EXIT_FAILURE);
    }
  else if (disassembler == "dare")
    {
      cerr << prog_name
	   << ": error: '" << disassembler << "' disassembler is not yet implemented" << endl;
      usage(EXIT_FAILURE);
    }
  else if (disassembler == "kinder1")
    {
      cerr << prog_name
	   << ": error: '" << disassembler << "' disassembler is not yet implemented" << endl;
      usage(EXIT_FAILURE);
    }
  else if (disassembler == "kinder2")
    {
      cerr << prog_name
	   << ": error: '" << disassembler << "' disassembler is not yet implemented" << endl;
      usage(EXIT_FAILURE);
    }
  else
    {
      cerr << prog_name
	   << ": error: '" << disassembler << "' disassembler is unknown" << endl
	   << "Type '" << prog_name << " -l' to list all disassemblers" << endl;
      exit (EXIT_FAILURE);
    }

  mc->sort ();
    
  /* Displaying the microcode */
  if (output_format == "mc")
    *output << mc->pp() << endl;
  else if (output_format == "dot")
    mc->toDot(*output);
  else if (output_format == "xml")
    {
      *output << xml_of_microcode(mc);
    }
  else
    {
      cerr << prog_name
	   << ": error: '" << output_format << "' unknown format" << endl;
      usage(EXIT_FAILURE);
    }

  /* Cleaning all from Insight */
  delete mc;
  delete decoder;
  delete memory;
  delete entrypoint;
  delete loader;

  Insight::terminate();

  /* Cleaning other stuff */
  delete output;

  return (EXIT_SUCCESS);
}

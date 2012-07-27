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

#include <kernel/insight.hh>

#include <loaders/LoaderFactory.hh>
#include <decoders/binutils/BinutilsDecoder.hh>

#include "cfgrecovery.hh"

using namespace std;
using namespace binutils;

/* global variables */
ofstream outfile ("cfg.mc", ios_base::in);	/* output file */
string prog_name = "cfgrecovery";	        /* program name  */
int verbosity = 0;		                /* verbosity level */

typedef
  std::tr1::unordered_map < int,
			    std::string,
			    std::tr1::hash<int> > disas_map_t;

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
	<< "  -e, --entrypoint ADDR\tforce entry point" << endl
	<< "  -l, --list\t\tlist all disassembly types" << endl
	<< "  -t, --type #TYPE\tselect disassembly type" << endl
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

/* Linear sweep disassembly method */
Microcode *
linearsweep (const ConcreteAddress * entrypoint,
	     ConcreteMemory * memory,
	     Decoder * decoder)
{
  Microcode * mc = new Microcode();
  ConcreteAddress current = *entrypoint;

  while (memory->is_defined(current))
    {
      current = decoder->decode(mc, current);
      cout << mc->pp() << endl;
    }

  return mc;
}

int
main (int argc, char *argv[])
{
  /* Option values */
  int optc;

  /* Long options struct */
  struct option const
    long_opts[] = {
    {"entrypoint", required_argument, NULL, 'e'},
    {"list", no_argument, NULL, 'l'},
    {"type", required_argument, NULL, 't'},
    {"output", required_argument, NULL, 'o'},
    {"verbose", no_argument, NULL, 'v'},
    {"version", no_argument, NULL, 'V'},
    {"help", no_argument, NULL, 'h'},
    {NULL, 0, NULL, 0}
  };

  disas_map_t disas_types;

  /* Setting the list of disassembly types */
  disas_types[LINEAR_SWEEP] = "Linear sweep";
  disas_types[RECURSIVE_TRAVERSAL] = "Recursive traversal";
  disas_types[PATH_PREDICATE] = "Path predicate";
  disas_types[DART] = "Directed automated random testing";
  disas_types[KINDER_1] =
    "CFG reconstruction by abstract interpretation";
  disas_types[KINDER_2] = "Alternating CFG reconstruction";

  /* Setting default choice */
  disas_types[DEFAULT] = disas_types[LINEAR_SWEEP];

  /* Setting default disassembly type */
  int disas_type = DEFAULT;

  /* Setting entrypoint */
  ConcreteAddress * entrypoint;

  /* Parsing options */
  while ((optc =
	  getopt_long (argc, argv, "e:hlt:o:vV", long_opts, NULL)) != -1)
    switch (optc)
      {
      case 'e':		/* Force entrypoint */
	entrypoint = new ConcreteAddress(strtoul (optarg, NULL, 0));
	break;

      case 'h':		/* Display usage and exit */
	usage (EXIT_SUCCESS);
	break;

      case 'l':		/* List disassembly types */
	cout << "Disassembly types (value to pass):" << endl;
	for (disas_map_t::iterator it = disas_types.begin ();
	     it != disas_types.end (); ++it)
	  {
	    if (it->first != DEFAULT)
	      cout << " - " << it->second << " (" << it->first << ")" << endl;
	  }
	exit (EXIT_SUCCESS);
	break;

      case 't':		/* Select disassembly type */
	disas_type = atoi(optarg);
	break;

      case 'o':		/* Output file */
	outfile.open (optarg, ios_base::in);
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

  string execfile_name = argv[optind];

  /* Starting insight and initializing the needed objects */
  Insight::init();

  /* Getting the loader */
  BinaryLoader * loader;
  try {
    loader = LoaderFactory::get_BinaryLoader(execfile_name);
  } catch (UnknownBinaryFormat) {
    cerr << prog_name
	 << ": error: unsupported binary format" << endl;
    exit (EXIT_FAILURE);
  } catch (UnsupportedArch) {
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
  Microcode * mc;

  /* Starting disassembly with proper disassembly type */
  switch (disas_type)
    {
    case DEFAULT:
    case LINEAR_SWEEP:
      if (verbosity > 0)
	cout << "Starting linear sweep disassembly" << endl;
      mc = linearsweep(entrypoint, memory, decoder);
      break;

    case RECURSIVE_TRAVERSAL:
      cerr << prog_name
	   << ": error: disassembly type not yet implemented" << endl;
      usage(EXIT_FAILURE);
      break;

    case PATH_PREDICATE:
      cerr << prog_name
	   << ": error: disassembly type not yet implemented" << endl;
      usage(EXIT_FAILURE);
      break;

    case DART:
      cerr << prog_name
	   << ": error: disassembly type not yet implemented" << endl;
      usage(EXIT_FAILURE);
      break;

    case KINDER_1:
      cerr << prog_name
	   << ": error: disassembly type not yet implemented" << endl;
      usage(EXIT_FAILURE);
      break;

    case KINDER_2:
      break;

    default:
      cerr << prog_name
	   << ": error: '" << disas_type << "' unknown disassembly type" << endl
	   << "Please, try '" << prog_name << " -l' for all possible types"
	   << endl;
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
  outfile.close ();

  exit (EXIT_SUCCESS);
}

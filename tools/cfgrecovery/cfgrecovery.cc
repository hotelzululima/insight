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

#include <ctype.h>
#include <getopt.h>
#include <libgen.h>
#include <stdlib.h>

#include <kernel/insight.hh>
#include <kernel/expressions/ExprSolver.hh>

#include <decoders/binutils/BinutilsDecoder.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <io/microcode/xml_microcode_generator.hh>
#include <io/microcode/asm-writer.hh>
#include <io/microcode/dot-writer.hh>

#include <config.h>
#include "FloodTraversal.hh"
#include "linearsweep.hh"
#include "recursivetraversal.hh"
#include "symbexec.hh"

#include "cfgrecovery.hh"

using namespace std;

/* Global options */
int verbosity = 0;	           /* verbosity level */
ostream * output;                  /* output stream */
ofstream output_file;              /* output file */
static ConfigTable CONFIG;
const ConfigTable *CFGRECOVERY_CONFIG = &CONFIG;

struct disassembler {
  const char *name;
  const char *desc;
  Microcode * (*process)(const ConcreteAddress *, ConcreteMemory *, Decoder *);
} disassemblers[] = {
  /* List must be kept sorted by name */
  { "dare", "directed automated random exploration", NULL },
  { "flood", "flood traversal", flood_traversal },
  { "kinder1", "CFG reconstruction by abstract interpretation", NULL },
  { "kinder2", "alternating CFG reconstruction", NULL },
  { "linear", "linear sweep", linearsweep },
  { "predicate", "path predicate validation", NULL },
  { "recursive", "recursive traversal", recursivetraversal },
  { "symsim", "symbolic traversal (require a SMT solver supporting QF_AUFBV.", 
    symbexec },
  /* List must be kept sorted by name */
  { NULL, NULL, NULL }
};

#define NDISASSEMBLERS ((sizeof disassemblers / sizeof disassemblers[0])-1)

static struct disassembler *
disassembler_lookup(const char *name) {
  for (size_t i = 0; i < NDISASSEMBLERS; i++)
    if (strcmp(disassemblers[i].name, name) == 0)
      return disassemblers + i;

  return NULL;
}

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
	   << "  -c, --config FILE\t specify configuration filename (default " 
	   << CFGRECOVERY_CONFIG_FILENAME << ")" << endl
	   << "  -d, --disas TYPE\tselect disassembler type" << endl
	   << "  -l, --list\t\tlist all disassembler types" << endl
	   << "  -e, --entrypoint ADDR\tforce entry point" << endl
	   << "  -f, --format FMT\toutput format asm|mc|dot|asm-dot|xml (default: mc)" 
	   << endl
	   << "  -o, --output FILE\twrite output to FILE" << endl
	   << "  -h, --help\t\tdisplay this help" << endl
	   << "  -v, --verbose\t\tincrease verbosity level" << endl
	   << "  -D, --debug\t\tenable debug traces" << endl
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
  string config_filename = CFGRECOVERY_CONFIG_FILENAME;

  /* Default output format (asm, _mc_, dot, asm-dot, xml) */
  string output_format = "mc";

  /* Long options struct */
  struct option const
    long_opts[] = {
    {"config", required_argument, NULL, 'c'},
    {"disas", required_argument, NULL, 'd'},
    {"list", no_argument, NULL, 'l'},
    {"entrypoint", required_argument, NULL, 'e'},
    {"format", required_argument, NULL, 'f'},
    {"output", required_argument, NULL, 'o'},
    {"help", no_argument, NULL, 'h'},
    {"debug", no_argument, NULL, 'D'},
    {"verbose", no_argument, NULL, 'v'},
    {"version", no_argument, NULL, 'V'},
    {NULL, 0, NULL, 0}
  };

  /* Setting default disassembly type */
  const char *disassembler = "linear";

  /* Setting entrypoint */
  ConcreteAddress * entrypoint = NULL;
  const char *entrypoint_symbol = NULL;

  /* Setting debug trace */
  bool enable_debug = false;
  /* Parsing options */
  while ((optc =
	  getopt_long (argc, argv, "ld:e:f:o:hDvV", long_opts, NULL)) != -1)
    switch (optc)
      {
      case 'c':		/* Config file name */
	{
	  fstream f (optarg, fstream::in);
	  if (f.is_open ())
	    {
	      config_filename = string(optarg);
	      f.close();
	    }
	  else
	    {
	      cerr << "warning: can't open configuration file '" 
		   << optarg << "'." << endl;
	    }
	}
	break;

      case 'd':		/* Select disassembly type */
	disassembler = optarg;
	break;

      case 'l':		/* List disassembly types */
	cout << "Disassembler types ('value to pass' = description):" << endl;
	for (size_t i = 0; i < NDISASSEMBLERS; i++) {
	    cout << "  '" << disassemblers[i].name << "' = " <<
	      disassemblers[i].desc << endl;
	}
	exit (EXIT_SUCCESS);
	break;

      case 'e':		/* Force entrypoint */
	if (isdigit(optarg[0])) {
	  entrypoint = new ConcreteAddress(strtoul (optarg, NULL, 0));
	  entrypoint_symbol = NULL;
	} else {
	  entrypoint_symbol = optarg;
	  if (entrypoint != NULL) {
	    entrypoint = NULL;
	    delete entrypoint;
	  }
	}
	break;

      case 'f':		/* Output file format */
	output_format = string(optarg);

	/* Checking if the format is known */
	if ((output_format != "asm")  &&
	    (output_format != "mc")  &&
	    (output_format != "dot") &&
	    (output_format != "asm-dot") &&
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

      case 'D':
	enable_debug = true;
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
  
  CONFIG.set (logs::STDIO_ENABLED_PROP, true);
  CONFIG.set (logs::DEBUG_ENABLED_PROP, enable_debug);
  CONFIG.set (ExprSolver::DEBUG_TRACES_PROP, false);
  if (enable_debug)
    {
      CONFIG.set (logs::STDIO_DEBUG_IS_CERR_PROP, true);
      CONFIG.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);
    }
#if HAVE_Z3_SOLVER
  CONFIG.set (ExprSolver::DEFAULT_COMMAND_PROP, "z3");
  CONFIG.set (ExprSolver::DEFAULT_NB_ARGS_PROP, 2);
  CONFIG.set (ExprSolver::DEFAULT_ARG_PROP (0), "-smt2");
  CONFIG.set (ExprSolver::DEFAULT_ARG_PROP (1), "-in");
#endif

  {
    fstream f (config_filename.c_str (), fstream::in);
    if (f.is_open ())
      {
	CONFIG.load (f);
	f.close();
      }
  }

  insight::init (CONFIG);

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
  if (entrypoint_symbol != NULL) {
    Option<ConcreteAddress> val =
      loader->get_symbol_value(string(entrypoint_symbol));
    if (val.hasValue())
      entrypoint = new ConcreteAddress(val.getValue());
    else {
      cerr << "Error: symbol '" << entrypoint_symbol << "' not found" << endl;
      exit(EXIT_FAILURE);
    }
  }

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
  struct disassembler *dis = disassembler_lookup(disassembler);
  if (dis == NULL) {
    cerr << prog_name
	 << ": error: '" << disassembler << "' disassembler is unknown" << endl
	 << "Type '" << prog_name << " -l' to list all disassemblers" << endl;
    exit (EXIT_FAILURE);
  }

  if (dis->process == NULL) {
    cerr << prog_name << ": error: '" << dis->name << " (" << dis->desc <<
      ")' disassembler is not yet implemented" << endl;
    usage(EXIT_FAILURE);
  }

  if (verbosity > 0)
    cout << "Starting " << dis->desc << " disassembly" << endl;

  mc = dis->process(entrypoint, memory, decoder);

  mc->sort ();
    
  /* Displaying the microcode */
  if (output_format == "asm")
    asm_writer (*output, mc);
  else if (output_format == "mc")
    *output << mc->pp() << endl;
  else if (output_format == "dot" || output_format == "asm-dot")
    {
      int asmonly = (output_format == "asm-dot");
      dot_writer (cout, mc, asmonly, execfile_name, entrypoint, loader);
    }
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

  insight::terminate();

  /* Cleaning other stuff */
  delete output;

  return (EXIT_SUCCESS);
}

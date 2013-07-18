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

#include <signal.h>
#include <ctype.h>
#include <getopt.h>
#include <libgen.h>
#include <stdlib.h>

#include <kernel/insight.hh>
#include <kernel/expressions/ExprSolver.hh>

#include <decoders/binutils/BinutilsDecoder.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <io/microcode/xml_microcode_generator.hh>
#include <io/microcode/xml_microcode_parser.hh>
#include <io/microcode/asm-writer.hh>
#include <io/microcode/dot-writer.hh>

#include <config.h>
#include "algorithms.hh"
#include "cfgrecovery.hh"

using namespace std;

#define OUTPUT_FORMATS \
  FORMAT(OF_ASM, "asm", "assembler code", ".asm") \
  FORMAT(OF_ASM_DOT, "asm-dot", "assembler code on a dot graph", ".asm.dot") \
  FORMAT(OF_MC, "mc", "microcode", ".mc") \
  FORMAT(OF_MC_DOT, "mc", "microcode on a dot graph", ".mc.dot") \
  FORMAT(OF_XML, "xml", "microcode in XML format", ".mc.xml") 

#define FORMAT(id,name,desc,ext) id, 
enum OutputFormatID  { OUTPUT_FORMATS OF_UNKNOWN };
#undef FORMAT

struct OutputFormat {
  OutputFormatID id;
  const char *name;
  const char *desc;
  const char *extension;
};

#define FORMAT(id,name,desc,ext) { id, name, desc, ext }, 
static const OutputFormat FORMATS[] = { 
  OUTPUT_FORMATS 
  FORMAT(OF_UNKNOWN, NULL, NULL, NULL) 
};
#undef FORMAT

#define DEFAULT_FORMAT (&FORMATS[OF_ASM])

/* Global options */
int verbosity = 0;	           /* verbosity level */
static ConfigTable CONFIG;
const ConfigTable *CFGRECOVERY_CONFIG = &CONFIG;
static int asm_with_bytes = 0;
static int asm_with_holes = 0;
static int asm_with_labels = 0;

struct disassembler {
  const char *name;
  const char *desc;
  void (*process)(const ConcreteAddress &, ConcreteMemory *, Decoder *,
		  Microcode *);
} disassemblers[] = {
  /* List must be kept sorted by name */
  { "flood", "flood traversal", flood_traversal },
  { "linear", "linear sweep", linear_sweep },
  { "recursive", "recursive traversal", recursive_traversal },
  { "symsim", "symbolic simulation", symbolic_simulator },
  { "sim=symbolic", "symbolic simulation", symbolic_simulator },
  { "sim=concrete", "simulation within concrete domain", concrete_simulator },
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
	   << "  -f, --formats FMT\toutput format " << FORMATS->name;
      
      for (const OutputFormat *of = FORMATS + 1; of->id != OF_UNKNOWN; of++)
	cout << "|" << of->name;
      
      cout << " (default: " << DEFAULT_FORMAT->name << ")" << endl
	   << "  -x, --in FILE\tpreload an existing XML program" << endl
	   << "  -o, --output FILE\twrite outputs to FILE" << endl
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

struct CtrlCHandler : public Microcode::ArrowCreationCallback {
  bool output_program;
  BinaryLoader *loader;
  std::string exec_filename;
  ConcreteAddress *entrypoint;

  void write_microcode (Microcode *mc, OutputFormatID fmt, ostream &output) {
    mc->sort ();
    switch (fmt)
      {
      case OF_ASM :
	asm_writer (output, mc, loader, asm_with_bytes, asm_with_holes,
		    asm_with_labels);
	break;
      case OF_MC :
	mc->output_text (output);
	output << endl;
	break;
      case OF_MC_DOT : 
      case OF_ASM_DOT : 
	dot_writer (output, mc, (fmt == OF_ASM_DOT), 
		    exec_filename, entrypoint, loader);
	break;
      case OF_XML:
	output << xml_of_microcode (mc);
	break;

      default:
	cerr << "internal error. unknown format specified for output." << endl;
	abort ();
      }
  }
    
  virtual void add_node (Microcode *mc, StmtArrow *) {
    if (output_program)
      {
	write_microcode (mc, OF_ASM, logs::warning);    
	output_program = false;
      }
  }
};

static CtrlCHandler CTRL_C_HANDLER;

static void 
s_sighandler (int) 
{
  CTRL_C_HANDLER.output_program = true;
}    

int
main (int argc, char *argv[])
{
  /* Various option values */
  int optc;
  const char *output_filename = NULL;
  const char *preload_filename = NULL;
  string config_filename = CFGRECOVERY_CONFIG_FILENAME;

  /* Default output format (asm, _mc_, dot, asm-dot, xml) */
  list<const OutputFormat *> output_formats;
  
  /* Long options struct */
  struct option const
    long_opts[] = {
    {"config", required_argument, NULL, 'c'},
    {"disas", required_argument, NULL, 'd'},
    {"list", no_argument, NULL, 'l'},
    {"entrypoint", required_argument, NULL, 'e'},
    {"format", required_argument, NULL, 'f'},
    {"in", required_argument, NULL, 'x'},
    {"output", required_argument, NULL, 'o'},
    {"help", no_argument, NULL, 'h'},
    {"debug", no_argument, NULL, 'D'},
    {"verbose", no_argument, NULL, 'v'},
    {"version", no_argument, NULL, 'V'},
    {"asm-with-bytes", no_argument, &asm_with_bytes, 1 }, 
    {"asm-with-holes", no_argument, &asm_with_holes, 1 }, 
    {"asm-with-labels", no_argument, &asm_with_labels, 1 }, 
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
	  getopt_long (argc, argv, "ld:e:f:o:hDvVc:", long_opts, NULL)) != -1)
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
	{
	  string fmt (optarg);
	  const OutputFormat *of = FORMATS;
	  for (; of->id != OF_UNKNOWN; of++) 
	    {
	      if (fmt == of->name)
		{
		  output_formats.push_back (of);
		  break;
		}
	    }
	  if (of->id == OF_UNKNOWN)
	    {
	      cerr << prog_name 
		   << ": error: '" << fmt << "' unknown format" << endl;
	      usage(EXIT_FAILURE);
	    }
	}
	break;

      case 'o':		/* Output file name */
	output_filename = optarg;
	break;

      case 'x':		/* Preloaded file name */
	preload_filename = optarg;
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
      case 0:
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

  /* Getting the execfile from command line */
  string execfile_name = argv[optind];

  /* Starting insight and initializing the needed objects */
  
  CONFIG.set (logs::STDIO_ENABLED_PROP, true);
  CONFIG.set (logs::STDIO_ENABLE_WARNINGS_PROP, verbosity > 0);
  CONFIG.set (logs::DEBUG_ENABLED_PROP, enable_debug);
  CONFIG.set (ExprSolver::DEBUG_TRACES_PROP, false);
  if (enable_debug)
    {
      CONFIG.set (logs::STDIO_DEBUG_IS_CERR_PROP, true);
      CONFIG.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);
    }

  fstream f (config_filename.c_str (), fstream::in);
  if (f.is_open ())
    {
      CONFIG.load (f);
      f.close();
    }

  insight::init (CONFIG);

  /* Getting the loader */
  BinaryLoader * loader;
  try {
    loader = new BinutilsBinaryLoader(execfile_name);
  } catch (Architecture::UnsupportedArch &e) {
    cerr << execfile_name << ": " << e.what() << endl;
    exit(EXIT_FAILURE);
  } catch (std::runtime_error &e) {
    cerr << e.what() << endl;
    exit(EXIT_FAILURE);
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


  if (preload_filename != NULL)
    mc = xml_parse_mc_program (preload_filename);
  else
    mc = new Microcode ();

  CTRL_C_HANDLER.output_program = false;
  CTRL_C_HANDLER.loader = loader;
  CTRL_C_HANDLER.exec_filename = execfile_name;
  CTRL_C_HANDLER.entrypoint = entrypoint;

  if (signal (SIGUSR1, &s_sighandler) != 0)
    logs::error << "unable to set CTRL-C handler." << std::endl;

  try
    {
      mc->add_arrow_creation_callback (&CTRL_C_HANDLER);
      dis->process (*entrypoint, memory, decoder, mc);
    }
  catch (Decoder::Exception &e)
    {
      delete mc;
      mc = NULL;
      cerr << "error: " << e.what () << endl;
    }
  catch (runtime_error &e)
    {
      delete mc;
      mc = NULL;
      cerr << e.what() << endl;
    }

  if (mc == NULL)
    exit (EXIT_FAILURE);

  if (output_formats.empty ())
    output_formats.push_back (DEFAULT_FORMAT);
  
  if (output_filename == NULL)
    {
      for (list<const OutputFormat *>::iterator i = output_formats.begin ();
	   i != output_formats.end (); i++)
	CTRL_C_HANDLER.write_microcode (mc, (*i)->id, cout);
      cout.flush ();
    }
  else 
    {
      for (list<const OutputFormat *>::iterator i = output_formats.begin ();
	   i != output_formats.end (); i++)
	{
	  ostringstream oss;
	  oss << output_filename << (*i)->extension;
	  string filename = oss.str ();
	  ofstream output (filename.c_str ());
	  if (! output.is_open ())
	    {
	      logs::error << prog_name << ": error opening file '" 
			  << filename << "'" << endl;
	      perror (prog_name.c_str ());
	    }
	  else
	    {
	      CTRL_C_HANDLER.write_microcode (mc, (*i)->id, output);
	      output.flush ();
	    }
	}
    }

  /* Cleaning all from Insight */
  delete mc;
  delete decoder;
  delete memory;
  delete entrypoint;
  delete loader;

  insight::terminate();

  return (EXIT_SUCCESS);
}


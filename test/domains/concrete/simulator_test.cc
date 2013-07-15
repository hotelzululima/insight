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

#include <atf-c++.hpp>
#include <string>
#include <sstream>

#include <kernel/annotations/AsmAnnotation.hh>
#include <decoders/DecoderFactory.hh>
#include <analyses/cfgrecovery/AlgorithmFactory.hh>
#include <kernel/insight.hh>
#include <kernel/Microcode.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <utils/logs.hh>


#ifndef TEST_SAMPLES_DIR
# error TEST_SAMPLES_DIR is not defined
#endif

using namespace std;

#define FAILURE_ADDR 0x6666
#define SUCCESS_ADDR 0x1111
#define EXCEPTION_HANDLING_ADDR (FAILURE_ADDR+20)

static Microcode *
s_build_cfg (const ConcreteAddress *entrypoint, ConcreteMemory *memory,
	     Decoder *decoder)
{
  Microcode *result = new Microcode ();
  AlgorithmFactory F;
  
  F.set_memory (memory);
  F.set_decoder (decoder);
  F.set_show_states (false);
  F.set_show_pending_arrows (false);
  F.set_warn_on_unsolved_dynamic_jumps (false);
  F.set_max_number_of_visits_per_address (-1);
  AlgorithmFactory::Algorithm *algo = F.buildConcreteSimulator ();
  algo->compute (*entrypoint, result);
  delete algo;

  return result;
}

static bool
s_program_has_node (Microcode *prg, address_t addr)
{
  bool result;

  try
    {
      MicrocodeAddress ma (addr, 0);
      MicrocodeNode *node = prg->get_node (ma);
      result = node->has_annotation (AsmAnnotation::ID);
    }
  catch (GetNodeNotFoundExc &)
    {
      result = false;
    }
  return result;
}

static void 
s_simulate (const char *filename)
{
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);

  BinaryLoader *loader = new BinutilsBinaryLoader (filename);
  ConcreteMemory *memory = loader->get_memory();
  MicrocodeArchitecture arch (loader->get_architecture ());
  Decoder *decoder = DecoderFactory::get_Decoder (&arch, memory);
  ConcreteAddress start = loader->get_entrypoint ();

  logs::display << "Entry-point := " << start << endl;
  Microcode *prg = s_build_cfg (&start, memory, decoder);
  
  prg->sort ();

  logs::display << "Microcode program : " << endl
		<< prg->pp () << endl;

  ConcreteAddress exception_handling_addr (EXCEPTION_HANDLING_ADDR);
  ATF_REQUIRE (memory->is_defined (exception_handling_addr));
  
  ConcreteValue check_exception = memory->get (exception_handling_addr, 1, 
					       arch.get_endian ());

  if (! check_exception.get ())
    {
      ATF_REQUIRE (s_program_has_node (prg, SUCCESS_ADDR));
      ATF_REQUIRE (! s_program_has_node (prg, FAILURE_ADDR));
    }
  else
    {
      ATF_REQUIRE (! s_program_has_node (prg, SUCCESS_ADDR));
      ATF_REQUIRE (! s_program_has_node (prg, FAILURE_ADDR));
    }
  delete prg;
  delete loader;
  delete decoder;
  delete memory;
  insight::terminate ();

}

#include "simulator_test_cases.hh"

#define BINARY_FILE(id, file) \
ATF_TEST_CASE(id) \
\
ATF_TEST_CASE_HEAD(id)	\
{ \
  set_md_var ("descr", \
	      "Simulate Microcode on binary file '" \
	      TEST_SAMPLES_DIR file "'"); \
} \
\
ATF_TEST_CASE_BODY(id) \
{ \
  s_simulate (TEST_SAMPLES_DIR file); \
}

SIMULATED_BINARIES
#undef BINARY_FILE

#define BINARY_FILE(id, file) \
  ATF_ADD_TEST_CASE(tcs, id);

ATF_INIT_TEST_CASES(tcs)
{
  SIMULATED_BINARIES
}

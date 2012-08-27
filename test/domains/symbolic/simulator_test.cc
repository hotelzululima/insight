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

#include <analyses/microcode_exec.hh>
#include <decoders/DecoderFactory.hh>
#include <domains/symbolic/SymbolicExecContext.hh>
#include <kernel/insight.hh>
#include <kernel/Microcode.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <utils/Log.hh>


#ifndef TEST_SAMPLES_DIR
# error TEST_SAMPLES_DIR is not defined
#endif

using namespace std;

#define EXCEPTION_HANDLING_ADDR 0x12FA792
#define FAILURE_ADDR 0x6666
#define SUCCESS_ADDR 0x1111

static void 
s_simulate (const char *filename)
{
  ConfigTable ct;
  ct.set (log::DEBUG_ENABLED_PROP, false);
  ct.set (log::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);
  {
    BinaryLoader *loader = new BinutilsBinaryLoader (filename);
    ConcreteMemory *memory = loader->get_memory();
    const Architecture *A = loader->get_architecture ();
    // Must initialize registers
    for (RegisterSpecs::const_iterator i = A->get_registers ()->begin ();
	 i != A->get_registers ()->end (); i++)
      {
	if (! i->second->is_alias ())
	  memory->put (i->second, 		     
		       ConcreteValue (i->second->get_register_size (), 0) );
      }
    MicrocodeArchitecture arch (A);

    Decoder *decoder = DecoderFactory::get_Decoder (&arch, memory);
    ConcreteAddress start = loader->get_entrypoint ();

    log::display << "Entry-point := " << start << endl;
    SymbolicExecContext *ctxt = new SymbolicExecContext (memory, decoder);

    ctxt->init (SymbolicContext::empty_context (memory));

    MicrocodeAddress lastaddr;
    MicrocodeAddress newaddr = ctxt->get_current_program_point ().to_address ();

    SymbolicExecContext::Context *last_context = NULL;

    for (;;)
      {      
	lastaddr = newaddr;

	bool simulation_can_continue = ctxt->step();

	if (!(simulation_can_continue && 
	      ctxt->get_current_context ().hasValue ()))
	  break;

	if (last_context != NULL)
	  delete last_context;
	last_context =  ctxt->get_current_context ().getValue ()->clone ();
	last_context->memory->output_text (log::display);
	log::display << endl;

	ATF_REQUIRE (simulation_can_continue);
	ATF_REQUIRE (ctxt->pending_arrows.size () > 0);

	newaddr = ctxt->get_current_program_point ().to_address ();
      
	if (lastaddr.equals (newaddr))
	  {
	    SymbolicExecContext::Arrow pa = ctxt->pending_arrows.front ();

	    if (! pa.arr->is_static ())
	      continue;
	  
	    StaticArrow *a = dynamic_cast<StaticArrow *> (pa.arr);
	    if (a->get_condition () != NULL)
	      {
		SymbolicExecContext::Context *c = 
		  ctxt->get_current_context ().getValue ();
		SymbolicValue v = c->eval (a->get_condition ());
		if (! v.to_bool().getValue ())
		  continue;
	      }
	    if (a->get_target().equals (lastaddr))
	      break;
	  }
      }

    ATF_REQUIRE (last_context != NULL);
  
    ConcreteAddress exception_handling_addr (EXCEPTION_HANDLING_ADDR);
    ATF_REQUIRE (last_context->memory->is_defined (exception_handling_addr));

    SymbolicValue check_exception = 
      last_context->memory->get (exception_handling_addr, 1, 
				 arch.get_reference_arch ()->endianness);

    if (! check_exception.to_bool().getValue ())
      {
	ATF_REQUIRE (lastaddr.getLocal () == 0);
	ATF_REQUIRE (lastaddr.getGlobal () == FAILURE_ADDR ||
		     lastaddr.getGlobal () == SUCCESS_ADDR);
	ATF_REQUIRE (lastaddr.getGlobal () == SUCCESS_ADDR);
      }
    else
      {
	ATF_REQUIRE (lastaddr.getGlobal () != FAILURE_ADDR);
	ATF_REQUIRE (lastaddr.getGlobal () != SUCCESS_ADDR);
	ATF_REQUIRE (ctxt->pending_arrows.size () == 0);
      }
    delete last_context;
    delete ctxt; 
    delete loader;
    delete decoder;
    delete memory;
  }
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

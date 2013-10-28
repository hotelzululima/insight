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

#include <config.h>

#include <kernel/Architecture.hh>
#include <kernel/insight.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <decoders/DecoderFactory.hh>
#include <utils/logs.hh>

#ifndef TEST_SAMPLES_DIR
# error TEST_SAMPLES_DIR is not defined
#endif

using namespace std;
using namespace insight;

ATF_TEST_CASE (BUG_001)
ATF_TEST_CASE_HEAD (BUG_001)
{
  set_md_var("descr",
	     "Check bug 001 related to missing exception on unknown mnemonic");
}

ATF_TEST_CASE_BODY (BUG_001)
{
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);

  BinaryLoader *loader =
    new BinutilsBinaryLoader (TEST_SAMPLES_DIR "x86_32-bug-001.bin", 
			      "elf32-i386", "",
			      Architecture::UnknownEndian);
  ConcreteMemory *memory = new ConcreteMemory ();
  loader->load_memory (memory);
  ConcreteAddress entrypoint (loader->get_entrypoint ());
  MicrocodeArchitecture arch (loader->get_architecture());
  Decoder *decoder = DecoderFactory::get_Decoder (&arch, memory);

  /* Initializing Microcode program */
  Microcode * mc = new Microcode ();

  ATF_REQUIRE_THROW(Decoder::UnknownMnemonic,
		    decoder->decode (mc, entrypoint););

  delete mc;
  delete decoder;
  delete memory;
  delete loader;

  insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE (tcs, BUG_001);
}

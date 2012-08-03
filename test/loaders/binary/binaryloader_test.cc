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
#include <kernel/Insight.hh>
#include <loaders/LoaderFactory.hh>

#ifndef TEST_SAMPLES_DIR
# error TEST_SAMPLES_DIR is not defined
#endif

using namespace std;

ATF_TEST_CASE(binutils_binaryloader_x86_64);
ATF_TEST_CASE_HEAD(binutils_binaryloader_x86_64)
{
  set_md_var("descr",
	     "Check features of binaryloader on an x86-64 binary file");
}
ATF_TEST_CASE_BODY(binutils_binaryloader_x86_64)
{
  Insight::init ();

  ATF_REQUIRE_THROW(UnsupportedArch,
		    try {
		      LoaderFactory::get_BinaryLoader(TEST_SAMPLES_DIR 
						      "echo-linux-amd64"); 
		    } catch (UnknownBinaryFormat) { 
		      throw UnsupportedArch(); 
		    });
  Insight::terminate ();
}

ATF_TEST_CASE(binutils_binaryloader_x86_32);
ATF_TEST_CASE_HEAD(binutils_binaryloader_x86_32)
{
  set_md_var("descr",
	     "Check features of binaryloader on an x86-32 binary file");
}

ATF_TEST_CASE_BODY(binutils_binaryloader_x86_32)
{
  Insight::init ();
  BinaryLoader * loader =
    LoaderFactory::get_BinaryLoader(TEST_SAMPLES_DIR "echo-linux-i386");

  /* Checking various (non-critical) fields from the loader */
  ATF_REQUIRE_EQ(loader->get_filename(),
		 string(TEST_SAMPLES_DIR "echo-linux-i386"));
  ATF_REQUIRE_EQ(loader->get_format(), "elf32-i386");

  /* Checking if the architecture has been properly detected */
  const Architecture * x86_32_arch = loader->get_architecture();
  ATF_REQUIRE_EQ(x86_32_arch->processor, Architecture::X86_32);
  ATF_REQUIRE_EQ(x86_32_arch->endianness, Architecture::LittleEndian);

  /* Checking the entrypoint */
  ConcreteAddress entrypoint = ConcreteAddress(0x804927c);
  ATF_REQUIRE_EQ(loader->get_entrypoint().get_address(),
		 entrypoint.get_address());

  /* Checking if the memory has been properly loaded */
  ConcreteMemory * memory = loader->get_memory();

  ATF_REQUIRE(memory->is_defined(entrypoint));
  ATF_REQUIRE(!memory->is_defined(ConcreteAddress(0x100)));
  Insight::terminate ();
}

ATF_TEST_CASE(binutils_binaryloader_arm);
ATF_TEST_CASE_HEAD(binutils_binaryloader_arm)
{
  set_md_var("descr",
	     "Check features of binaryloader on an ARM binary file");
}

ATF_TEST_CASE_BODY(binutils_binaryloader_arm)
{
  Insight::init ();
  BinaryLoader * loader =
    LoaderFactory::get_BinaryLoader(TEST_SAMPLES_DIR "echo-linux-armel");

  /* Checking various (non-critical) fields from the loader */
  ATF_REQUIRE_EQ(loader->get_filename(),
		 string(TEST_SAMPLES_DIR "echo-linux-armel"));
  ATF_REQUIRE_EQ(loader->get_format(), "elf32-littlearm");

  /* Checking if the architecture has been properly detected */
  const Architecture * x86_32_arch = loader->get_architecture();
  ATF_REQUIRE_EQ(x86_32_arch->processor, Architecture::ARM);
  ATF_REQUIRE_EQ(x86_32_arch->endianness, Architecture::LittleEndian);

  /* Checking the entrypoint */
  ConcreteAddress entrypoint = ConcreteAddress(0x93a4);
  ATF_REQUIRE_EQ(loader->get_entrypoint().get_address(),
		 entrypoint.get_address());

  /* Checking if the memory has been properly loaded */
  ConcreteMemory * memory = loader->get_memory();

  ATF_REQUIRE(memory->is_defined(entrypoint));
  ATF_REQUIRE(!memory->is_defined(ConcreteAddress(0x100)));
  Insight::terminate();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, binutils_binaryloader_x86_64);
  ATF_ADD_TEST_CASE(tcs, binutils_binaryloader_x86_32);
  ATF_ADD_TEST_CASE(tcs, binutils_binaryloader_arm);
}

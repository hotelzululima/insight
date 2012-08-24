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

#include <kernel/Architecture.hh>
#include <kernel/insight.hh>
#include <utils/Log.hh>

ATF_TEST_CASE(architecture_x86_32);
ATF_TEST_CASE_HEAD(architecture_x86_32)
{
  set_md_var("descr",
	     "Check the creation and content of an x86-32 architecture "
	     "description object");
}

static void
s_check_x86_32 (const Architecture * arch_x86_32)
{
  ATF_REQUIRE_EQ(arch_x86_32->processor, Architecture::X86_32);

  /* Check if 'eax' register is here */
  ATF_REQUIRE(arch_x86_32->get_register("eax") != NULL);
  ATF_REQUIRE(arch_x86_32->get_register("eax")->get_register_size () == 32);

  /* Check if 'ah' alias register is here */
  RegisterDesc * ah = (RegisterDesc *) arch_x86_32->get_register("ah");
  ATF_REQUIRE(ah != NULL);
  ATF_REQUIRE(ah->is_alias ());
  ATF_REQUIRE(ah->get_register_size () == 32);
  ATF_REQUIRE(ah->get_window_size () == 8);
  ATF_REQUIRE(ah->get_window_offset () == 8);

  /* Check if an exception is thrown on inexistant register name */
  ATF_REQUIRE_THROW(Architecture::RegisterDescNotFound,
		    arch_x86_32->get_register("xxx"));
}

ATF_TEST_CASE_BODY(architecture_x86_32)
{
  ConfigTable ct;
  ct.set (log::DEBUG_ENABLED_PROP, false);
  ct.set (log::STDIO_ENABLED_PROP, true);

  insight::init (ct);
  /* Check full initialization (x86-32) with both arguments */
  const Architecture * arch_x86_32 =
    Architecture::getArchitecture(Architecture::X86_32,
				  Architecture::LittleEndian);
  ATF_REQUIRE_EQ(arch_x86_32->endianness, Architecture::LittleEndian);

  s_check_x86_32 (arch_x86_32);

  /* Check short initialization (x86-32) */
  arch_x86_32 = Architecture::getArchitecture(Architecture::X86_32);
  ATF_REQUIRE_EQ(arch_x86_32->endianness, Architecture::LittleEndian);

  s_check_x86_32 (arch_x86_32);
  insight::terminate ();
}

ATF_TEST_CASE(architecture_arm);
ATF_TEST_CASE_HEAD(architecture_arm)
{
  set_md_var("descr",
	     "Check the creation and content of an arm architecture "
	     "description object");
}
ATF_TEST_CASE_BODY(architecture_arm)
{
  ConfigTable ct;
  ct.set (log::DEBUG_ENABLED_PROP, false);
  ct.set (log::STDIO_ENABLED_PROP, true);

  insight::init (ct);
  /* Check full initialization (x86-32) with both arguments */
  const Architecture * arch_arm =
    Architecture::getArchitecture(Architecture::ARM,
				  Architecture::LittleEndian);
  ATF_REQUIRE_EQ(arch_arm->processor, Architecture::ARM);
  ATF_REQUIRE_EQ(arch_arm->endianness, Architecture::LittleEndian);

  /* Check if 'r0' register is here */
  ATF_REQUIRE(arch_arm->get_register("r0") != NULL);
  ATF_REQUIRE(arch_arm->get_register("r0")->get_register_size () == 32);

  /* Check if an exception is thrown on inexistant register name */
  ATF_REQUIRE_THROW(Architecture::RegisterDescNotFound,
		    arch_arm->get_register("xxx"));
  insight::terminate ();
}

ATF_TEST_CASE(architecture_missing);
ATF_TEST_CASE_HEAD(architecture_missing)
{
  set_md_var("descr",
	     "Check what happen when wrong arguments are given.");
}
ATF_TEST_CASE_BODY(architecture_missing)
{
  ConfigTable ct;
  ct.set (log::DEBUG_ENABLED_PROP, false);
  ct.set (log::STDIO_ENABLED_PROP, true);

  insight::init (ct);
  /* Check if an exception is thrown on unknown architecture */
  ATF_REQUIRE_THROW(Architecture::UnsupportedArch,
		    Architecture::getArchitecture(Architecture::Unknown));

  /* Check if an exception is thrown on wrong endianness */
  ATF_REQUIRE_THROW(Architecture::UnsupportedArch,
		    Architecture::getArchitecture(Architecture::X86_32,
						      Architecture::BigEndian));

  /* Check if an exception is thrown on unimplemented architecture */
  ATF_REQUIRE_THROW(Architecture::UnsupportedArch,
		    Architecture::getArchitecture(Architecture::Alpha));
  insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, architecture_x86_32);
  ATF_ADD_TEST_CASE(tcs, architecture_arm);
  ATF_ADD_TEST_CASE(tcs, architecture_missing);
}

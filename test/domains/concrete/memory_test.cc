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

#include <domains/concrete/ConcreteMemory.hh>
#include <kernel/Architecture.hh>
#include <kernel/insight.hh>
#include <utils/Log.hh>

ATF_TEST_CASE(concretememory_registers)
ATF_TEST_CASE_HEAD(concretememory_registers)
{
  set_md_var("descr",
	     "Check the registers behavior within a ConcreteMemory object");
}
ATF_TEST_CASE_BODY(concretememory_registers)
{
  ConfigTable ct;
  ct.set (log::DEBUG_ENABLED_PROP, false);
  ct.set (log::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);

  const Architecture * arch_x86 =
    Architecture::getArchitecture(Architecture::X86_32);

  ConcreteMemory * memory = new ConcreteMemory();

  const RegisterDesc * eax = arch_x86->get_register("eax");

  /* Check if an exception is thrown on inexistant register name */
  ATF_REQUIRE_THROW(Architecture::RegisterDescNotFound,
		    arch_x86->get_register("xxx"));

  /* Check if register are undefined */
  ATF_REQUIRE_EQ(memory->is_defined(eax), false);

  /* Check if an exception is thrown on accessing an undefined register */
  ATF_REQUIRE_THROW(UndefinedValueException, memory->get(eax));

  /* Assigning '00000000000000001000000000000000' to eax */
  memory->put(eax, ConcreteValue(32, 32768));

  /* Check if register are undefined */
  ATF_REQUIRE_EQ(memory->is_defined(eax), true);

  /* Check if the put() did work well */
  ATF_REQUIRE(memory->get(eax) == ConcreteValue(32, 32768));

  delete memory;

  insight::terminate ();
}

ATF_TEST_CASE(concretememory_memcells)
ATF_TEST_CASE_HEAD(concretememory_memcells)
{
  set_md_var("descr",
	     "Check the memory cells behavior within a ConcreteMemory object");
}
ATF_TEST_CASE_BODY(concretememory_memcells)
{
  ConfigTable ct;
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);

  ConcreteMemory * memory = new ConcreteMemory();

  /* Check if memcells are undefined */
  ATF_REQUIRE_EQ(memory->is_defined(ConcreteAddress::null_addr()), false);
  ATF_REQUIRE_EQ(memory->is_defined(ConcreteAddress(6234)), false);

  ConcreteAddress addr = ConcreteAddress(1024);
  ConcreteValue value = ConcreteValue(32, 6235);

  memory->put(addr, value, Architecture::LittleEndian);

  /* Check if the put() did work well */
  ATF_REQUIRE(memory->get(addr, 4, Architecture::LittleEndian).get() == 6235);
  ATF_REQUIRE(memory->get(addr, 2, Architecture::LittleEndian).get() == 6235);
  ATF_REQUIRE(memory->get(addr, 1, Architecture::LittleEndian).get() == 91);
  ATF_REQUIRE(memory->get(++(++addr), 2, Architecture::LittleEndian).get() == 0);

  memory->put(addr, value, Architecture::BigEndian);

  /* Check if the put() did work well */
  ATF_REQUIRE(memory->get(addr, 4, Architecture::BigEndian).get() == 6235);
  ATF_REQUIRE(memory->get(addr, 2, Architecture::BigEndian).get() == 0);
  ATF_REQUIRE(memory->get(++(++addr), 2, Architecture::BigEndian).get() == 6235);
  ATF_REQUIRE(memory->get(++addr, 1, Architecture::BigEndian).get() == 91);

  delete memory;

  insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, concretememory_registers);
  ATF_ADD_TEST_CASE(tcs, concretememory_memcells);
}

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

#include <kernel/expressions/exprutils.hh>
#include <domains/symbolic/SymbolicMemory.hh>
#include <kernel/Architecture.hh>
#include <kernel/insight.hh>
#include <utils/logs.hh>

ATF_TEST_CASE(registers)
ATF_TEST_CASE_HEAD(registers)
{
  set_md_var("descr",
	     "Check the registers behavior within a SymbolicMemory object");
}
ATF_TEST_CASE_BODY(registers)
{
  ConfigTable ct;

  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);

  const Architecture * arch_x86 =
    Architecture::getArchitecture(Architecture::X86_32);

  ConcreteMemory *cm = new ConcreteMemory;
  SymbolicMemory * memory = new SymbolicMemory (cm);

  const RegisterDesc * eax = arch_x86->get_register("eax");

  /* Check if an exception is thrown on inexistant register name */
  ATF_REQUIRE_THROW(Architecture::RegisterDescNotFound,
		    arch_x86->get_register("xxx"));

  /* Check if register are undefined */
  ATF_REQUIRE_EQ(memory->is_defined(eax), false);

  /* Check if an exception is thrown on accessing an undefined register */
  ATF_REQUIRE_THROW(UndefinedValueException, memory->get(eax));

  /* Assigning '00000000000000001000000000000000' to eax */
  memory->put(eax, SymbolicValue(32, 32768));

  /* Check if register are undefined */
  ATF_REQUIRE_EQ(memory->is_defined(eax), true);

  /* Check if the put() did work well */
  ATF_REQUIRE(memory->get(eax) == SymbolicValue(32, 32768));

  delete memory;
  delete cm;

  insight::terminate ();
}

ATF_TEST_CASE(memcells)
ATF_TEST_CASE_HEAD(memcells)
{
  set_md_var("descr",
	     "Check the memory cells behavior within a SymbolicMemory object");
}

static word_t 
s_get_simplified (const SymbolicMemory *mem, const ConcreteAddress &a, 
		  int size_in_bytes, Architecture::endianness_t e)
{
  Expr *val = mem->get(a, size_in_bytes, e).get_Expr ()->ref ();
  exprutils::simplify (&val);
  ATF_REQUIRE (val->is_Constant ());
  word_t result = dynamic_cast<const Constant *>(val)->get_val ();
  val->deref ();

  return result;
}

ATF_TEST_CASE_BODY(memcells)
{
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);
  {
    ConcreteMemory *cm = new ConcreteMemory;
    SymbolicMemory * memory = new SymbolicMemory (cm);

    /* Check if memcells are undefined */
    ATF_REQUIRE_EQ(memory->is_defined(ConcreteAddress::null_addr()), false);
    ATF_REQUIRE_EQ(memory->is_defined(ConcreteAddress(6234)), false);

    ConcreteAddress addr = ConcreteAddress(1024);
    SymbolicValue value = SymbolicValue(32, 6235);

    memory->put(addr, value, Architecture::LittleEndian);

    /* Check if the put() did work well */
    ATF_REQUIRE_EQ(s_get_simplified (memory, 
				     addr, 4, Architecture::LittleEndian), 
		   6235);
    ATF_REQUIRE_EQ (s_get_simplified (memory, 
				      addr, 2, Architecture::LittleEndian), 
		    6235);
    ATF_REQUIRE_EQ (s_get_simplified (memory, 
				      addr, 1, Architecture::LittleEndian), 91);
    ATF_REQUIRE_EQ (s_get_simplified (memory, 
				      ++(++addr), 2, 
				      Architecture::LittleEndian),
		    0);

    memory->put(addr, value, Architecture::BigEndian);

    /* Check if the put() did work well */
    ATF_REQUIRE_EQ (s_get_simplified (memory, 
				      addr, 4, Architecture::BigEndian), 6235);
    ATF_REQUIRE_EQ (s_get_simplified (memory, 
				      addr, 2, Architecture::BigEndian), 0);
    ATF_REQUIRE_EQ (s_get_simplified (memory, 
				      ++(++addr), 2, Architecture::BigEndian), 
		    6235);
    ATF_REQUIRE_EQ (s_get_simplified (memory, 
				      ++addr, 1, Architecture::BigEndian), 91);

    delete memory;
    delete cm;
  }
  insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, registers);
  ATF_ADD_TEST_CASE(tcs, memcells);
}

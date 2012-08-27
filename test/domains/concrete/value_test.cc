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

#include <domains/concrete/ConcreteValue.hh>
#include <kernel/Architecture.hh>
#include <kernel/insight.hh>
#include <utils/logs.hh>

ATF_TEST_CASE(concretevalue)
ATF_TEST_CASE_HEAD(concretevalue)
{
  set_md_var("descr",
	     "Check the creation and content of a ConcreteValue object");
}
ATF_TEST_CASE_BODY(concretevalue)
{
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);
  /* Checking default initialization */
  ConcreteValue default_value = ConcreteValue();
  ATF_REQUIRE_EQ(default_value.get(), 0);
  ATF_REQUIRE_EQ(default_value.get_size(), 0);

  /* Checking default size when none passed */
  ConcreteValue only_value(BV_DEFAULT_SIZE, 6342);
  ATF_REQUIRE_EQ(only_value.get(), 6342);
  ATF_REQUIRE_EQ(only_value.get_size(), BV_DEFAULT_SIZE);

  /* Checking definition of value and size */
  ConcreteValue value(32, 6342);
  ATF_REQUIRE_EQ(value.get(), 6342);
  ATF_REQUIRE_EQ(value.get_size(), 32);

  /* Checking to_string method */
  ATF_REQUIRE(value.to_string() == std::string("6342{32}"));

  /* Checking cloning */
  ConcreteValue clone_value(value);
  ATF_REQUIRE_EQ(clone_value.get(), 6342);
  ATF_REQUIRE_EQ(clone_value.get_size(), 32);

  /* Checking for operator== */
  ATF_REQUIRE(value == clone_value);

  /* Checking for unknown_value() primitive */
  ConcreteValue unknown_value = ConcreteValue::unknown_value(BV_DEFAULT_SIZE);
  ATF_REQUIRE_EQ(unknown_value.get(), 0);
  ATF_REQUIRE_EQ(unknown_value.get_size(), BV_DEFAULT_SIZE);

  insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, concretevalue);
}

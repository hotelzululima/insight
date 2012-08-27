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

#include <domains/concrete/ConcreteAddress.hh>
#include <domains/concrete/ConcreteValue.hh>
#include <kernel/Architecture.hh>
#include <kernel/insight.hh>
#include <utils/logs.hh>

ATF_TEST_CASE(concreteaddress)
ATF_TEST_CASE_HEAD(concreteaddress)
{
  set_md_var("descr",
	     "Check the creation and content of a ConcreteAddress object");
}
ATF_TEST_CASE_BODY(concreteaddress)
{
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);
  /* Check default initialization */
  ConcreteAddress default_address = ConcreteAddress();
  ATF_REQUIRE_EQ(default_address.get_address(), 0);

  /* Check normal initialization and operator++ */
  ConcreteAddress address = ConcreteAddress(6234);
  ATF_REQUIRE_EQ(address.get_address(), 6234);
  ATF_REQUIRE_EQ((++address).get_address(), 6235);
  ATF_REQUIRE_EQ((address++).get_address(), 6235);
  ATF_REQUIRE_EQ(address.get_address(), 6236);

  /* Check clone operator */
  ConcreteAddress clone_address = ConcreteAddress(address);
  ATF_REQUIRE_EQ(clone_address.get_address(), address.get_address());

  /* Check initialization through a ConcreteValue */
  ConcreteValue value = ConcreteValue(BV_DEFAULT_SIZE, 6234);
  ConcreteAddress concretevalue_address = ConcreteAddress(value);
  ATF_REQUIRE_EQ(concretevalue_address.get_address(), 6234);

  /* Check null_addr (null address) */
  ConcreteAddress null_address = ConcreteAddress::null_addr();
  ATF_REQUIRE_EQ(null_address.get_address(), 0);
  insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, concreteaddress);
}

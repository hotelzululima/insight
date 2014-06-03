/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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
#include <sstream>
#include <utils/ConfigTable.hh>
#include <kernel/insight.hh>

using namespace std;

ATF_TEST_CASE(basics)
ATF_TEST_CASE_HEAD(basics)
{
  set_md_var("descr", "Check basic operations of ConfigTable.");
}
ATF_TEST_CASE_BODY(basics)
{
  insight::init ();
  ConfigTable ct;

  ct.set ("firstname", "foo");
  ct.set ("lastname", "bar");

  ATF_REQUIRE (ct.has ("firstname"));
  ATF_REQUIRE (ct.has ("lastname"));
  ATF_REQUIRE (! ct.has ("birthday"));

  ATF_REQUIRE (ct.get ("firstname") == "foo");
  ATF_REQUIRE (ct.get ("lastname") == "bar");

  ATF_REQUIRE_EQ (ct.get_integer ("birthday"), 0);
  ATF_REQUIRE_EQ (ct.get_boolean ("birthday"), false);

  ct.set ("birthday", 19700101);

  ATF_REQUIRE (ct.has ("birthday"));
  ATF_REQUIRE_EQ (ct.get_integer ("birthday"), 19700101);
  ATF_REQUIRE_EQ (ct.get_boolean ("birthday"), true);

  insight::terminate ();
}

ATF_TEST_CASE(io)
ATF_TEST_CASE_HEAD(io)
{
  set_md_var("descr", "Check IO operations of ConfigTable.");
}
ATF_TEST_CASE_BODY(io)
{
  insight::init ();
  ConfigTable ct1;
  ConfigTable ct2;

  ct1.set ("firstname", "foo");
  ct1.set ("lastname", "bar");
  ct1.set ("birthday", 19700101);

  ostringstream oss1;
  ct1.save (oss1);

  istringstream iss (oss1.str ());
  ct2.load (iss);

  ostringstream oss2;
  ct2.save (oss2);

  ATF_REQUIRE_EQ (oss1.str (), oss2.str ());
  insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, basics);
  ATF_ADD_TEST_CASE(tcs, io);
}

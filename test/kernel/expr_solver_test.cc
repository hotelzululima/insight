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

#include <kernel/Architecture.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/ExprSolver.hh>
#include <kernel/insight.hh>
#include <io/expressions/expr-parser.hh>

using namespace std;

#define ALL_TESTS					\
  SOLVER_TEST (NP, "(NOT %pf)", ExprSolver::SAT)  \
  SOLVER_TEST (US1, "(EQ (NOT %pf) %pf)", ExprSolver::UNSAT) \
  SOLVER_TEST (S2, "(OR (NOT %pf) %pf){0;1}", ExprSolver::SAT) \
  SOLVER_TEST (US2, "(NOT (OR (NOT %pf) %pf){0;1})", ExprSolver::UNSAT) \
  SOLVER_TEST (S3, "[%eax]{0;8}", ExprSolver::SAT)				\


#define SOLVER_TEST(id, e, res)     \
ATF_TEST_CASE(id); \
\
ATF_TEST_CASE_HEAD(id)	\
{ \
  set_md_var ("descr", \
	      "Check expression solver against satisfiability of " # id); \
} \
\
ATF_TEST_CASE_BODY(id) \
{ \
  s_check_tautology (# id, e, res); \
}

static void
s_check_tautology (const string &, const string &expr, ExprSolver::Result res)
{
  insight::init ();
  const Architecture *x86_32 = 
    Architecture::getArchitecture (Architecture::X86_32);
  MicrocodeArchitecture ma (x86_32);

  Expr *e = expr_parser (expr, &ma);
  ATF_REQUIRE (e != NULL);
  ExprSolver *s = ExprSolver::create_default_solver (&ma);

  ATF_REQUIRE_EQ (s->check_sat (e), res);
  e->deref ();

  insight::terminate ();
}

ALL_TESTS
#undef SOLVER_TEST

#define SOLVER_TEST(id, e, expout) \
  ATF_ADD_TEST_CASE(tcs, id);

ATF_INIT_TEST_CASES(tcs)
{
  ALL_TESTS
}

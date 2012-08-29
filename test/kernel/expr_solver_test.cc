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

#include <config.h>
#include <utils/logs.hh>
#include <kernel/Architecture.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/ExprSolver.hh>
#include <kernel/insight.hh>
#include <io/expressions/expr-parser.hh>

using namespace std;

#if HAVE_Z3_SOLVER 

#define ALL_TESTS					\
  SOLVER_TEST (NP, "(NOT %pf)", ExprSolver::SAT)  \
  SOLVER_TEST (US1, "(EQ (NOT %pf) %pf)", ExprSolver::UNSAT) \
  SOLVER_TEST (S2, "(OR (NOT %pf) %pf){0;1}", ExprSolver::SAT) \
  SOLVER_TEST (US2, "(NOT (OR (NOT %pf) %pf){0;1})", ExprSolver::UNSAT) \
  SOLVER_TEST (S3, "[%eax]{0;8}", ExprSolver::SAT) \
  \
  EVAL_TEST (E1, "(MUL_U 3{0;32} Y{0;32}){0;32}", "(EQ Y{0;32} 5)", "15{0;32}")

#define SOLVER_TEST(id, e, res)     \
ATF_TEST_CASE(id);		    \
\
ATF_TEST_CASE_HEAD(id)			\
{ \
  set_md_var ("descr", \
	      "Check expression solver against satisfiability of " e); \
} \
\
ATF_TEST_CASE_BODY(id)			\
{ \
  s_check_tautology (# id, e, res); \
}

#define EVAL_TEST(id, e, cond, res)  \
ATF_TEST_CASE(id);		    \
\
ATF_TEST_CASE_HEAD(id)			\
{ \
  set_md_var ("descr", \
	      "Check expression solver against evaluation of " e); \
} \
\
ATF_TEST_CASE_BODY(id)			\
{ \
  s_check_evaluation (# id, e, cond, res);	\
}

static void
s_check_tautology (const string &, const string &expr, ExprSolver::Result res)
{
  ConfigTable cfg;

  cfg.set (logs::DEBUG_ENABLED_PROP, true);
  cfg.set (logs::STDIO_ENABLED_PROP, true);
  cfg.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  cfg.set (ExprSolver::DEFAULT_COMMAND_PROP, "z3");
  cfg.set (ExprSolver::DEFAULT_NB_ARGS_PROP, 2);
  cfg.set (ExprSolver::DEFAULT_ARG_PROP (0), "-smt2");
  cfg.set (ExprSolver::DEFAULT_ARG_PROP (1), "-in");

  insight::init (cfg);
  const Architecture *x86_32 = 
    Architecture::getArchitecture (Architecture::X86_32);
  MicrocodeArchitecture ma (x86_32);

  Expr *e = expr_parser (expr, &ma);
  ATF_REQUIRE (e != NULL);

  ExprSolver *s = ExprSolver::create_default_solver (&ma);

  s->push ();
  ATF_REQUIRE_EQ (s->check_sat (e), res); 
  s->pop ();
  e->deref ();

  insight::terminate ();
}

static void
s_check_evaluation (const string &, const string &expr, const string &cond,
		    const string &expected_result)
{
  ConfigTable cfg;

  cfg.set (logs::DEBUG_ENABLED_PROP, true);
  cfg.set (logs::STDIO_ENABLED_PROP, true);
  cfg.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);
  
  cfg.set (ExprSolver::DEFAULT_COMMAND_PROP, "z3");
  cfg.set (ExprSolver::DEFAULT_NB_ARGS_PROP, 2);
  cfg.set (ExprSolver::DEFAULT_ARG_PROP (0), "-smt2");
  cfg.set (ExprSolver::DEFAULT_ARG_PROP (1), "-in");

  insight::init (cfg);
  const Architecture *x86_32 = 
    Architecture::getArchitecture (Architecture::X86_32);
  MicrocodeArchitecture ma (x86_32);

  Expr *e = expr_parser (expr, &ma);
  ATF_REQUIRE (e != NULL);
  Expr *c = expr_parser (cond, &ma);
  ATF_REQUIRE (c != NULL);
  Expr *er = expr_parser (expected_result, &ma);
  ATF_REQUIRE (er != NULL);
  
  ExprSolver *s = ExprSolver::create_default_solver (&ma);
  
  Expr *res = s->evaluate (e, c);
  ATF_REQUIRE_EQ (res, er);
  e->deref ();
  c->deref ();
  er->deref ();
  res->deref ();
  
  insight::terminate ();
}

ALL_TESTS
#undef SOLVER_TEST
#undef EVAL_TEST

#define SOLVER_TEST(id, e, expout) \
  ATF_ADD_TEST_CASE(tcs, id);

#define EVAL_TEST(id, e, cond, res)	\
  ATF_ADD_TEST_CASE(tcs, id);

ATF_INIT_TEST_CASES(tcs)
{
  ALL_TESTS
}
#else
static void
s_check_tautology (const string &, const string &, ExprSolver::Result)
{
}

static void
s_check_evaluation (const string &, const string &, const string &,
		    const string &)
{
}

ATF_TEST_CASE(NO_Z3_SOLVER)

ATF_TEST_CASE_HEAD(NO_Z3_SOLVER)
{ 
  set_md_var ("descr", "Z3 has not been found."); 
} 

ATF_TEST_CASE_BODY(NO_Z3_SOLVER) 
{ 
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, NO_Z3_SOLVER);
}
#endif


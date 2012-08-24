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
#include <kernel/insight.hh>
#include <io/expressions/expr-parser.hh>
#include <utils/Log.hh>

using namespace std;

#define ALL_X86_CC							\
  X86_32_CC (NP,  "(NOT %pf)",						\
	     "(NOT %eflags{2;1}){0;1}")					\
  X86_32_CC (A,   "(NOT (OR %cf %zf){0;1})",				\
	     "(NOT (OR %eflags{0;1} %eflags{6;1}){0;1}){0;1}")		\
  X86_32_CC (AE,  "(NOT %cf)",						\
	     "(NOT %eflags{0;1}){0;1}")					\
  X86_32_CC (B,   "%cf",						\
	     "%eflags{0;1}")						\
  X86_32_CC (BE,  "(OR %cf %zf){0;1}",					\
	     "(OR %eflags{0;1} %eflags{6;1}){0;1}")			\
  X86_32_CC (E,   "%zf",						\
	     "%eflags{6;1}")						\
  X86_32_CC (G,   "(NOT (OR (XOR %sf %of){0;1} %zf){0;1})",		\
	     "(NOT (OR (XOR %eflags{7;1} %eflags{11;1}){0;1} "		\
	     "%eflags{6;1}){0;1}){0;1}")				\
  X86_32_CC (GE,  "(NOT (XOR %sf %of){0;1})",				\
	     "(NOT (XOR %eflags{7;1} %eflags{11;1}){0;1}){0;1}")	\
  X86_32_CC (L,   "(XOR %sf %of){0;1}",					\
	     "(XOR %eflags{7;1} %eflags{11;1}){0;1}")			\
  X86_32_CC (LE,  "(OR (XOR %sf %of){0;1} %zf){0;1}",			\
	     "(OR (XOR %eflags{7;1} %eflags{11;1}){0;1} "		\
	     "%eflags{6;1}){0;1}")					\
  X86_32_CC (NA,  "(OR %cf %zf){0;1}",					\
	     "(OR %eflags{0;1} %eflags{6;1}){0;1}")			\
  X86_32_CC (NAE, "%cf",						\
	     "%eflags{0;1}")						\
  X86_32_CC (NB,  "(NOT %cf)",						\
	     "(NOT %eflags{0;1}){0;1}")					\
  X86_32_CC (NBE, "(NOT (OR %cf %zf){0;1})",				\
	     "(NOT (OR %eflags{0;1} %eflags{6;1}){0;1}){0;1}")		\
  X86_32_CC (NE,  "(NOT %zf)",						\
	     "(NOT %eflags{6;1}){0;1}")					\
  X86_32_CC (NG,  "(OR (XOR %sf %of){0;1} %zf){0;1}",			\
	     "(OR (XOR %eflags{7;1} %eflags{11;1}){0;1} "		\
	     "%eflags{6;1}){0;1}")					\
  X86_32_CC (NGE, "(XOR %sf %of){0;1}",					\
	     "(XOR %eflags{7;1} %eflags{11;1}){0;1}")			\
  X86_32_CC (NL,  "(NOT (XOR %sf %of){0;1})",				\
	     "(NOT (XOR %eflags{7;1} %eflags{11;1}){0;1}){0;1}")	\
  X86_32_CC (NLE, "(NOT (OR (XOR %sf %of){0;1} %zf){0;1})",		\
	     "(NOT (OR (XOR %eflags{7;1} %eflags{11;1}){0;1} "		\
	     "%eflags{6;1}){0;1}){0;1}")				\
  X86_32_CC (NO,  "(NOT %of)",						\
	     "(NOT %eflags{11;1}){0;1}")				\
  X86_32_CC (NS,  "(NOT %sf)",						\
	     "(NOT %eflags{7;1}){0;1}")					\
  X86_32_CC (NZ,  "(NOT %zf)",						\
	     "(NOT %eflags{6;1}){0;1}")					\
  X86_32_CC (O,   "%of",						\
	     "%eflags{11;1}")						\
  X86_32_CC (P,   "%pf",						\
	     "%eflags{2;1}")						\
  X86_32_CC (PE,  "%pf",						\
	     "%eflags{2;1}")						\
  X86_32_CC (PO,  "(NOT %pf)",						\
	     "(NOT %eflags{2;1}){0;1}")					\
  X86_32_CC (S,   "%sf",						\
	     "%eflags{7;1}")						\
  X86_32_CC (Z,   "%zf",						\
	     "%eflags{6;1}")

#define X86_32_CC(id, e, expout) \
ATF_TEST_CASE(expr_parser_for_cc_ ## id); \
\
ATF_TEST_CASE_HEAD(expr_parser_for_cc_ ## id)	\
{ \
  set_md_var ("descr", \
	      "Check expression parser against x86_32 condition code " # id); \
} \
\
ATF_TEST_CASE_BODY(expr_parser_for_cc_ ## id) \
{ \
  s_check_expr_parser (# id, e, expout); \
}

static void
s_check_expr_parser (const string &, const string &expr, \
		     const string &expectedout)
{
  insight::init ();
  const Architecture *x86_32 = 
    Architecture::getArchitecture (Architecture::X86_32);
  MicrocodeArchitecture ma (x86_32);

  Expr *e = expr_parser (expr, &ma);
  ATF_REQUIRE_EQ (e->to_string (), expectedout);
  insight::terminate ();
}

ALL_X86_CC
#undef X86_32_CC

#define X86_32_CC(id, e, expout) \
  ATF_ADD_TEST_CASE(tcs, expr_parser_for_cc_ ## id);

ATF_INIT_TEST_CASES(tcs)
{
  ALL_X86_CC
}

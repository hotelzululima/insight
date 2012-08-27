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
#include <io/expressions/smtlib-writer.hh>
#include <io/expressions/expr-parser.hh>
#include <utils/logs.hh>

using namespace std;

#define ALL_X86_CC							\
  X86_32_CC (NP,  "(NOT %pf)",						\
	     "(= (bvnot ((_ extract 2 2 ) eflags)) #b1)")		\
  X86_32_CC (A,   "(NOT (OR %cf %zf){0;1})",				\
	     "(not (= (bvor ((_ extract 0 0 ) eflags) ((_ extract 6 6 ) eflags)) #b1))") \
  X86_32_CC (AE,  "(NOT %cf)",						\
	     "(not (= ((_ extract 0 0 ) eflags) #b1))")			\
  X86_32_CC (B,   "%cf",						\
	     "(= ((_ extract 0 0 ) eflags) #b1)")			\
  X86_32_CC (BE,  "(OR %cf %zf){0;1}",					\
	     "(= (bvor ((_ extract 0 0 ) eflags) ((_ extract 6 6 ) eflags)) #b1)") \
  X86_32_CC (E,   "%zf",						\
	     "(= ((_ extract 6 6 ) eflags) #b1)")			\
  X86_32_CC (G,   "(NOT (OR (XOR %sf %of){0;1} %zf){0;1})",		\
	     "(not (= (bvor (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) ((_ extract 6 6 ) eflags)) #b1))") \
  X86_32_CC (GE,  "(NOT (XOR %sf %of){0;1})",				\
	     "(not (= (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) #b1))") \
  X86_32_CC (L,   "(XOR %sf %of){0;1}",					\
	     "(= (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) #b1)") \
  X86_32_CC (LE,  "(OR (XOR %sf %of){0;1} %zf){0;1}",			\
	     "(= (bvor (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) ((_ extract 6 6 ) eflags)) #b1)") \
  X86_32_CC (NA,  "(OR %cf %zf){0;1}",					\
	     "(= (bvor ((_ extract 0 0 ) eflags) ((_ extract 6 6 ) eflags)) #b1)") \
  X86_32_CC (NAE, "%cf",						\
	     "(= ((_ extract 0 0 ) eflags) #b1)")			\
  X86_32_CC (NB,  "(NOT %cf)",						\
	     "(not (= ((_ extract 0 0 ) eflags) #b1))")			\
  X86_32_CC (NBE, "(NOT (OR %cf %zf){0;1})",				\
	     "(not (= (bvor ((_ extract 0 0 ) eflags) ((_ extract 6 6 ) eflags)) #b1))") \
  X86_32_CC (NE,  "(NOT %zf)",						\
	     "(= (bvnot ((_ extract 6 6 ) eflags)) #b1)")		\
  X86_32_CC (NG,  "(OR (XOR %sf %of){0;1} %zf){0;1}",			\
	     "(= (bvor (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) ((_ extract 6 6 ) eflags)) #b1)") \
  X86_32_CC (NGE, "(XOR %sf %of){0;1}",					\
	     "(= (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) #b1)") \
  X86_32_CC (NL,  "(NOT (XOR %sf %of){0;1})",				\
	     "(not (= (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) #b1))") \
  X86_32_CC (NLE, "(NOT (OR (XOR %sf %of){0;1} %zf){0;1})",		\
	     "(not (= (bvor (bvxor ((_ extract 7 7 ) eflags) ((_ extract 11 11 ) eflags)) ((_ extract 6 6 ) eflags)) #b1))") \
  X86_32_CC (NO,  "(NOT %of)",						\
	     "(= (bvnot ((_ extract 11 11 ) eflags)) #b1)")		\
  X86_32_CC (NS,  "(NOT %sf)",						\
	     "(= (bvnot ((_ extract 7 7 ) eflags)) #b1)")		\
  X86_32_CC (NZ,  "(NOT %zf)",						\
	     "(= (bvnot ((_ extract 6 6 ) eflags)) #b1)")		\
  X86_32_CC (O,   "%of",						\
	     "(= ((_ extract 11 11 ) eflags) #b1)")			\
  X86_32_CC (P,   "%pf",						\
	     "(= ((_ extract 2 2 ) eflags) #b1)")			\
  X86_32_CC (PE,  "%pf",						\
	     "(= ((_ extract 2 2 ) eflags) #b1)")			\
  X86_32_CC (PO,  "(NOT %pf)",						\
	     "(= (bvnot ((_ extract 2 2 ) eflags)) #b1)")		\
  X86_32_CC (S,   "%sf",						\
	     "(= ((_ extract 7 7 ) eflags) #b1)")			\
  X86_32_CC (Z,   "%zf",						\
	     "(= ((_ extract 6 6 ) eflags) #b1)")

#define X86_32_CC(id, e, expout) \
ATF_TEST_CASE(smtlib_ ## id) \
\
ATF_TEST_CASE_HEAD(smtlib_ ## id)	\
{ \
  set_md_var ("descr", \
	      "Check expression parser against x86_32 condition code " # id); \
} \
\
ATF_TEST_CASE_BODY(smtlib_ ## id) \
{ \
  s_check_expr_to_smtlib (# id, e, expout); \
}

static void
s_check_expr_to_smtlib (const string &, const string &expr, 
			const string &expectedout)
{
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);
  const Architecture *x86_32 = 
    Architecture::getArchitecture (Architecture::X86_32);
  MicrocodeArchitecture ma (x86_32);

  Expr *e = expr_parser (expr, &ma);
  ATF_REQUIRE (e != NULL);
  ostringstream oss;

  smtlib_writer (oss, e, "memory", 32);
  
  ATF_REQUIRE_EQ (oss.str (), expectedout);
  e->deref ();

  insight::terminate ();
}

ALL_X86_CC
#undef X86_32_CC

#if 1
#define X86_32_CC(id, e, expout) \
  ATF_ADD_TEST_CASE(tcs, smtlib_ ## id)


ATF_INIT_TEST_CASES(tcs)
{
  ALL_X86_CC
}
#else

static void 
gen_string (const string &e, const MicrocodeArchitecture &ma)
{					      
  Expr *ex = expr_parser (e, &ma);            
  ostringstream oss;				
  smtlib_writer (oss, ex, "memory", 32);
  string smte = oss.str ();			
  string::size_type i = smte.find ('\n'); 
  while (i != string::npos)			
    {						
      string s = smte.replace (i, 1, "\\n");	
      smte = s;					
      i = smte.find ('\n');			
    } 
  logs::display << *ex << "-->" << smte << endl;
  ex->deref ();					
}

#define X86_32_CC(id, e, expout) gen_string (e, ma);

int 
main()
{
  ConfigTable ct;
  ct.set (logs::DEBUG_ENABLED_PROP, false);
  ct.set (logs::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);
  insight::init (ct);
  const Architecture *x86_32 = 
    Architecture::getArchitecture (Architecture::X86_32);
  MicrocodeArchitecture ma (x86_32);
  ALL_X86_CC 
  insight::terminate ();

  return 0;
}
#endif

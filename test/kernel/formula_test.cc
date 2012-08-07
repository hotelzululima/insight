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
#include <list>

#include <kernel/Architecture.hh>
#include <kernel/Expressions.hh>
#include <kernel/Insight.hh>
#include <kernel/expressions/PatternMatching.hh>
#include <kernel/expressions/ExprUtils.hh>

using namespace std;

#define DEFBV "{0;32}"

static Expr *
s_parse_expr (const string &s)
{
  Expr *F = Expr::parse (NULL, s);

  ATF_REQUIRE (F != NULL);

  return F;
}

static bool
s_check_is_true (Expr *F)
{  
  Expr *tmp = F->ref ();
  ExprUtils::simplify_level0 (&tmp);
  Option<bool> value = tmp->try_eval_level0 ();
  bool result = value.hasValue ();

  if (result)
    result = value.getValue();
  tmp->deref ();

  return result;
}

#define CHK_TAUTOLOGY(f) s_check_tautology (f, __FILE__, __LINE__)
static void
s_check_tautology (Expr *F, const char *file, int line)
{
  if (! s_check_is_true (F))
    {
      ostringstream oss;
      oss << file << ":" << line << ": "
	  << "fail to check tautology " << F->to_string ();
      ATF_FAIL (oss.str ());
    }  
}

#define CHK_EQUIV(f1, f2) s_check_equivalence (f1, f2, __FILE__, __LINE__)
static void
s_check_equivalence (Expr *F1, Expr *F2, const char *file, int line)
{
  Expr *c1 = Expr::createAnd (F1->ref (), F2->ref ());
  Expr *c2 = Expr::createAnd (Expr::createNot (F1->ref ()),
			      Expr::createNot (F2->ref ()));
  Expr *F = Expr::createOr (c1, c2);
  if (!s_check_is_true (F))
    {
      ostringstream oss;
      oss << file << ":" << line << ": "
	  << "fail to check equivalence between " << F1->to_string ()
	  << " and " << F2->to_string ();
      ATF_FAIL (oss.str ());
    }
  F->deref ();
}

ATF_TEST_CASE (check_tautologies);

ATF_TEST_CASE_HEAD (check_tautologies)
{ 
  set_md_var ("descr", "check that some simple exprs are tautologies");
} 

ATF_TEST_CASE_BODY (check_tautologies) 
{ 
  Insight::init ();
  Expr *F = s_parse_expr ("(NOT (AND X (NOT X){0;1}){0;1}){0;1}");

  ATF_REQUIRE (F != NULL);
  CHK_TAUTOLOGY (F);
  F->deref ();

  F = s_parse_expr ("(OR X (NOT X){0;1}){0;1}");
  ATF_REQUIRE (F != NULL);
  CHK_TAUTOLOGY (F);
  F->deref ();

  F = s_parse_expr ("(AND X X){0;1}");
  ATF_REQUIRE (F != NULL);
  Expr *G = s_parse_expr ("X");
  ATF_REQUIRE (G != NULL);
  CHK_EQUIV (F, G);
  F->deref ();

  F = s_parse_expr ("(OR X X){0;1}");
  ATF_REQUIRE (F != NULL);
  CHK_EQUIV (F, G);
  G->deref ();

  CHK_EQUIV (F, F);
  F->deref ();

  Insight::terminate ();
}

			/* --------------- */

static Expr *
s_replace (Expr *F, Expr *P, Expr *V)
{
  Expr *result = ExprUtils::replace_subterm (F, P, V);

  F->deref ();
  P->deref ();
  V->deref ();

  return result;
}

ATF_TEST_CASE (check_replacement);

ATF_TEST_CASE_HEAD (check_replacement)
{ 
  set_md_var ("descr", "check replace procedure");
} 

ATF_TEST_CASE_BODY(check_replacement) 
{ 
  Insight::init ();

  /* 
   * compute (replace (replace (replace (Y || X) Y tmp) X Y) tmp X) 
   * and check equivalence with X || Y 
   */

  Expr *F = s_parse_expr ("(OR Y X){0;1}");
  Expr *X = s_parse_expr ("X");
  Expr *Y = s_parse_expr ("Y");
  Expr *tmp = s_parse_expr ("tmp");

  F = s_replace (F, Y->ref (), tmp->ref ()); /* F <- replace (Y || X) Y tmp */  
  Expr *aux = s_parse_expr ("(OR tmp X){0;1}");
  CHK_EQUIV (F, aux);
  aux->deref ();

  F = s_replace (F, X->ref (), Y->ref ()); /* F <- replace (tmp || X) X Y */
  aux = s_parse_expr ("(OR tmp Y){0;1}");
  CHK_EQUIV (F, aux);
  aux->deref ();

  F = s_replace (F, tmp->ref (), X->ref ()); /* F <- replace (tmp || Y) tmp X */
  aux = s_parse_expr ("(OR X Y){0;1}");
  CHK_EQUIV (F, aux);
  aux->deref ();
  F->deref ();
  X->deref ();
  Y->deref ();
  tmp->deref ();

  /* 
   * compute F <- (EQ (MUL 2 X) (ADD X X))
   * and check equivalence between
   * replace $F (MUL 2 X) Z)
   * and (EQ Z (ADD X X));
   */
  F = s_replace (s_parse_expr ("(EQ (MUL_U 2 X)" DEFBV "(ADD X X)" DEFBV ")"),
		 s_parse_expr ("(MUL_U 2 X)" DEFBV), 
		 s_parse_expr ("Z"));
  aux = s_parse_expr ("(EQ Z  (ADD X X)" DEFBV ")");
  CHK_EQUIV (F, aux);
  F->deref ();
  aux->deref ();

  Insight::terminate ();
}

			/* --------------- */

ATF_TEST_CASE (check_pattern_matching);

ATF_TEST_CASE_HEAD (check_pattern_matching)
{ 
  set_md_var ("descr", "check pattern matching procedure");
} 

ATF_TEST_CASE_BODY(check_pattern_matching) 
{ 
  Insight::init ();

  /* 
   * compute PM <- match (EQ Y (ADD T Z)) $F Y T Z;
   * then check that 
   * PM[Y] <=> (2 * X)
   * PM[T] <=> X
   * PM[Z] <=> X
   */

  Expr *F = s_parse_expr ("(EQ (MUL_U 2 X)" DEFBV "(ADD X X)" DEFBV "){0;1}");
  Expr *pattern = s_parse_expr ("(EQ Y (ADD T Z)" DEFBV "){0;1}");
  list<const Variable *> free_variables;
  Variable *Y = dynamic_cast<Variable *> (s_parse_expr ("Y"));
  ATF_REQUIRE (Y != NULL);
  Variable *T = dynamic_cast<Variable *> (s_parse_expr ("T"));
  ATF_REQUIRE (T != NULL);
  Variable *Z = dynamic_cast<Variable *> (s_parse_expr ("Z"));
  ATF_REQUIRE (Z != NULL);

  free_variables.push_back (Y);
  free_variables.push_back (T);
  free_variables.push_back (Z);

  try
    {
      PatternMatching *PM = 
	PatternMatching::match (F, pattern, free_variables);

      F->deref ();

      ATF_REQUIRE (PM->has (Y));
      
      F = 
	BinaryApp::create (BV_OP_EQ, 
			   dynamic_cast<const Expr *>(PM->get (Y))->ref (), 
			   dynamic_cast<Expr *>(s_parse_expr ("(MUL_U 2 X)" 
							      DEFBV)));
      CHK_TAUTOLOGY (F);
      F->deref ();

      ATF_REQUIRE (PM->has (T));
      F = BinaryApp::create (BV_OP_EQ, 
			     dynamic_cast<const Expr *>(PM->get (T))->ref (), 
			     dynamic_cast<Expr *>(s_parse_expr ("X")));
      CHK_TAUTOLOGY (F);
      F->deref ();

      ATF_REQUIRE (PM->has (Z));
      F = BinaryApp::create (BV_OP_EQ, 
			     dynamic_cast<const Expr *>(PM->get (Z))->ref (), 
			     dynamic_cast<Expr *>(s_parse_expr ("X")));
      CHK_TAUTOLOGY (F);
      delete PM;
      Y->deref ();
      T->deref ();
      Z->deref ();
    }
  catch(PatternMatching::Failure &)
    {
      ATF_FAIL ("pattern matching failure");
    }

  pattern->deref ();
  F->deref ();



  Insight::terminate ();
}

ATF_INIT_TEST_CASES(tcs)
{
  ATF_ADD_TEST_CASE(tcs, check_tautologies);
  ATF_ADD_TEST_CASE(tcs, check_replacement);
  ATF_ADD_TEST_CASE(tcs, check_pattern_matching);
}

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

#include <kernel/microcode/MicrocodeStatements.hh>

using namespace std;

string Assignment::pp()
{
  ostringstream oss;
  oss << lval->to_string () << " := " << rval->to_string();

  return oss.str();
}

string Jump::pp()
{
  ostringstream oss;
  oss << "Jmp " << target->to_string ();

  return oss.str();
}

string Skip::pp()
{
  ostringstream oss;
  oss << "Skip";

  return oss.str();
}

string External::pp()
{
  ostringstream oss;
  oss << "External(" << id << ")";

  return oss.str();
}

/**********************************************************************/

Statement::Statement() {};
Statement::Statement(const Statement &) {};
Statement::~Statement() {} ;

Skip::Skip() : Statement() {};
Skip::Skip(const Skip &sk) : Statement(sk) {};
Skip::~Skip() {};

/**********************************************************************/

Assignment::Assignment(LValue *lv, Expr *v) : Statement(), lval(lv), rval(v) { };
Assignment::Assignment(const Assignment &as) : Statement(as)
{
  lval = (LValue *) as.lval->ref ();
  rval = as.rval->ref ();
};

Assignment::~Assignment()
{
  lval->deref ();
  rval->deref ();
};

LValue * Assignment::get_lval()
{
  return lval;
};

void Assignment::set_lval(LValue *lv)
{
  lval = lv;
};

Expr * Assignment::get_rval()
{
  return rval;
};

void Assignment::set_rval(LValue *rv)
{
  rval = rv;
};

/**********************************************************************/

bool Statement::is_Assignment()
{
  return dynamic_cast<Assignment *>(this);
}

bool Statement::is_Skip()
{
  return dynamic_cast<Skip *>(this);
}

bool Statement::is_Jump()
{
  return dynamic_cast<Jump *>(this);
}

bool Statement::is_External()
{
  return dynamic_cast<External *>(this);
}

/**********************************************************************/

Statement *Assignment::clone() const
{
  return new Assignment(*this);
}

Statement *Jump::clone() const
{
  return new Jump(*this);
}

Statement *Skip::clone() const
{
  return new Skip(*this);
}

Statement *External::clone() const
{
  return new External(*this);
}

/**********************************************************************/

bool Statement::equal(Statement * s1, Statement * s2) {

	if (s1->is_Assignment() && s2->is_Assignment())
		return (((Assignment*) s1)->get_lval() == ((Assignment*) s2)->get_lval()) &&
		       (((Assignment*) s1)->get_rval() && ((Assignment*) s2)->get_rval());

	if (s1->is_Skip() && s2->is_Skip())
		return true;

	if (s1->is_Jump() && s2->is_Jump())
		return ((Jump*) s1)->get_target() == ((Jump*) s2)->get_target();

	if (s1->is_External() && s2->is_External())
		return ((External*) s1)->get_id() == ((External *) s2)->get_id();

	return false;
}

bool Statement::equal(Statement * other) {
	return Statement::equal(this, other);
}

/**********************************************************************/

vector<Expr **> * Assignment::expr_list()
{
  vector<Expr **> * exprs = new vector<Expr **>;
  exprs->push_back((Expr **) &lval);
  exprs->push_back(&rval);

  return exprs;
}

vector<Expr **> * Jump::expr_list()
{
  vector<Expr **> * exprs = new vector<Expr **>;
  exprs->push_back(&target);

  return exprs;
}

vector<Expr **> * Skip::expr_list()
{
  vector<Expr **> * exprs = new vector<Expr **>;

  return exprs;
}

vector<Expr **> * External::expr_list()
{
  vector<Expr **> * exprs = new vector<Expr **>;

  return exprs;
}

/*****************************************************************************/

Jump::Jump(Expr *target) : Statement(), target(target) {};

Jump::Jump(const Jump &jp) : Statement(jp) {
	target = jp.target->ref ();
};

Jump::~Jump() {
  target->deref ();
};

Expr * Jump::get_target() {
	return target;
};

/*****************************************************************************/

External::External(std::string id) : Statement(), id(id) {};
External::External(const External &bb) : Statement(bb), id(bb.id) {};
External::~External() {};
std::string External::get_id() { return id; };

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

#include <kernel/expressions/Operators.hh>

#include <sstream>
#include <stdexcept>

using namespace std;

static void
s_unknown_operator(const char *kind, int op)
{
  ostringstream oss;

  oss << "unknown " << kind << "operator '" << op << "'.";
  throw invalid_argument(oss.str());
}

/* --------------- */

bool binary_op_associative(BinaryOp op)
{
  switch (op)
    {
#define BINARY_OP(_op,_pp,_commut,_assoc) case _op: return _assoc;
#include "Operators.def"
#undef BINARY_OP
    default:
      break;
    }
  s_unknown_operator("binary", op);

  return false;
}

/* --------------- */

bool binary_op_commutative(BinaryOp op)
{
  switch (op)
    {
#define BINARY_OP(_op,_pp,_commut,_assoc) case _op: return _commut;
#include "Operators.def"
#undef BINARY_OP
    default:
      break;
    }
  s_unknown_operator("binary", op);

  return false;
}

/* --------------- */

string binary_op_to_string(BinaryOp op)
{
  switch (op)
    {
#define BINARY_OP(_op,_pp,_commut,_assoc) \
case _op: return ((*_pp) ? (_pp) : (#_op));
#include "Operators.def"
#undef BINARY_OP
    default:
      break;
    }
  s_unknown_operator("binary", op);

  return "";
}

/* --------------- */

string ternary_op_to_string(TernaryOp op)
{
  switch (op)
    {
#define TERNARY_OP(_op,_pp) case _op: return ((*_pp) ? (_pp) : (#_op));
#include "Operators.def"
#undef TERNARY_OP
    default:
      break;
    }
  s_unknown_operator("ternary", op);

  return "";
}

/* --------------- */

string unary_op_to_string(UnaryOp op)
{
  switch (op)
    {
#define UNARY_OP(_op,_pp) case _op: return ((*_pp) ? (_pp) : (#_op));
#include "Operators.def"
#undef UNARY_OP
    default:
      break;
    }
  s_unknown_operator("unary", op);

  return "";
}

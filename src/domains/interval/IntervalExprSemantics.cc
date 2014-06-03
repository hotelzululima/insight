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

#include <domains/interval/IntervalExprSemantics.hh>

#include <algorithm>
using namespace std;

template<> IntervalValue
IntervalExprSemantics::BV_OP_ADD_eval(IntervalValue v1, IntervalValue v2,
				      int, int)
{
  return IntervalValue(v1.get_size(),
                       v1.getMin() + v2.getMin(), v1.getMax() + v2.getMax());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_SUB_eval(IntervalValue v1, IntervalValue v2,
				      int, int)
{
  return IntervalValue(v1.get_size(),
                       v1.getMin() - v2.getMax(), v1.getMax() - v2.getMin());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_MUL_U_eval(IntervalValue v1, IntervalValue v2,
					int, int)
{
  word_t x1 = v1.getMin() * v2.getMin();
  word_t x2 = v1.getMin() * v2.getMax();
  word_t x3 = v1.getMax() * v2.getMin();
  word_t x4 = v1.getMax() * v2.getMax();

  return IntervalValue(v1.get_size(), min(min(x1, x2), min(x3, x4)),
                       max(max(x1, x2), max(x3, x4)));
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_MUL_S_eval(IntervalValue v1, IntervalValue v2,
					int, int)
{
  word_t x1 = v1.getMin() * v2.getMin();
  word_t x2 = v1.getMin() * v2.getMax();
  word_t x3 = v1.getMax() * v2.getMin();
  word_t x4 = v1.getMax() * v2.getMax();

  return IntervalValue(v1.get_size(), min(min(x1, x2), min(x3, x4)),
                       max(max(x1, x2), max(x3, x4)));
}


template<> IntervalValue
IntervalExprSemantics::BV_OP_DIV_U_eval(IntervalValue v1, IntervalValue,
					int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_DIV_S_eval(IntervalValue v1, IntervalValue,
					int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_POW_eval(IntervalValue v1, IntervalValue,
				      int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_AND_eval(IntervalValue v1, IntervalValue,
				      int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_OR_eval(IntervalValue v1, IntervalValue,
				     int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_XOR_eval(IntervalValue v1, IntervalValue,
				      int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_LSH_eval(IntervalValue v1, IntervalValue,
				      int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_RSH_U_eval(IntervalValue v1, IntervalValue,
					int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_RSH_S_eval(IntervalValue v1, IntervalValue,
					int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_ROR_eval(IntervalValue v1, IntervalValue,
				      int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_ROL_eval(IntervalValue v1, IntervalValue,
				      int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_EQ_eval(IntervalValue v1, IntervalValue,
				     int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_NEQ_eval(IntervalValue v1, IntervalValue,
				      int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_LEQ_S_eval(IntervalValue v1, IntervalValue,
					int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_LT_S_eval(IntervalValue v1, IntervalValue,
				       int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_LEQ_U_eval(IntervalValue v1, IntervalValue,
					int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_LT_U_eval(IntervalValue v1, IntervalValue,
				       int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_NEG_eval(IntervalValue v, int, int)
{
  return IntervalValue(v.get_size(), -v.getMax(), -v.getMin());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_NOT_eval(IntervalValue v, int, int)
{
  /* Uses the property of 2's complement representation: -x = (~x + 1) */
  return IntervalValue(v.get_size(), -v.getMax() - 1, -v.getMin() - 1);
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_MODULO_eval(IntervalValue v1, IntervalValue,
					 int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_CONCAT_eval(IntervalValue v1, IntervalValue,
					 int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_EXTEND_U_eval(IntervalValue v1, IntervalValue,
					   int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_EXTEND_S_eval(IntervalValue v1, IntervalValue,
					   int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::BV_OP_EXTRACT_eval(IntervalValue v1, IntervalValue,
					  IntervalValue, int, int)
{
  return IntervalValue(v1.get_size());
}

template<> IntervalValue
IntervalExprSemantics::embed_eval(IntervalValue v1, IntervalValue v2, int off) {
  return expr_semantics_embed_eval<IntervalValue,
				   IntervalExprSemantics>(v1, v2, off);
}

template<> IntervalValue
IntervalExprSemantics::extract_eval(IntervalValue v,  int off, int size) {
  return expr_semantics_extract_eval<IntervalValue,
				     IntervalExprSemantics>(v, off, size);
}

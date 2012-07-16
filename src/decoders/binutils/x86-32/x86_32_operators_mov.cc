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

#include "x86_32_translate.hh"

using namespace std;
using x86_32::parser_data;

X86_32_TRANSLATE_2_OP(MOV)
{
  Expr *src = op1;
  LValue *dst = (LValue *) op2;

  if (src->get_bv_size () > dst->get_bv_size ())
    Expr::extract_with_bit_vector_size_of (src, dst);
  else if (src->get_bv_size () < dst->get_bv_size ())
    Expr::extract_with_bit_vector_size_of ((Expr *&) dst, src);

  data.mc->add_assignment (data.start_ma, dst, src, data.next_ma);
}

X86_32_TRANSLATE_2_OP(MOVB)
{
  Expr::extract_bit_vector (op1, 0, 8);
  Expr::extract_bit_vector (op2, 0, 8);

  x86_32_translate<X86_32_TOKEN(MOV)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(MOVW)
{
  Expr::extract_bit_vector (op1, 0, 16);
  Expr::extract_bit_vector (op2, 0, 16);

  x86_32_translate<X86_32_TOKEN(MOV)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(MOVL)
{
  assert (op1->get_bv_size () == 32);

  x86_32_translate<X86_32_TOKEN(MOV)> (data, op1, op2);
}


static void
s_mov_on_cc (MicrocodeAddress from, x86_32::parser_data &data, 
	     Expr *op1, Expr *op2, Expr *cond, MicrocodeAddress to)
{
  Expr *src = op1;
  LValue *dst = (LValue *) op2;

  if (src->get_bv_size () > dst->get_bv_size ())
    Expr::extract_with_bit_vector_size_of (src, dst);
  else if (src->get_bv_size () < dst->get_bv_size ())
    Expr::extract_with_bit_vector_size_of ((Expr *&) dst, src);

  data.mc->add_skip (from, to, 
		     UnaryApp::create (NOT, cond, 0, cond->get_bv_size ()));
  data.mc->add_skip (from, from + 1, cond->ref());
  from++;
  data.mc->add_assignment (from, dst, src, to);
}

#define X86_32_CC(cc, f) \
X86_32_TRANSLATE_2_OP (CMOV ## cc) \
{ s_mov_on_cc (data.start_ma, data, op1, op2, \
	       data.condition_codes[parser_data::X86_32_CC_ ## cc]->ref (), \
	       data.next_ma); }

#include "x86_32_cc.def"
#undef X86_32_CC

X86_32_TRANSLATE_2_OP (CMOVC)
{ 
  s_mov_on_cc (data.start_ma, data, op1, op2, 
	       data.condition_codes[parser_data::X86_32_CC_B]->ref (), \
	       data.next_ma); 
}

X86_32_TRANSLATE_2_OP (CMOVNC)
{ 
  s_mov_on_cc (data.start_ma, data, op1, op2, 
	       data.condition_codes[parser_data::X86_32_CC_NB]->ref (), \
	       data.next_ma); 
}

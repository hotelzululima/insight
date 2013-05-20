/*-
 * Copyright (C) 2010-2013, Centre National de la Recherche Scientifique,
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

#include "x86_64_translation_functions.hh"

using namespace std;

static void 
s_binary_op (x86_64::parser_data &data, BinaryOp op, Expr *op1, Expr *op2)
{
  MicrocodeAddress from (data.start_ma);
  Expr *dst = op2;
  Expr *src = op1;

  x86_64_set_operands_size ((Expr *&) dst, src);

  Expr *result = BinaryApp::create (op, dst->ref (), src->ref (), 0,
				    dst->get_bv_size ());

  data.mc->add_assignment (from, (LValue *) dst->ref (), result);
  x86_64_compute_SF (from, data, dst);
  x86_64_compute_ZF (from, data, dst);
  x86_64_compute_PF (from, data, dst);
  x86_64_reset_CF (from, data);
  x86_64_reset_OF (from, data, NULL, &data.next_ma);

  dst->deref ();
  src->deref ();
}


X86_64_TRANSLATE_2_OP(AND)
{
  s_binary_op (data, BV_OP_AND, op1, op2);
}

X86_64_TRANSLATE_2_OP(ANDB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(AND)>);
}

X86_64_TRANSLATE_2_OP(ANDW)
{
  x86_64_translate_with_size (data, op1, op2, 16, 
			      x86_64_translate<X86_64_TOKEN(AND)>);
}

X86_64_TRANSLATE_2_OP(ANDL)
{
  x86_64_translate_with_size (data, op1, op2, 32, 
			      x86_64_translate<X86_64_TOKEN(AND)>);
}

X86_64_TRANSLATE_2_OP(OR)
{
  s_binary_op (data, BV_OP_OR, op1, op2);
}

X86_64_TRANSLATE_2_OP(ORB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(OR)>);
}

X86_64_TRANSLATE_2_OP(ORW)
{
  x86_64_translate_with_size (data, op1, op2, 16, 
			      x86_64_translate<X86_64_TOKEN(OR)>);
}

X86_64_TRANSLATE_2_OP(ORL)
{
  x86_64_translate_with_size (data, op1, op2, 32, 
			      x86_64_translate<X86_64_TOKEN(OR)>);
}

X86_64_TRANSLATE_1_OP(NOT)
{
  LValue *dst = (LValue *) op1;
  Expr *src = op1->ref ();
  MicrocodeAddress start = data.start_ma;

  data.mc->add_assignment (start, dst, UnaryApp::create (BV_OP_NOT, src, 0,
							 src->get_bv_size ()), 
			   data.next_ma);
}

X86_64_TRANSLATE_1_OP(NOTB)
{
  x86_64_translate_with_size (data, op1, 8, 
			      x86_64_translate<X86_64_TOKEN(NOT)>);
}

X86_64_TRANSLATE_1_OP(NOTW)
{
  x86_64_translate_with_size (data, op1, 16, 
			      x86_64_translate<X86_64_TOKEN(NOT)>);
}

X86_64_TRANSLATE_1_OP(NOTL)
{
  x86_64_translate_with_size (data, op1, 32, 
			      x86_64_translate<X86_64_TOKEN(NOT)>);
}

X86_64_TRANSLATE_2_OP(TEST)
{
  MicrocodeAddress start = data.start_ma;
  x86_64_set_operands_size (op1, op2);
  LValue *r0 = data.get_tmp_register (TMPREG(0), op1->get_bv_size ());


    
  data.mc->add_assignment (start, r0, 
			   BinaryApp::create (BV_OP_AND, op1, op2, 0,
					      op1->get_bv_size ()));

  x86_64_compute_SF (start, data, r0);
  x86_64_compute_ZF (start, data, r0);
  x86_64_compute_PF (start, data, r0);
  x86_64_reset_CF (start, data);
  x86_64_reset_OF (start, data, NULL, &data.next_ma);
}

X86_64_TRANSLATE_2_OP(TESTB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(TEST)>);
}

X86_64_TRANSLATE_2_OP(TESTW)
{
  x86_64_translate_with_size (data, op1, op2, 16, 
			      x86_64_translate<X86_64_TOKEN(TEST)>);
}

X86_64_TRANSLATE_2_OP(TESTL)
{
  x86_64_translate_with_size (data, op1, op2, 32, 
			      x86_64_translate<X86_64_TOKEN(TEST)>);
}

X86_64_TRANSLATE_2_OP(XOR)
{
  s_binary_op (data, BV_OP_XOR, op1, op2);
}

X86_64_TRANSLATE_2_OP(XORB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(XOR)>);
}

X86_64_TRANSLATE_2_OP(XORW)
{
  x86_64_translate_with_size (data, op1, op2, 16, 
			      x86_64_translate<X86_64_TOKEN(XOR)>);
}

X86_64_TRANSLATE_2_OP(XORL)
{
  x86_64_translate_with_size (data, op1, op2, 32, 
			      x86_64_translate<X86_64_TOKEN(XOR)>);
}


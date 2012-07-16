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

#include "x86_32_translation_functions.hh"

using namespace std;

static x86_32_compute_flag_proc *flags[] = {
  x86_32_reset_CF,
  x86_32_reset_OF,
  x86_32_compute_SF,
  x86_32_compute_ZF,
  x86_32_compute_PF,
  NULL
};

X86_32_TRANSLATE_2_OP(AND)
{
  MicrocodeAddress start = data.start_ma;
  x86_32_binary_op (start, data, AND_OP, (LValue *) op2, op1, flags, 
		    &data.next_ma);
}

X86_32_TRANSLATE_2_OP(ANDB)
{
  x86_32_translate_with_size (data, op1, op2, 8, 
			      x86_32_translate<X86_32_TOKEN(AND)>);
}

X86_32_TRANSLATE_2_OP(ANDW)
{
  x86_32_translate_with_size (data, op1, op2, 16, 
			      x86_32_translate<X86_32_TOKEN(AND)>);
}

X86_32_TRANSLATE_2_OP(ANDL)
{
  x86_32_translate_with_size (data, op1, op2, 32, 
			      x86_32_translate<X86_32_TOKEN(AND)>);
}

X86_32_TRANSLATE_2_OP(XOR)
{
  MicrocodeAddress start = data.start_ma;
  x86_32_binary_op (start, data, XOR, (LValue *) op2, op1, flags, 
		    &data.next_ma);
}

X86_32_TRANSLATE_2_OP(XORB)
{
  x86_32_translate_with_size (data, op1, op2, 8, 
			      x86_32_translate<X86_32_TOKEN(XOR)>);
}

X86_32_TRANSLATE_2_OP(XORW)
{
  x86_32_translate_with_size (data, op1, op2, 16, 
			      x86_32_translate<X86_32_TOKEN(XOR)>);
}

X86_32_TRANSLATE_2_OP(XORL)
{
  x86_32_translate_with_size (data, op1, op2, 32, 
			      x86_32_translate<X86_32_TOKEN(XOR)>);
}

X86_32_TRANSLATE_2_OP(OR)
{
  MicrocodeAddress start = data.start_ma;
  x86_32_binary_op (start, data, OR, (LValue *) op2, op1, flags, 
		    &data.next_ma);
}

X86_32_TRANSLATE_2_OP(ORB)
{
  x86_32_translate_with_size (data, op1, op2, 8, 
			      x86_32_translate<X86_32_TOKEN(OR)>);
}

X86_32_TRANSLATE_2_OP(ORW)
{
  x86_32_translate_with_size (data, op1, op2, 16, 
			      x86_32_translate<X86_32_TOKEN(OR)>);
}

X86_32_TRANSLATE_2_OP(ORL)
{
  x86_32_translate_with_size (data, op1, op2, 32, 
			      x86_32_translate<X86_32_TOKEN(OR)>);
}

X86_32_TRANSLATE_1_OP(NOT)
{
  LValue *dst = (LValue *) op1;
  Expr *src = op1->ref ();
  MicrocodeAddress start = data.start_ma;

  data.mc->add_assignment (start, dst, UnaryApp::create (NOT, src, 0,
							 src->get_bv_size ()), 
			   data.next_ma);
}

X86_32_TRANSLATE_1_OP(NOTB)
{
  x86_32_translate_with_size (data, op1, 8, 
			      x86_32_translate<X86_32_TOKEN(NOT)>);
}

X86_32_TRANSLATE_1_OP(NOTW)
{
  x86_32_translate_with_size (data, op1, 16, 
			      x86_32_translate<X86_32_TOKEN(NOT)>);
}

X86_32_TRANSLATE_1_OP(NOTL)
{
  x86_32_translate_with_size (data, op1, 32, 
			      x86_32_translate<X86_32_TOKEN(NOT)>);
}

X86_32_TRANSLATE_2_OP(TEST)
{
  MicrocodeAddress start = data.start_ma;
  LValue *r0 = data.get_tmp_register (TMPREG(0), op1->get_bv_size ());

  data.mc->add_assignment (start, r0, 
			   BinaryApp::create (AND_OP, op1, op2, 0,
					      op1->get_bv_size ()));

  x86_32_compute_SF (start, data, r0);
  x86_32_compute_ZF (start, data, r0);
  x86_32_compute_PF (start, data, r0);
  x86_32_reset_CF (start, data);
  x86_32_reset_OF (start, data, NULL, &data.next_ma);
}

X86_32_TRANSLATE_2_OP(TESTB)
{
  x86_32_translate_with_size (data, op1, op2, 8, 
			      x86_32_translate<X86_32_TOKEN(TEST)>);
}

X86_32_TRANSLATE_2_OP(TESTW)
{
  x86_32_translate_with_size (data, op1, op2, 16, 
			      x86_32_translate<X86_32_TOKEN(TEST)>);
}

X86_32_TRANSLATE_2_OP(TESTL)
{
  x86_32_translate_with_size (data, op1, op2, 32, 
			      x86_32_translate<X86_32_TOKEN(TEST)>);
}

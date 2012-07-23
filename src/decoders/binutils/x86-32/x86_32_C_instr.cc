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

void
x86_32_cmpgen (MicrocodeAddress &from, x86_32::parser_data &data, 
	       Expr *op1, Expr *op2, MicrocodeAddress *to)
{
  Expr *src = op1;
  Expr *dst = op2;

  x86_32_set_operands_size ((Expr *&) dst, src);

  LValue *tmpr0 = data.get_tmp_register (TMPREG(0), dst->get_bv_size () + 1);

  data.mc->add_assignment (from, (LValue *) tmpr0->ref (), 
			   BinaryApp::create (SUB, dst->ref (), src, 0, 
					      tmpr0->get_bv_size ()));
  x86_32_assign_CF (from, data, 
		    tmpr0->extract_bit_vector (dst->get_bv_size (), 1), 
		    NULL);

  Expr *tmp[3];
  
  tmp[0] = dst->extract_bit_vector (dst->get_bv_size () - 1, 1);
  tmp[1] = src->extract_bit_vector (src->get_bv_size () - 1, 1);
  tmp[2] = tmpr0->extract_bit_vector (dst->get_bv_size () - 1, 1);

  tmp[1] = BinaryApp::create (XOR, tmp[0], tmp[1], 0, 1); 
  tmp[0] = BinaryApp::create (XOR, tmp[0]->ref (), tmp[2], 0, 1); 
  
  tmp[2] = BinaryApp::create (AND_OP, tmp[0], tmp[1], 0, 1);

  x86_32_assign_OF (from, data, tmp[2]);

  dst->deref ();

  dst = (LValue *) tmpr0->extract_bit_vector (0, dst->get_bv_size ());

  tmpr0->deref ();  

  x86_32_compute_SF (from, data, dst);
  x86_32_compute_ZF (from, data, dst);
  x86_32_compute_AF (from, data, dst);
  x86_32_compute_PF (from, data, dst, to);
  dst->deref ();
}

			/* --------------- */

X86_32_TRANSLATE_2_OP(CMP)
{
  MicrocodeAddress from = data.start_ma;
  x86_32_cmpgen (from, data, op1, op2, &data.next_ma);
}

X86_32_TRANSLATE_2_OP(CMPB)
{
  if (op1->get_bv_size () != 8)
    Expr::extract_bit_vector (op1, 0, 8);
  if (op2->get_bv_size () != 8)
    Expr::extract_bit_vector (op2, 0, 8);
  x86_32_translate<X86_32_TOKEN(CMP)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(CMPW)
{
  if (op1->get_bv_size () != 16)
    Expr::extract_bit_vector (op1, 0, 16);
  if (op2->get_bv_size () != 16)
    Expr::extract_bit_vector (op2, 0, 16);
  x86_32_translate<X86_32_TOKEN(CMP)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(CMPL)
{
  x86_32_translate<X86_32_TOKEN(CMP)> (data, op1, op2);
}

			/* --------------- */


X86_32_TRANSLATE_2_OP(CMPXCHG)
{
  Expr *dst = op2;
  Expr *src = op1;
  Expr *eax = data.get_register ("eax");

  Expr::extract_bit_vector (eax, 0, op2->get_bv_size ());

  MicrocodeAddress from (data.start_ma + 1);
  MicrocodeAddress ifaddr (from);
  x86_32_assign_ZF (from, data, Constant::one (1));
  data.mc->add_assignment (from, (LValue *) dst->ref (), src->ref (),
			   data.next_ma);
  from++;
  MicrocodeAddress elseaddr (from);
  x86_32_reset_ZF (from, data);
  data.mc->add_assignment (from, (LValue *) eax->ref (), dst->ref (), 
			   data.next_ma);
  
  Expr *cond = BinaryApp::create (EQ, eax->ref (), dst->ref (), 0, 1);
  data.mc->add_skip (data.start_ma, elseaddr,
		     UnaryApp::create (NOT, cond->ref (), 0, 1));
  data.mc->add_skip (data.start_ma, ifaddr, cond->ref ());

  cond->deref ();
  dst->deref ();
  src->deref ();
  eax->deref ();
}

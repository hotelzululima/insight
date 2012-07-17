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

static int
s_actual_size (const Expr *e)
{
  int bv_size = e->get_bv_size ();
  if (e->get_bv_offset () + bv_size > BV_DEFAULT_SIZE)
    return BV_DEFAULT_SIZE - e->get_bv_offset () + 1;
  return bv_size;
}

			/* --------------- */

static Expr *
s_msb (Expr *e)
{  
  int msbindex = e->get_bv_offset () + s_actual_size (e) - 1;
  Expr *result = BinaryApp::create (LSH, e, msbindex);
  Expr::extract_bit_vector (result, 0, 1);

  return result;
}


static void
s_translate_shift (MicrocodeAddress &from, x86_32::parser_data &data, 
		   LValue *dst, Expr *shift, 
		   MicrocodeAddress *to, bool go_left, bool keep_sign)
{
  Expr *val;
  Expr *carry_index;
  int shiftnbbits = s_actual_size (shift);
  LValue *tmpreg0 = data.get_tmp_register (TMPREG (0), shift->get_bv_size ());
  LValue *tmpreg1 = data.get_tmp_register (TMPREG (1), dst->get_bv_size ());

  /* tmpreg0 <- 5 first bits of shift count */
  data.mc->add_assignment (from, tmpreg0, 
			   BinaryApp::create (AND_OP, shift, 
					      Constant::create (0x1F, 0, 
								shiftnbbits)));
  Expr::extract_with_bit_vector_size_of ((Expr *&) tmpreg1, dst);

  /* tmpreg1 <- dst */
  data.mc->add_assignment (from, tmpreg1, dst->ref ());

  /* 
   * If shift count is 0 then nothing has to be done; thus, we go directly 
   * to the end. 
   */
  data.mc->add_skip (from, *to, BinaryApp::create (EQ, tmpreg0->ref (), 0));
  data.mc->add_skip (from, from + 1, 
		     BinaryApp::create (NEQ, tmpreg0->ref (), 0));
  from++;

  if (go_left)
    {
      /* Index of the last bit shifted out: offset+sz-shift */
      carry_index = Constant::create (dst->get_bv_offset() +
				      s_actual_size (dst));
      carry_index = BinaryApp::create (SUB, carry_index, tmpreg0->ref ());
				      
      val = BinaryApp::create (LSH, dst->ref (), tmpreg0->ref ());
    }
  else
    {
      /* Index of the last bit shifted out: offset+shift-1 */
	carry_index = tmpreg0->ref ();

      if (dst->get_bv_offset ())
	carry_index = 
	  BinaryApp::create (ADD, 
			     Constant::create (dst->get_bv_offset()), 
			     carry_index);
	
      carry_index = BinaryApp::create (SUB, carry_index, 1);

      val = BinaryApp::create (RSH, dst->ref (), tmpreg0->ref ());
    }

  /* 
   * Since we cannot restrict Expression by other expressions,
   * we get the carry using a shift on the right: 
   * CF <- (dst >> cindex){0;1} 
   */
  Expr *carry = BinaryApp::create (RSH, dst->ref (), carry_index, 0, 1);

  data.mc->add_assignment (from, dst, val);
  x86_32_assign_CF (from, data, carry);

  if (! go_left && ! keep_sign)
    {
      /* especially for SHR we have to reset lefts bits */
      Expr *mask = UnaryApp::create (NOT, Constant::zero()); /* 0xFF...FF */
      mask = BinaryApp::create (LSH, mask, tmpreg0->ref ());
      mask = UnaryApp::create (NOT, mask);
      Expr::extract_with_bit_vector_of (mask, dst);
      data.mc->add_assignment (from, (LValue *) dst->ref (), 
			       BinaryApp::create (AND_OP, dst->ref (), mask, 
						  0, 1));
    }
  data.mc->add_skip (from, *to, 
		     BinaryApp::create (NEQ, tmpreg0->ref (), 1, 0, 1));
  data.mc->add_skip (from, from + 1, 
		     BinaryApp::create (EQ, tmpreg0->ref (), 1, 0, 1));
  from++;

  /* compute OF */
  Expr *OF;

  if (go_left)
    {
      /* OF <- MSB (dst) ^ CF */
      OF = BinaryApp::create (XOR, dst->ref (), data.get_flag ("cf"), 0, 1);
    }
  else if (keep_sign)
    {
      /* OF <- 0 */ 
      OF = Constant::zero(1);
    }
  else
    {
      /* OF <- MSB (prevdst) */
      OF = s_msb (tmpreg1->ref ());
    }
  x86_32_assign_OF (from, data, OF);
  x86_32_compute_SF (from, data, dst);
  x86_32_compute_ZF (from, data, dst);
  x86_32_compute_PF (from, data, dst, to);
}

			/* --------------- */

X86_32_TRANSLATE_2_OP(SAL)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  MicrocodeAddress start = data.start_ma;

  s_translate_shift (start, data, dst, bitcount, &data.next_ma, true, true);
}

X86_32_TRANSLATE_2_OP(SHL)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  MicrocodeAddress start = data.start_ma;

  s_translate_shift (start, data, dst, bitcount, &data.next_ma, true, false);
}

X86_32_TRANSLATE_2_OP(SAR)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  MicrocodeAddress start = data.start_ma;

  s_translate_shift (start, data, dst, bitcount, &data.next_ma, false, true);
}

X86_32_TRANSLATE_2_OP(SHR)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  MicrocodeAddress start = data.start_ma;

  s_translate_shift (start, data, dst, bitcount, &data.next_ma, false, false);
}

			/* --------------- */

#define translate_shift_one_bit(op) \
X86_32_TRANSLATE_1_OP(op) \
{ x86_32_translate<X86_32_TOKEN(op)> (data, Constant::create (1), op1); }


translate_shift_one_bit (SAL);
translate_shift_one_bit (SALB)
translate_shift_one_bit (SALL);
translate_shift_one_bit (SALW);
translate_shift_one_bit (SAR);
translate_shift_one_bit (SARB);
translate_shift_one_bit (SARL);
translate_shift_one_bit (SARW);
translate_shift_one_bit (SHL);
translate_shift_one_bit (SHLB);
translate_shift_one_bit (SHLL);
translate_shift_one_bit (SHLW);
translate_shift_one_bit (SHR);
translate_shift_one_bit (SHRB);
translate_shift_one_bit (SHRL);
translate_shift_one_bit (SHRW);

#define translate_shift_two_args(op,szc,sz)				\
X86_32_TRANSLATE_2_OP(op ## szc)					\
{									\
  Expr *aux = TernaryApp::create (EXTRACT, op1,				\
				  Constant::zero (op2->get_bv_size ()), \
 				  Constant::create (op2->get_bv_size (), \
				 		    0, BV_DEFAULT_SIZE)); \
  x86_32_translate<X86_32_TOKEN(op)> (data, aux, op2); \
}

translate_shift_two_args(SAL,B,8);
translate_shift_two_args(SAL,L,32);
translate_shift_two_args(SAL,W,16);

translate_shift_two_args(SAR,B,8);
translate_shift_two_args(SAR,L,32);
translate_shift_two_args(SAR,W,16);

translate_shift_two_args(SHL,B,8);
translate_shift_two_args(SHL,L,32);
translate_shift_two_args(SHL,W,16);

translate_shift_two_args(SHR,B,8);
translate_shift_two_args(SHR,L,32);
translate_shift_two_args(SHR,W,16);

			/* --------------- */


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

#include "x86_translation_functions.hh"

using namespace std;

static void
s_translate_shift (x86::parser_data &data, LValue *dst, Expr *shift, 
		   bool go_left, bool keep_sign)
{
  MicrocodeAddress from (data.start_ma);
  LValue *tempCount = data.get_tmp_register (TMPREG(0), 8);
  LValue *tempDest = data.get_tmp_register (TMPREG(1), dst->get_bv_size ());
  int dsz = dst->get_bv_size ();
  Expr *mshift = 
    BinaryApp::create (BV_OP_AND, shift->ref (),
		       Constant::create (0x1F, 0, shift->get_bv_size ()), 
		       0, 8);
  
  data.mc->add_assignment (from, (LValue *) tempCount->ref (), mshift->ref ());
  data.mc->add_assignment (from, (LValue *) tempDest->ref (), dst->ref ());
  
  MicrocodeAddress start_while (from);
  from++;
  int cfindex = go_left ? dsz - 1 : 0;

  data.mc->add_assignment (from, data.get_flag ("cf"),
			   dst->extract_bit_vector (cfindex, 1));
  BinaryOp op;

  if (go_left) op = BV_OP_LSH;
  else if (keep_sign) op = BV_OP_RSH_S;
  else op = BV_OP_RSH_U;

  data.mc->add_assignment (from, (LValue *) dst->ref (),
			   BinaryApp::create (op, dst->ref (), 
					      Constant::one (dsz),
					      0 , dsz));
  data.mc->add_assignment (from, (LValue *) tempCount->ref (),
			   BinaryApp::create (BV_OP_SUB, tempCount->ref (),
					      Constant::one (8), 0, 8),
			   start_while);
  from++;
  x86_if_then_else (start_while, data, 
		       BinaryApp::create (BV_OP_NEQ, tempCount->ref (),
					  Constant::zero (8), 0, 1),
		       start_while + 1, from);

  x86_if_then_else (from, data, 
		       BinaryApp::createEquality (mshift->ref (),
						  Constant::one (8)),
		       from + 1, from + 2);
  from++;
  Expr *ofval;
  if (go_left)
    ofval = BinaryApp::create (BV_OP_XOR, data.get_flag ("cf"),
			       dst->extract_bit_vector (cfindex, 1), 0, 1);
  else if (keep_sign)
    ofval = Constant::zero (1);
  else
    ofval = tempDest->extract_bit_vector (cfindex, 1);

  x86_if_then_else (from, data, 
		       BinaryApp::createEquality (mshift->ref (),
						  Constant::zero (8)),
		       data.next_ma, from + 1);
  from++;
  x86_assign_OF (from, data, ofval);
  x86_compute_SF (from, data, dst);
  x86_compute_ZF (from, data, dst);
  x86_compute_PF (from, data, dst, &data.next_ma);

  tempCount->deref ();
  tempDest->deref ();
  mshift->deref ();
  shift->deref ();
  dst->deref ();
}

			/* --------------- */

X86_TRANSLATE_2_OP(SAL)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;

  s_translate_shift (data, dst, bitcount, true, true);
}

X86_TRANSLATE_2_OP(SHL)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;

  s_translate_shift (data, dst, bitcount, true, false);
}

X86_TRANSLATE_2_OP(SAR)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  MicrocodeAddress start = data.start_ma;

  s_translate_shift (data, dst, bitcount, false, true);
}

X86_TRANSLATE_2_OP(SHR)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  MicrocodeAddress start = data.start_ma;

  s_translate_shift (data, dst, bitcount, false, false);
}

			/* --------------- */

#define translate_shift_one_bit(op) \
X86_TRANSLATE_1_OP(op) \
{ x86_translate<X86_TOKEN(op)> (data, Constant::one (data.arch->get_word_size ()), op1); }


translate_shift_one_bit (SAL)
translate_shift_one_bit (SALB)
translate_shift_one_bit (SALL)
translate_shift_one_bit (SALW)
translate_shift_one_bit (SAR)
translate_shift_one_bit (SARB)
translate_shift_one_bit (SARL)
translate_shift_one_bit (SARW)
translate_shift_one_bit (SHL)
translate_shift_one_bit (SHLB)
translate_shift_one_bit (SHLL)
translate_shift_one_bit (SHLW)
translate_shift_one_bit (SHR)
translate_shift_one_bit (SHRB)
translate_shift_one_bit (SHRL)
translate_shift_one_bit (SHRW)

#define translate_shift_two_args(op,szc,sz)				\
X86_TRANSLATE_2_OP(op ## szc)					\
{									\
  Expr *aux = TernaryApp::create (BV_OP_EXTRACT, op1,			\
				  Constant::zero (op2->get_bv_size ()), \
 				  Constant::create (op2->get_bv_size (), 0, \
				 		    data.arch->get_word_size ())); \
  x86_translate<X86_TOKEN(op)> (data, aux, op2); \
}

translate_shift_two_args(SAL,B,8)
translate_shift_two_args(SAL,L,32)
translate_shift_two_args(SAL,W,16)

translate_shift_two_args(SAR,B,8)
translate_shift_two_args(SAR,L,32)
translate_shift_two_args(SAR,W,16)

translate_shift_two_args(SHL,B,8)
translate_shift_two_args(SHL,L,32)
translate_shift_two_args(SHL,W,16)

translate_shift_two_args(SHR,B,8)
translate_shift_two_args(SHR,L,32)
translate_shift_two_args(SHR,W,16)

			/* --------------- */

#define translate_rotate_one_bit_wosz(op)				\
  X86_TRANSLATE_1_OP(op)						\
  {									\
    x86_translate<X86_TOKEN(op)> (data,				\
					Constant::one (data.arch->get_word_size ()), \
					op1);				\
  }

#define translate_rotate_one_bit_wsz(op,sz)				\
  X86_TRANSLATE_1_OP(op)						\
  {									\
    Expr::extract_bit_vector (op1, 0, sz);				\
    x86_translate<X86_TOKEN(op)> (data,				\
					Constant::one (data.arch->get_word_size ()), \
					op1);				\
  }

translate_rotate_one_bit_wosz (RCL)
translate_rotate_one_bit_wosz (RCR) 
translate_rotate_one_bit_wosz (ROL) 
translate_rotate_one_bit_wosz (ROR) 

translate_rotate_one_bit_wsz (RCLB, 8)
translate_rotate_one_bit_wsz (RCLW, 16)
translate_rotate_one_bit_wsz (RCLL, 32)

translate_rotate_one_bit_wsz (RCRB, 8)
translate_rotate_one_bit_wsz (RCRW, 16)
translate_rotate_one_bit_wsz (RCRL, 32)

translate_rotate_one_bit_wsz (ROLB, 8)
translate_rotate_one_bit_wsz (ROLW, 16)
translate_rotate_one_bit_wsz (ROLL, 32)

translate_rotate_one_bit_wsz (RORB, 8)
translate_rotate_one_bit_wsz (RORW, 16)
translate_rotate_one_bit_wsz (RORL, 32)


#define translate_rotate_two_args(op,szc,sz)			\
  X86_TRANSLATE_2_OP(op ## szc)				\
  {								\
    Expr::extract_bit_vector (op2, 0, sz);			\
    x86_translate<X86_TOKEN(op)> (data, op1, op2);	\
  }

translate_rotate_two_args (RCL, B, 8)
translate_rotate_two_args (RCL, W, 16)
translate_rotate_two_args (RCL, L, 32)

translate_rotate_two_args (RCR, B, 8)
translate_rotate_two_args (RCR, W, 16)
translate_rotate_two_args (RCR, L, 32)

translate_rotate_two_args (ROL, B, 8)
translate_rotate_two_args (ROL, W, 16)
translate_rotate_two_args (ROL, L, 32)

translate_rotate_two_args (ROR, B, 8)
translate_rotate_two_args (ROR, W, 16)
translate_rotate_two_args (ROR, L, 32)

static void
s_translate_rotate (x86::parser_data &data, LValue *dst, Expr *bitcount, 
		    bool go_left, bool rotate_carry);

X86_TRANSLATE_2_OP(RCL)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  s_translate_rotate (data, dst, bitcount, true, true);
}

X86_TRANSLATE_2_OP(RCR)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  s_translate_rotate (data, dst, bitcount, false, true);
}

X86_TRANSLATE_2_OP(ROL)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  s_translate_rotate (data, dst, bitcount, true, false);
}

X86_TRANSLATE_2_OP(ROR)
{
  LValue *dst = (LValue *) op2;
  Expr *bitcount = op1;
  s_translate_rotate (data, dst, bitcount, false, false);
}

static void
s_translate_rotate (x86::parser_data &data, LValue *dst, Expr *count, 
		    bool go_left, bool rotate_carry)
{
  MicrocodeAddress from (data.start_ma);
  int dsz = dst->get_bv_size ();
  int csz = count->get_bv_size ();
  Expr *counteq1 = 
    BinaryApp::createEquality (count->ref (), Constant::one (csz));

  /*
   * computation of OF flag for RCR case
   */
  if (! go_left && rotate_carry) 
    {
      x86_if_then_else (from, data, counteq1->ref (), from + 1, from + 2);
      from++;
      Expr *of = BinaryApp::create (BV_OP_XOR, data.get_flag ("cf"),
				    dst->extract_bit_vector (dsz - 1, 1), 
				    0, 1);
      x86_assign_OF (from, data, of);
    }

  /* tmpc : adjusted number of bits to be rotated */
  LValue *tmpc = data.get_tmp_register (TMPREG (0), 8);

  data.mc->add_assignment (from, tmpc, 
			   BinaryApp::create (BV_OP_AND, 
					      count->extract_bit_vector (0, 8), 
					      Constant::create (0x1F, 0, 8),
					      0, 8));

  Expr *cond =
    BinaryApp::create (BV_OP_GT_U, tmpc->ref (), Constant::zero (8), 0, 1);

  /*
   * ROL and ROR do nothing if count is 0; so make a jump to next instruction.
   */
  if (! rotate_carry)
    {
      x86_if_then_else (from, data, cond->ref (), from + 1, data.next_ma);
      from++;
    }

  data.mc->add_assignment (from, (LValue *) tmpc->ref (), 
			   BinaryApp::create (BV_OP_MODULO, tmpc->ref (),
					      Constant::create (dsz + (rotate_carry ? 1 : 0), 
								0, 8), 0, 8));
  /*
   * Rotation loop.
   */
  MicrocodeAddress start_while (from);

  from++;
  LValue *tempCF = data.get_tmp_register (TMPREG (1), 1);
  data.mc->add_assignment (from, tempCF,
			   dst->extract_bit_vector (go_left ? dsz - 1 : 0, 1));
  Expr *newdst;

  if (go_left)
    {
      newdst = BinaryApp::create (BV_OP_MUL_U, dst->ref (), 
				  Constant::create (2, 0, dsz), 0, dsz);
      Expr *cf = rotate_carry ? data.get_flag ("cf") : tempCF->ref ();
      Expr *aux = Expr::createExtend (BV_OP_EXTEND_U, cf, dsz);

      newdst = BinaryApp::create (BV_OP_ADD, newdst, aux, 0, dsz);
    }
  else
    {
      newdst = BinaryApp::create (BV_OP_DIV_U, dst->ref (), 
				  Constant::create (2, 0, dsz), 0, dsz);
      Expr *cf = rotate_carry ? data.get_flag ("cf") : tempCF->ref ();
      Expr *aux = Expr::createExtend (BV_OP_EXTEND_U, cf, dsz);
      aux = BinaryApp::create (BV_OP_MUL_U, aux,
			       Constant::create (1 << (dsz - 1), 0, dsz));

      newdst = BinaryApp::create (BV_OP_ADD, newdst, aux, 0, dsz);
    }
  data.mc->add_assignment (from, (LValue *) dst->ref (), newdst);
  if (rotate_carry)
    data.mc->add_assignment (from, data.get_flag ("cf"), tempCF->ref ());
  data.mc->add_assignment (from, (LValue *) tmpc->ref (), 
			   BinaryApp::create (BV_OP_SUB, tmpc->ref (), 
					      Constant::one (8), 0, 8), 
			   start_while);
  from++;
  
  x86_if_then_else (start_while, data, cond, start_while + 1, 
		       (rotate_carry && !go_left) ? data.next_ma : from);

  /*
   * computation of CF for ROL and ROR cases
   */
  if (! rotate_carry)
    {
      int cfindex = go_left ? 0 : dsz - 1;
      x86_assign_CF (from, data, dst->extract_bit_vector (cfindex, 1));
    }

  /*
   * computation of OF for cases RCL, ROL and ROR cases
   */ 
  if (! (!go_left && rotate_carry)) // ! RCR case
    {
      x86_if_then_else (from, data, counteq1->ref (), from + 1, 
			   data.next_ma);
      from++;

      Expr *of;
      if (go_left && rotate_carry) // RCL and ROL cases
	of = BinaryApp::create (BV_OP_XOR, data.get_flag ("cf"), 
				dst->extract_bit_vector (dsz - 1,1), 0, 1);
      else
	of = BinaryApp::create (BV_OP_XOR, dst->extract_bit_vector (dsz - 1, 1), 
				dst->extract_bit_vector (dsz - 2, 1), 0, 1);
	  
      x86_assign_OF (from, data, of, &data.next_ma);
    }

  counteq1->deref ();
  count->deref ();
  dst->deref ();
}

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

X86_32_TRANSLATE_2_OP(BOUND)
{
  Expr *index = op1;
  Expr::extract_with_bit_vector_of (op2, op1);

  MemCell *min = dynamic_cast<MemCell *>(op2->ref ());

  assert (min != NULL);

  Expr *max_addr = 
    BinaryApp::create (ADD, min->get_addr ()->ref (),
		       op1->get_bv_size () / 8,
		       0, min->get_addr ()->get_bv_size ());

  Expr *max = MemCell::create (max_addr, 0, index->get_bv_size ());

  data.mc->add_skip (data.start_ma, data.next_ma,
		     BinaryApp::create (AND_OP,
					BinaryApp::create (LEQ_S,
							   min,
							   index->ref (), 
							   0, 1),
					BinaryApp::create (LEQ_S,
							   index->ref (), 
							   max,
							   0, 1),
					0, 1));
  op1->deref ();
  op2->deref ();
}

static void
s_bs (x86_32::parser_data &data, Expr *op1, Expr *op2, bool forward)
{
  x86_32_set_operands_size (op2, op1);
  Expr *src = op1;
  Expr *dst = op2;
  int dst_size = dst->get_bv_size ();
  LValue *temp = data.get_tmp_register (TMPREG(0), dst_size);
    
  assert (dst_size == src->get_bv_size ());

  MicrocodeAddress if_part (data.start_ma + 1);
  
  MicrocodeAddress from (if_part);
  x86_32_set_flag (from, data, "zf", &data.next_ma);
  from = if_part + 1;

  MicrocodeAddress else_part (from);  

  x86_32_reset_flag (from, data, "zf");
  int init_index = forward ? 0 : dst_size - 1;
  
  data.mc->add_assignment (from, (LValue *) temp->ref (), 
			   Constant::create (init_index, 0, dst_size));
			       
  MicrocodeAddress start_while (from); 
  from++;
  Expr *stopcond = TernaryApp::create (EXTRACT, src->ref (), temp->ref (), 
				       Constant::one (1), 0, 1);
  stopcond = BinaryApp::create (EQ, stopcond, Constant::zero (1), 0, 1);

  data.mc->add_skip (start_while, start_while + 1, stopcond->ref ());
  BinaryOp op = forward ? ADD : SUB;
  data.mc->add_assignment (from, (LValue *) temp->ref (), 
			   BinaryApp::create (op,
					      temp->ref (),
					      Constant::one (dst_size), 0,
					      dst_size));
  data.mc->add_skip (from, start_while);
  from++;
  data.mc->add_skip (start_while, from, UnaryApp::create (LNOT, stopcond));
  data.mc->add_assignment (from, (LValue *) dst->ref (), temp->ref (), 
			   data.next_ma);

  /*
   * create branches
   */
  Expr *cond = BinaryApp::create(EQ, src->ref (), 
				 Constant::zero (src->get_bv_size ()), 0, 1);
  data.mc->add_skip (data.start_ma, else_part, 
		     UnaryApp::create (NOT, cond, 0, 1));
  data.mc->add_skip (data.start_ma, if_part, cond->ref ());

  temp->deref ();
  dst->deref ();
  src->deref ();
}

X86_32_TRANSLATE_2_OP(BSF)
{  
  s_bs (data, op1, op2, true);
}

X86_32_TRANSLATE_2_OP(BSR)
{
  s_bs (data, op1, op2, false);
}

X86_32_TRANSLATE_1_OP(BSWAP)
{
  assert (op1->get_bv_offset () == 0);
  assert (op1->get_bv_size () == 32);
  assert (op1->is_LValue ());

  MicrocodeAddress from (data.start_ma);
  LValue *temp = data.get_tmp_register (TMPREG(0), op1->get_bv_size ());

  data.mc->add_assignment (from, 
			   (LValue *) temp->ref (), 
			   op1->ref ());
  data.mc->add_assignment (from, 
			   (LValue *) op1->extract_bit_vector (0, 8),
			   temp->extract_bit_vector (24, 8));
  data.mc->add_assignment (from, 
			   (LValue *) op1->extract_bit_vector (8, 8),
			   temp->extract_bit_vector (16, 8));
  data.mc->add_assignment (from, 
			   (LValue *) op1->extract_bit_vector (16, 8),
			   temp->extract_bit_vector (8, 8));
  data.mc->add_assignment (from, 
			   (LValue *) op1->extract_bit_vector (24, 8),
			   temp->extract_bit_vector (0, 8),
			   data.next_ma);
  temp->deref ();
  op1->deref ();
}

#define BT_NO_CHG 0
#define BT_SET    1
#define BT_RESET  2
#define BT_COMP   3

static void
s_bt (x86_32::parser_data &data, Expr *op1, Expr *op2, int chg)
{
  MicrocodeAddress from (data.start_ma);
  Expr *bitbase = op2;
  int bbsize = bitbase->get_bv_size ();
  Expr *bitoffset = op1;
  MicrocodeAddress *to = (chg == BT_NO_CHG) ? &data.next_ma : NULL;
  int mask  = bbsize == 32 ? 6 : 4;

  bitoffset = op1->extract_bit_vector (0, mask);
  op1->deref ();

  x86_32_assign_CF (from, data, 
		    BinaryApp::create (RSH, bitbase, bitoffset, 0, 1), to);
  if (chg == BT_NO_CHG)
    return;

  MicrocodeAddress ifloc;
  if (chg == BT_COMP)
    {
      ifloc = from;
      from++;
    }

  if (chg == BT_SET || chg == BT_COMP)
    {
      /* set the selected bit to 1 */
      Expr *newval = 
	BinaryApp::create (OR, bitbase->ref (), 
			   BinaryApp::create (LSH, Constant::one (bbsize), 
					      bitoffset->ref (), 0, bbsize));
      
      data.mc->add_assignment (from, (LValue *) bitbase->ref (), newval, 
			       data.next_ma);
    }

  if (chg == BT_COMP)
    from++;

  if (chg == BT_RESET || chg == BT_COMP)
    {
      /* set the selected bit to 0 */
      Expr *newval = 
	UnaryApp::create (NOT, 
			  BinaryApp::create (LSH, 
					     Constant::one (bbsize), 
					     bitoffset->ref (), 0, bbsize),
			  0, bbsize);
      newval = BinaryApp::create (AND_OP, bitbase->ref (), newval);
      
      data.mc->add_assignment (from, (LValue *) bitbase->ref (), newval, 
			       data.next_ma);
    }

  if (chg == BT_COMP)
    {
      LValue *cf = data.get_flag ("cf");
      data.mc->add_skip (ifloc, ifloc + 2, cf);      
      data.mc->add_skip (ifloc, ifloc + 1, 
			 UnaryApp::create (NOT, cf->ref (), 0, 1));
    }

}

X86_32_TRANSLATE_2_OP(BT)
{
  s_bt (data, op1, op2, BT_NO_CHG);
}

X86_32_TRANSLATE_2_OP(BTW)
{
  x86_32_translate<X86_32_TOKEN (BT)> (data, op1, op2);
}
X86_32_TRANSLATE_2_OP(BTL)
{
  x86_32_translate<X86_32_TOKEN (BT)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(BTC)
{
  s_bt (data, op1, op2, BT_COMP);
}

X86_32_TRANSLATE_2_OP(BTCW)
{
  x86_32_translate<X86_32_TOKEN (BTC)> (data, op1, op2);
}
X86_32_TRANSLATE_2_OP(BTCL)
{
  x86_32_translate<X86_32_TOKEN (BTC)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(BTR)
{
  s_bt (data, op1, op2, BT_RESET);
}

X86_32_TRANSLATE_2_OP(BTRW)
{
  x86_32_translate<X86_32_TOKEN (BTR)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(BTRL)
{
  x86_32_translate<X86_32_TOKEN (BTR)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(BTS)
{
  s_bt (data, op1, op2, BT_SET);
}

X86_32_TRANSLATE_2_OP(BTSW)
{
  x86_32_translate<X86_32_TOKEN (BTS)> (data, op1, op2);
}
X86_32_TRANSLATE_2_OP(BTSL) 
{
  x86_32_translate<X86_32_TOKEN (BTS)> (data, op1, op2);
}

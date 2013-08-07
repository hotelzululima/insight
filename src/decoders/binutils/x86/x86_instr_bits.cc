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
s_bs (x86::parser_data &data, Expr *op1, Expr *op2, bool forward)
{
  x86_set_operands_size (op2, op1);
  Expr *src = op1;
  Expr *dst = op2;
  int dst_size = dst->get_bv_size ();
  LValue *temp = data.get_tmp_register (TMPREG(0), dst_size);
    
  assert (dst_size == src->get_bv_size ());

  MicrocodeAddress if_part (data.start_ma + 1);
  
  MicrocodeAddress from (if_part);
  x86_set_flag (from, data, "zf", &data.next_ma);
  from = if_part + 1;

  MicrocodeAddress else_part (from);  

  x86_reset_flag (from, data, "zf");
  int init_index = forward ? 0 : dst_size - 1;
  
  data.mc->add_assignment (from, (LValue *) temp->ref (), 
			   Constant::create (init_index, 0, dst_size));
			       
  MicrocodeAddress start_while (from); 
  from++;
  Expr *stopcond = TernaryApp::create (BV_OP_EXTRACT, src->ref (), 
				       temp->ref (), 
				       Constant::one (1), 0, 1);
  stopcond = BinaryApp::createEquality (stopcond, Constant::zero (1));

  data.mc->add_skip (start_while, start_while + 1, stopcond->ref ());
  BinaryOp op = forward ? BV_OP_ADD : BV_OP_SUB;
  data.mc->add_assignment (from, (LValue *) temp->ref (), 
			   BinaryApp::create (op,
					      temp->ref (),
					      Constant::one (dst_size), 0,
					      dst_size));
  data.mc->add_skip (from, start_while);
  from++;
  data.mc->add_skip (start_while, from, Expr::createLNot (stopcond));
  data.mc->add_assignment (from, (LValue *) dst->ref (), temp->ref (), 
			   data.next_ma);

  /*
   * create branches
   */
  Expr *cond = BinaryApp::createEquality(src->ref (), 
					 Constant::zero (src->get_bv_size ()));
  
  data.mc->add_skip (data.start_ma, else_part, Expr::createLNot (cond));
  data.mc->add_skip (data.start_ma, if_part, cond->ref ());

  temp->deref ();
  dst->deref ();
  src->deref ();
}

X86_TRANSLATE_2_OP(BSF)
{  
  s_bs (data, op1, op2, true);
}

X86_TRANSLATE_2_OP(BSR)
{
  s_bs (data, op1, op2, false);
}

#define BT_NO_CHG 0
#define BT_SET    1
#define BT_RESET  2
#define BT_COMP   3

static void
s_bt (x86::parser_data &data, Expr *op1, Expr *op2, int chg)
{
  MicrocodeAddress from (data.start_ma);
  Expr *bitbase = op2;
  int bbsize = bitbase->get_bv_size ();
  Expr *bitoffset = op1;
  MicrocodeAddress *to = (chg == BT_NO_CHG) ? &data.next_ma : NULL;
  int mask  = bbsize == 32 ? 6 : 4;

  bitoffset = 
    Expr::createExtend (BV_OP_EXTEND_U, op1->extract_bit_vector (0, mask),
			op2->get_bv_size ());
				 
  op1->deref ();

  x86_assign_CF (from, data, 
		    BinaryApp::create (BV_OP_RSH_U, bitbase, bitoffset, 0, 1), 
		    to);
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
	BinaryApp::create (BV_OP_OR, bitbase->ref (), 
			   BinaryApp::create (BV_OP_LSH, 
					      Constant::one (bbsize), 
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
	UnaryApp::create (BV_OP_NOT, 
			  BinaryApp::create (BV_OP_LSH, 
					     Constant::one (bbsize), 
					     bitoffset->ref (), 0, bbsize),
			  0, bbsize);
      newval = BinaryApp::create (BV_OP_AND, bitbase->ref (), newval);
      
      data.mc->add_assignment (from, (LValue *) bitbase->ref (), newval, 
			       data.next_ma);
    }

  if (chg == BT_COMP)
    {
      LValue *cf = data.get_flag ("cf");
      data.mc->add_skip (ifloc, ifloc + 2, cf);      
      data.mc->add_skip (ifloc, ifloc + 1, 
			 UnaryApp::create (BV_OP_NOT, cf->ref (), 0, 1));
    }

}

X86_TRANSLATE_2_OP(BT)
{
  s_bt (data, op1, op2, BT_NO_CHG);
}

X86_TRANSLATE_2_OP(BTW)
{
  x86_translate<X86_TOKEN (BT)> (data, op1, op2);
}
X86_TRANSLATE_2_OP(BTL)
{
  x86_translate<X86_TOKEN (BT)> (data, op1, op2);
}

X86_TRANSLATE_2_OP(BTC)
{
  s_bt (data, op1, op2, BT_COMP);
}

X86_TRANSLATE_2_OP(BTCW)
{
  x86_translate<X86_TOKEN (BTC)> (data, op1, op2);
}
X86_TRANSLATE_2_OP(BTCL)
{
  x86_translate<X86_TOKEN (BTC)> (data, op1, op2);
}

X86_TRANSLATE_2_OP(BTR)
{
  s_bt (data, op1, op2, BT_RESET);
}

X86_TRANSLATE_2_OP(BTRW)
{
  x86_translate<X86_TOKEN (BTR)> (data, op1, op2);
}

X86_TRANSLATE_2_OP(BTRL)
{
  x86_translate<X86_TOKEN (BTR)> (data, op1, op2);
}

X86_TRANSLATE_2_OP(BTS)
{
  s_bt (data, op1, op2, BT_SET);
}

X86_TRANSLATE_2_OP(BTSW)
{
  x86_translate<X86_TOKEN (BTS)> (data, op1, op2);
}
X86_TRANSLATE_2_OP(BTSL) 
{
  x86_translate<X86_TOKEN (BTS)> (data, op1, op2);
}

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

#include <utils/bv-manip.hh>
#include <io/expressions/expr-parser.hh>
#include "x86_64_translation_functions.hh"

using namespace std;

static void
s_additive_op (MicrocodeAddress &from, x86_64::parser_data &data, 
	       BinaryOp op, Expr *dst, Expr *src, MicrocodeAddress *to)
{
  x86_64_set_operands_size ((Expr *&) dst, src);

  LValue *tmpr0 = data.get_tmp_register (TMPREG(0), dst->get_bv_size () + 1);

  data.mc->add_assignment (from, (LValue *) tmpr0->ref (),
			   BinaryApp::create (op, dst->ref (), src, 0, 
					      tmpr0->get_bv_size ()));

  x86_64_assign_CF (from, data, 
		    tmpr0->extract_bit_vector (dst->get_bv_size (), 1), 
		    NULL);
  Expr *tmp[3];
  
  tmp[0] = dst->extract_bit_vector (dst->get_bv_size () - 1, 1);
  tmp[1] = src->extract_bit_vector (src->get_bv_size () - 1, 1);
  tmp[2] = tmpr0->extract_bit_vector (dst->get_bv_size () - 1, 1);

  tmp[1] = BinaryApp::create (BV_OP_XOR, tmp[0], tmp[1], 0, 1); 
  if (op == BV_OP_ADD)
    tmp[1] = UnaryApp::create (BV_OP_NOT, tmp[1], 0, 1);
  
  tmp[0] = BinaryApp::create (BV_OP_XOR, tmp[0]->ref (), tmp[2], 0, 1); 
  
  tmp[2] = BinaryApp::create (BV_OP_AND, tmp[0], tmp[1], 0, 1);
  x86_64_assign_OF (from, data, tmp[2]);
  data.mc->add_assignment (from, (LValue *) dst->ref (), 
			   tmpr0->extract_bit_vector (0, dst->get_bv_size ()));

  x86_64_compute_SF (from, data, dst);
  x86_64_compute_ZF (from, data, dst);
  x86_64_compute_AF (from, data, dst);
  x86_64_compute_PF (from, data, dst, to);
  dst->deref ();
  tmpr0->deref ();
}

X86_64_TRANSLATE_2_OP(SUB)
{
  MicrocodeAddress start (data.start_ma);

  s_additive_op (start, data, BV_OP_SUB, op2, op1, &data.next_ma);
}

X86_64_TRANSLATE_2_OP(SUBB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(SUB)>);
}

X86_64_TRANSLATE_2_OP(SUBW)
{
  x86_64_translate_with_size (data, op1, op2, 16, 
			      x86_64_translate<X86_64_TOKEN(SUB)>);
}

X86_64_TRANSLATE_2_OP(SUBL)
{
  x86_64_translate_with_size (data, op1, op2, 32, 
			      x86_64_translate<X86_64_TOKEN(SUB)>);
}

X86_64_TRANSLATE_2_OP(ADD)
{
  MicrocodeAddress start (data.start_ma);
  s_additive_op (start, data, BV_OP_ADD, op2, op1, &data.next_ma);
}

X86_64_TRANSLATE_2_OP(ADDB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(SUB)>);
}

X86_64_TRANSLATE_2_OP(ADDW)
{
  x86_64_translate_with_size (data, op1, op2, 16, 
			      x86_64_translate<X86_64_TOKEN(SUB)>);
}

X86_64_TRANSLATE_2_OP(ADDL)
{
  x86_64_translate_with_size (data, op1, op2, 32, 
			      x86_64_translate<X86_64_TOKEN(SUB)>);
}

static void
s_adc_sbb (x86_64::parser_data &data, Expr *dst, Expr *src, BinaryOp op)
{
  if (src->is_Constant () && src->get_bv_size () < dst->get_bv_size ())
    {
      Constant *c = dynamic_cast <Constant *> (src);
      int val = c->get_val ();
      val = BitVectorManip::extend_signed (val, src->get_bv_size ());
      src->deref ();
      src = Constant::create (val, 0, dst->get_bv_size ());
    }
  assert (src->get_bv_size () >= dst->get_bv_size ());
  Expr::extract_bit_vector (src, 0, dst->get_bv_size ());

  MicrocodeAddress start (data.start_ma);
 
  Expr *cf =
    Expr::createExtend (BV_OP_EXTEND_U, data.get_register ("cf"),
			src->get_bv_size ());
  src = BinaryApp::create (BV_OP_ADD, src, cf, 0, src->get_bv_size ());

  s_additive_op (start, data, op, dst, src, &data.next_ma);
}

X86_64_TRANSLATE_2_OP(ADC)
{  
  if (op2->is_MemCell () && ! op1->is_Constant ())
    Expr::extract_bit_vector (op2, 0, op1->get_bv_size ());
  s_adc_sbb (data, op2, op1, BV_OP_ADD);
}

X86_64_TRANSLATE_2_OP(ADCB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(ADC)>);
}

X86_64_TRANSLATE_2_OP(ADCW)
{
  x86_64_translate_with_size (data, op1, op2, 16, 
			      x86_64_translate<X86_64_TOKEN(ADC)>);
}

X86_64_TRANSLATE_2_OP(ADCL)
{
  x86_64_translate_with_size (data, op1, op2, 32, 
			      x86_64_translate<X86_64_TOKEN(ADC)>);
}

X86_64_TRANSLATE_1_OP(INC)
{
  MicrocodeAddress start (data.start_ma);
  s_additive_op (start, data, BV_OP_ADD, op1, 
		 Constant::one (op1->get_bv_size ()), 
		 &data.next_ma);
}

X86_64_TRANSLATE_1_OP(INCB)
{
  x86_64_translate<X86_64_TOKEN(ADD)>(data, Constant::one(8), op1);
}

X86_64_TRANSLATE_1_OP(INCW)
{
  x86_64_translate<X86_64_TOKEN(ADD)>(data, Constant::one(16), op1);
}

X86_64_TRANSLATE_1_OP(INCL)
{
  x86_64_translate<X86_64_TOKEN(ADD)>(data, Constant::one(32), op1);
}

X86_64_TRANSLATE_1_OP(DEC)
{
  MicrocodeAddress start (data.start_ma);
  s_additive_op (start, data, BV_OP_SUB, op1, 
		 Constant::one (op1->get_bv_size ()), 
		 &data.next_ma);
}

X86_64_TRANSLATE_1_OP(DECB)
{
  x86_64_translate<X86_64_TOKEN(SUB)>(data, Constant::one(8), op1);
}

X86_64_TRANSLATE_1_OP(DECW)
{
  x86_64_translate<X86_64_TOKEN(SUB)>(data, Constant::one(16), op1);
}

X86_64_TRANSLATE_1_OP(DECL)
{
  x86_64_translate<X86_64_TOKEN(SUB)>(data, Constant::one(32), op1);
}

			/* --------------- */

static void
s_aa (x86_64::parser_data &data, BinaryOp op)
{
  MicrocodeAddress if_part (data.start_ma + 1);

  Expr *cond = 
    expr_parser ("(OR "
		 " (NOT (LEQ_U (AND %al 0x0F{0;8}){0;8} 0x9{0;8})) "
		 " (EQ %af 1{0;1})){0;1}", data.arch);

  assert (cond != NULL);

  MicrocodeAddress from (if_part);
  data.mc->add_assignment (from, data.get_register ("al"),
			   BinaryApp::create (op, 
					      data.get_register ("al"),
					      6, 0, 8));
  data.mc->add_assignment (from, data.get_register ("ah"),
			   BinaryApp::create (op, 
					      data.get_register ("ah"), 
					      1, 0, 8));
  x86_64_set_flag (from, data, "af");
  x86_64_set_flag (from, data, "cf");
  data.mc->add_assignment (from, data.get_register ("al"),
			   BinaryApp::create (BV_OP_AND, 
					      data.get_register ("al"),
					      0x0F, 0, 8),
			   data.next_ma);
  from++;
  MicrocodeAddress else_part (from);


  x86_64_reset_flag (from, data, "af");
  x86_64_reset_flag (from, data, "cf");
  data.mc->add_assignment (from, data.get_register ("al"),
			   BinaryApp::create (BV_OP_AND, 
					      data.get_register ("al"),
					      0x0F, 0, 8),
			   data.next_ma);  
  data.mc->add_skip (data.start_ma, else_part, 
		     UnaryApp::create (BV_OP_NOT, cond, 0, 1));
  data.mc->add_skip (data.start_ma, if_part, cond->ref ());
}

X86_64_TRANSLATE_0_OP(AAA)
{
  s_aa (data, BV_OP_ADD);
}

X86_64_TRANSLATE_0_OP(AAD)
{
  x86_64_translate<X86_64_TOKEN (AAD)> (data, Constant::create (10, 0, 8));
}

X86_64_TRANSLATE_1_OP(AAD)
{
  MicrocodeAddress from (data.start_ma);
  LValue *al = data.get_register ("al");
  LValue *ah = data.get_register ("ah");
  Expr::extract_bit_vector (op1, 0, 8);
  Expr *alvalue = BinaryApp::create (BV_OP_MUL_U, ah->ref (), op1, 0, 8);

  alvalue = BinaryApp::create (BV_OP_ADD, al->ref (), alvalue, 0, 8);

  data.mc->add_assignment (from, al, alvalue);
  data.mc->add_assignment (from, ah, Constant::zero (8));

  x86_64_compute_SF (from, data, al);
  x86_64_compute_ZF (from, data, al);
  x86_64_compute_PF (from, data, al, &data.next_ma);
}

X86_64_TRANSLATE_0_OP(AAM)
{
  x86_64_translate<X86_64_TOKEN (AAM)> (data, Constant::create (10, 0, 8));
}

X86_64_TRANSLATE_1_OP(AAM)
{
  MicrocodeAddress from (data.start_ma);
  LValue *al = data.get_register ("al");
  LValue *ah = data.get_register ("ah");

  Expr::extract_bit_vector (op1, 0, 8);

  data.mc->add_skip (from, from + 1,
		     BinaryApp::create (BV_OP_NEQ, op1->ref (),
					Constant::zero (8),
					0, 1));
  from++;
  data.mc->add_assignment (from, ah, 
			   BinaryApp::create (BV_OP_DIV_U, al->ref (), op1, 
					      0, 8));

  data.mc->add_assignment (from, al, 
			   BinaryApp::create (BV_OP_MODULO, al->ref (), 
					      op1->ref (), 0, 8));

  x86_64_compute_SF (from, data, al);
  x86_64_compute_ZF (from, data, al);
  x86_64_compute_PF (from, data, al, &data.next_ma);
}

X86_64_TRANSLATE_0_OP(AAS)
{
  s_aa (data, BV_OP_SUB);
}

			/* --------------- */

static void
s_daadas (x86_64::parser_data &data, bool add)
{
  LValue *old_AL = data.get_tmp_register (TMPREG(0), 8);
  LValue *old_CF = data.get_tmp_register (TMPREG(1), 1);
  MicrocodeAddress from = data.start_ma;

  data.mc->add_assignment (from, (LValue *) old_AL->ref (), 
			   data.get_register ("al"));
  data.mc->add_assignment (from, (LValue *) old_CF->ref (), 
			   data.get_flag ("cf"));
  x86_64_reset_CF (from, data);

  Expr *cond1 = expr_parser ("(OR "
			     "(GT_U (AND %al 0xF{0;8}){0;8} 0x9{0;8}){0;1} "
			     "(EQ %af 1{0;1}){0;1}"
			     "){0;1}", data.arch);
  assert (cond1 != NULL);
  Expr *cond2 = BinaryApp::create (BV_OP_OR,
				   BinaryApp::create (BV_OP_GT_U,
						      old_AL->ref(),
						      Constant::create (0x99, 
									0, 8),
						      0, 1),
				   BinaryApp::createEquality (old_CF->ref (),
							      Constant::one (1)));

  LValue *tmpr2 = data.get_tmp_register (TMPREG(2), 9);
  BinaryOp op = add ? BV_OP_ADD : BV_OP_SUB;

  data.mc->add_skip (from, from + 1, cond1->ref ());
  data.mc->add_skip (from, from + 5, 
		     UnaryApp::create (BV_OP_NOT, cond1->ref (), 0, 1));

  data.mc->add_assignment (from + 1, 
			   (LValue *) tmpr2->ref (),
			   BinaryApp::create (op,  data.get_register ("al"),
					      Constant::create (6, 0, 8), 
					      0, 9),
			   from + 2);
  data.mc->add_assignment (from + 2, 
			   data.get_register ("al"),
			   tmpr2->extract_bit_vector (0, 8),
			   from + 3);
  data.mc->add_assignment (from + 3, 
			   data.get_flag ("cf"),
			   BinaryApp::create (BV_OP_OR,
					      old_CF->ref (),
					      tmpr2->extract_bit_vector (8, 1),
					      0, 1),
			   from + 4);
  data.mc->add_assignment (from + 4, 
			   data.get_flag ("af"),
			   Constant::one (1), 
			   from + 6);
  data.mc->add_assignment (from + 5, 
			   data.get_flag ("af"),
			   Constant::zero (1), 
			   from + 6);
  
  from = from + 6;

  data.mc->add_skip (from, from + 1, cond2->ref ());

  data.mc->add_skip (from, from + (add ? 4 : 3),
		       UnaryApp::create (BV_OP_NOT, cond2->ref (), 0, 1));
    
  data.mc->add_assignment (from + 1 , 
			   data.get_register ("al"),
			   BinaryApp::create (op, 
					      data.get_register ("al"),
					      Constant::create (0x60, 0, 8), 
					      0, 8),
			   from + 2);
  data.mc->add_assignment (from + 2, 
			   data.get_flag ("cf"),
			   Constant::one (1),
			   from + (add ? 4 : 3));
  from = from + 3;
  if (add)
    data.mc->add_assignment (from, 
			     data.get_flag ("cf"),
			     Constant::zero (1));
  LValue *al = data.get_register ("al");
  x86_64_compute_SF (from, data, al);
  x86_64_compute_ZF (from, data, al);  
  x86_64_compute_PF (from, data, al, &data.next_ma);

  al->deref ();
  old_AL->deref ();
  old_CF->deref ();
  tmpr2->deref ();
  cond1->deref ();
  cond2->deref ();
}

			/* --------------- */

X86_64_TRANSLATE_0_OP(DAA)
{  
  s_daadas (data, true);
}

X86_64_TRANSLATE_0_OP(DAS)
{
  s_daadas (data, false);
}

			/* --------------- */

static void
s_div (x86_64::parser_data &data, Expr *op1, bool udiv)
{
  Expr *src = op1;
  int srcsize = src->get_bv_size ();
  MicrocodeAddress from (data.start_ma);
  LValue *temp = data.get_tmp_register (TMPREG(0), 2 * srcsize);
  LValue *temp2 = data.get_tmp_register (TMPREG(1), srcsize);
  word_t min, max;  
  Expr *op;
  const char *Qname;
  const char *Rname;
  
  if (srcsize == 8)
    {
      op = data.get_register ("ax");
      if (udiv) 
	{
	  min = 0x00;
	  max = 0xFF;
	}
      else
	{
	  min = 0x80;
	  max = 0x7F;
	}
      Qname = "al";
      Rname = "ah";
    }
  else if (srcsize == 16)
    {
      op = BinaryApp::create (BV_OP_CONCAT, 
			      data.get_register ("dx"),
			      data.get_register ("ax"),
			      0, 32);
      if (udiv)
	{
	  min = 0x0000;
	  max = 0xFFFF;
	}
      else
	{
	  min = 0x8000;
	  max = 0X7FFF;
	}
      Qname = "ax";
      Rname = "dx";
    }
  else
    {
      op = BinaryApp::create (BV_OP_CONCAT, 
			      data.get_register ("edx"),
			      data.get_register ("eax"),
			      0, 64);
      if (udiv)
	{
	  min = 0x00000000;
	  max = 0xFFFFFFFF;
	}
      else
	{
	  min = 0x80000000;
	  max = 0X7FFFFFFF;
	}
      Qname = "eax";
      Rname = "edx";
    }

  data.mc->add_skip (from, from + 1, 
		     BinaryApp::createDisequality (src->ref (), 
						   Constant::zero (srcsize)));
  from++;
  Expr *src2 = 
    BinaryApp::createExtend (udiv ? BV_OP_EXTEND_U : BV_OP_EXTEND_S, 
			     src->ref (), 2 * srcsize);

  data.mc->add_assignment (from, (LValue *) temp->ref (),
			   BinaryApp::create (udiv ? BV_OP_DIV_U : BV_OP_DIV_S, 
					      op->ref (), 
					      src2->ref (), 0, 
					      temp->get_bv_size ()));

  Expr *aux = BinaryApp::createExtend (udiv ? BV_OP_EXTEND_U : BV_OP_EXTEND_S, 
				       Constant::create (max, 0, srcsize), 
				       2 * srcsize);
    
  Expr *cond = 
    BinaryApp::create (udiv ? BV_OP_GT_U : BV_OP_GT_S, temp->ref (), aux, 0, 1);
  if (! udiv)
    {
      aux = BinaryApp::createExtend (BV_OP_EXTEND_S, 
				     Constant::create (min, 0, srcsize), 
				     2 * srcsize), 
      cond = 
	BinaryApp::createLOr (cond, 
			      BinaryApp::create (BV_OP_LT_S, 
						 temp->ref (), aux, 0, 1));
    }
  x86_64_if_then_else (from, data, cond, data.next_ma, from + 1);
  from++;
  data.mc->add_assignment (from, (LValue *) temp2->ref (),
			   BinaryApp::create (BV_OP_MODULO, op->ref (), 
					      src2->ref (), 
					      0, srcsize));

  data.mc->add_assignment (from, data.get_register (Qname), 
			   temp->extract_bit_vector (0, srcsize));

  data.mc->add_assignment (from, data.get_register (Rname), 
			   temp2->extract_bit_vector (0, srcsize),
			   data.next_ma);  
  op->deref ();
  temp->deref ();
  temp2->deref ();
  src->deref ();
  src2->deref ();
}

X86_64_TRANSLATE_1_OP(DIV)
{
  s_div (data, op1, true);
}

X86_64_TRANSLATE_1_OP(DIVB)
{
  x86_64_translate_with_size (data, op1, 8, 
			      x86_64_translate<X86_64_TOKEN(DIV)>);
}

X86_64_TRANSLATE_1_OP(DIVL)
{
  x86_64_translate_with_size (data, op1, 32, 
			      x86_64_translate<X86_64_TOKEN(DIV)>);
}

X86_64_TRANSLATE_1_OP(DIVW)
{
  x86_64_translate_with_size (data, op1, 16, 
			      x86_64_translate<X86_64_TOKEN(DIV)>);
}

X86_64_TRANSLATE_1_OP(IDIV)
{
  s_div (data, op1, false);
}

X86_64_TRANSLATE_1_OP(IDIVB)
{
  x86_64_translate_with_size (data, op1, 8, 
			      x86_64_translate<X86_64_TOKEN(IDIV)>);
}

X86_64_TRANSLATE_1_OP(IDIVL)
{
  x86_64_translate_with_size (data, op1, 32, 
			      x86_64_translate<X86_64_TOKEN(IDIV)>);
}

X86_64_TRANSLATE_1_OP(IDIVW)
{
  x86_64_translate_with_size (data, op1, 16, 
			      x86_64_translate<X86_64_TOKEN(IDIV)>);
}
			/* --------------- */

X86_64_TRANSLATE_1_OP(IMUL)
{
  Expr *src = op1;
  int srcsz = src->get_bv_size ();
  MicrocodeAddress from (data.start_ma);
  Expr *cond;

  if (srcsz == 8)
    {
      data.mc->add_assignment (from, data.get_register ("ax"),
			       BinaryApp::create (BV_OP_MUL_S, 
						  data.get_register ("al"),
						  src, 0, 16));

      cond = BinaryApp::createEquality (data.get_register ("ah"), 
					Constant::zero (8));
    }
  else if (srcsz == 16)
    {
      LValue *tmpr = data.get_tmp_register (TMPREG (0), 32);

      data.mc->add_assignment (from, tmpr,
			       BinaryApp::create (BV_OP_MUL_S, 
						  data.get_register ("ax"),
						  src, 0, 32));

      data.mc->add_assignment (from, 
			       data.get_register ("dx"),
			       tmpr->extract_bit_vector (16, 16));
      data.mc->add_assignment (from, 
			       data.get_register ("ax"),
			       tmpr->extract_bit_vector (0, 16));
      Expr *tmp = 
	Expr::createExtend (BV_OP_EXTEND_S, data.get_register ("ax"), 32);
      tmp = Expr::createExtract (tmp, 16, 16);
      cond = BinaryApp::createEquality (tmp, data.get_register ("dx"));
    }
  else
    {
      LValue *tmpr = data.get_tmp_register (TMPREG (0), 64);

      data.mc->add_assignment (from, tmpr,
			       BinaryApp::create (BV_OP_MUL_S, 
						  data.get_register ("eax"),
						  src, 0, 64));

      data.mc->add_assignment (from, data.get_register ("edx"), 
			       tmpr->extract_bit_vector (32, 32));
      data.mc->add_assignment (from, data.get_register ("eax"), 
			       tmpr->extract_bit_vector (0, 32));

      cond = BinaryApp::createEquality (data.get_register ("edx"), 
					Constant::zero (32));
    }

  x86_64_if_then_else (from, data, cond, from + 1, from + 3);
  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::zero (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::zero (1), 
			   data.next_ma); 
  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::one (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::one (1), 
			   data.next_ma);
}

X86_64_TRANSLATE_2_OP(IMUL)
{
  MicrocodeAddress from (data.start_ma);
  Expr *dst = op2;
  int dstsz = dst->get_bv_size ();
  Expr *src = op1;

  Expr::extract_with_bit_vector_of (src, dst);

  LValue *temp = data.get_tmp_register (TMPREG (0), 2 * dstsz);
  data.mc->add_assignment (from, 
			   (LValue *) temp->ref (), 
			   BinaryApp::create (BV_OP_MUL_S, dst->ref (), 
					      src->ref (), 
					      0, temp->get_bv_size ()));
  data.mc->add_assignment (from, 
			   (LValue *) dst->ref (), 
			   temp->extract_bit_vector (0, dstsz));

  Expr *aux = temp->extract_bit_vector (dstsz, dstsz);
  x86_64_if_then_else (from, data,
		       BinaryApp::createDisequality (Constant::zero (dstsz),
						     aux),
		       from + 1, from + 3);
  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::one (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::one (1), 
			   data.next_ma);

  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::zero (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::zero (1), 
			   data.next_ma);
  
  temp->deref ();
  src->deref ();
  dst->deref ();
}

X86_64_TRANSLATE_3_OP(IMUL)
{
  MicrocodeAddress from (data.start_ma);
  Expr *dst = op3;
  int dstsz = dst->get_bv_size ();
  Expr *src1 = op2;
  Constant *src2 = dynamic_cast<Constant *> (op1);

  Expr::extract_with_bit_vector_of (src1, dst);

  assert (src2 != NULL);
  word_t val = src2->get_val ();
  int src2_actual_size;
  
  if ((val & 0xFF) == val) src2_actual_size = 8;
  else if ((val & 0xFFFF) == val) src2_actual_size = 16;
  else src2_actual_size = 32;
  src2->deref ();

  val = BitVectorManip::extend_signed (val, src2_actual_size);
  src2 = Constant::create (val, 0, src1->get_bv_size ());

  LValue *temp = data.get_tmp_register (TMPREG (0), 2 * dstsz);
  data.mc->add_assignment (from, 
			   (LValue *) temp->ref (), 
			   BinaryApp::create (BV_OP_MUL_S, src1->ref (), 
					      src2->ref (), 
					      0, temp->get_bv_size ()));
  data.mc->add_assignment (from, 
			   (LValue *) dst->ref (), 
			   temp->extract_bit_vector (0, dstsz));

  Expr *aux = temp->extract_bit_vector (dstsz, dstsz);
  x86_64_if_then_else (from, data,
		       BinaryApp::createDisequality (Constant::zero (dstsz),
						     aux),
		       from + 1, from + 3);
  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::one (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::one (1), 
			   data.next_ma);

  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::zero (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::zero (1), 
			   data.next_ma);
  
  temp->deref ();
  src1->deref ();
  src2->deref ();
  dst->deref ();
}

X86_64_TRANSLATE_1_OP(IMULB)
{
  x86_64_translate_with_size (data, op1, 8, 
			      x86_64_translate<X86_64_TOKEN(IMUL)>);
}

X86_64_TRANSLATE_2_OP(IMULB)
{
  x86_64_translate_with_size (data, op1, op2, 8, 
			      x86_64_translate<X86_64_TOKEN(IMUL)>);
}

X86_64_TRANSLATE_3_OP(IMULB)
{
  Expr::extract_bit_vector (op1, 0, 8);
  Expr::extract_bit_vector (op2, 0, 8);
  
  x86_64_translate<X86_64_TOKEN(IMUL)> (data, op1, op2, op3);
}

X86_64_TRANSLATE_1_OP(IMULW)
{
  x86_64_translate_with_size (data, op1, 16, 
			      x86_64_translate<X86_64_TOKEN(IMUL)>);
}

X86_64_TRANSLATE_2_OP(IMULW)
{
  x86_64_translate_with_size (data, op1, op2, 16,
			      x86_64_translate<X86_64_TOKEN(IMUL)>);
}

X86_64_TRANSLATE_3_OP(IMULW)
{
  Expr::extract_bit_vector (op1, 0, 16);
  Expr::extract_bit_vector (op2, 0, 16);
  
  x86_64_translate<X86_64_TOKEN(IMUL)> (data, op1, op2, op3);
}

X86_64_TRANSLATE_1_OP(IMULL)
{
  x86_64_translate_with_size (data, op1, 32,
			      x86_64_translate<X86_64_TOKEN(IMUL)>);
}

X86_64_TRANSLATE_2_OP(IMULL)
{
  x86_64_translate_with_size (data, op1, op2, 32,
			      x86_64_translate<X86_64_TOKEN(IMUL)>);
}

X86_64_TRANSLATE_3_OP(IMULL)
{
  Expr::extract_bit_vector (op1, 0, 32);
  Expr::extract_bit_vector (op2, 0, 32);
  
  x86_64_translate<X86_64_TOKEN(IMUL)> (data, op1, op2, op3);
}

X86_64_TRANSLATE_1_OP(MUL)
{
  Expr *upper;
  Expr *lower;
  int op1size = op1->get_bv_size ();
  MicrocodeAddress from (data.start_ma);
  Expr *temp = data.get_tmp_register (TMPREG (0), 2 * op1size);

  if (op1size == 8)
   {
     upper = data.get_register ("ah");
     lower = data.get_register ("al");
    }
  else if (op1size == 16)
    {
     upper = data.get_register ("dx");
     lower = data.get_register ("ax");
    }
  else
    {
     upper = data.get_register ("edx");
     lower = data.get_register ("eax");
    }

  data.mc->add_assignment (from, (LValue *) temp->ref (), 
			   BinaryApp::create (BV_OP_MUL_U, lower->ref (), 
					      op1->ref (),
					      0, temp->get_bv_size ()));
  data.mc->add_assignment (from, (LValue *) lower->ref (), 
			   temp->extract_bit_vector (0, lower->get_bv_size ()));
  data.mc->add_assignment (from, (LValue *) upper->ref (), 
			   temp->extract_bit_vector (lower->get_bv_size (),
						     upper->get_bv_size ()));
  Expr *cond = 
    BinaryApp::createEquality (upper->ref (),
			       Constant::zero (upper->get_bv_size ()));
  x86_64_if_then_else (from, data, cond, from + 1, from + 3);
  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::zero (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::zero (1), 
			   data.next_ma);
  from++;
  data.mc->add_assignment (from, data.get_flag ("cf"), Constant::one (1));
  data.mc->add_assignment (from, data.get_flag ("of"), Constant::one (1), 
			   data.next_ma);

  op1->deref ();
  temp->deref ();
  upper->deref ();
  lower->deref ();
}

X86_64_TRANSLATE_1_OP(MULB)
{
  Expr::extract_bit_vector (op1, 0, 8);
  x86_64_translate<X86_64_TOKEN(MUL)> (data, op1); 
}

X86_64_TRANSLATE_1_OP(MULW)
{
  Expr::extract_bit_vector (op1, 0, 16);
  x86_64_translate<X86_64_TOKEN(MUL)> (data, op1); 
}

X86_64_TRANSLATE_1_OP(MULL)
{
  Expr::extract_bit_vector (op1, 0, 32);
  x86_64_translate<X86_64_TOKEN(MUL)> (data, op1); 
}

X86_64_TRANSLATE_1_OP(NEG)
{
  MicrocodeAddress from (data.start_ma);
  int op1size = op1->get_bv_size ();
  data.mc->add_assignment (from, data.get_flag ("cf"),
			   BinaryApp::create (BV_OP_NEQ, op1->ref (), 
					      Constant::zero (op1size), 0, 1));
  data.mc->add_assignment (from, (LValue *) op1,			   
			   UnaryApp::create (BV_OP_NEG, op1->ref (), 0, 
					     op1size),
			   data.next_ma);
}

X86_64_TRANSLATE_1_OP(NEGB)
{
  Expr::extract_bit_vector (op1, 0, 8);
  x86_64_translate<X86_64_TOKEN(NEG)> (data, op1);   
}

X86_64_TRANSLATE_1_OP(NEGW)
{
  Expr::extract_bit_vector (op1, 0, 16);
  x86_64_translate<X86_64_TOKEN(NEG)> (data, op1);   
}

X86_64_TRANSLATE_1_OP(NEGL)
{
  Expr::extract_bit_vector (op1, 0, 32);
  x86_64_translate<X86_64_TOKEN(NEG)> (data, op1);   
}

X86_64_TRANSLATE_2_OP(SBB)
{
  if (op2->is_MemCell () && ! op1->is_Constant ())
    Expr::extract_bit_vector (op2, 0, op1->get_bv_size ());
  s_adc_sbb (data, op2, op1, BV_OP_SUB);
}

X86_64_TRANSLATE_2_OP(SBBB)
{
  Expr::extract_bit_vector (op2, 0, 8);
  x86_64_translate<X86_64_TOKEN(SBB)> (data, op1, op2);
}

X86_64_TRANSLATE_2_OP(SBBW)
{
  Expr::extract_bit_vector (op2, 0, 16);
  x86_64_translate<X86_64_TOKEN(SBB)> (data, op1, op2);
}

X86_64_TRANSLATE_2_OP(SBBL)
{
  Expr::extract_bit_vector (op2, 0, 32);
  x86_64_translate<X86_64_TOKEN(SBB)> (data, op1, op2);
}

X86_64_TRANSLATE_2_OP(XADD)
{
  Expr *dst = op2;
  Expr *src = op1;
  MicrocodeAddress from (data.start_ma);

  Expr::extract_bit_vector (dst, 0, src->get_bv_size ());
  LValue *temp = data.get_tmp_register (TMPREG (0), dst->get_bv_size () + 1);
  
  data.mc->add_assignment (from, (LValue *) temp->ref (),
			   BinaryApp::create (BV_OP_ADD, 
					      dst->ref (), src->ref (), 0, 
					      temp->get_bv_size ()));

  x86_64_assign_CF (from, data, 
		    temp->extract_bit_vector (dst->get_bv_size (), 1), 
		    NULL);
  Expr *tmp[3];
  
  tmp[0] = dst->extract_bit_vector (dst->get_bv_size () - 1, 1);
  tmp[1] = src->extract_bit_vector (src->get_bv_size () - 1, 1);
  tmp[2] = temp->extract_bit_vector (dst->get_bv_size () - 1, 1);

  tmp[1] = BinaryApp::create (BV_OP_XOR, tmp[0], tmp[1], 0, 1); 
  tmp[1] = UnaryApp::create (BV_OP_NOT, tmp[1], 0, 1);
  
  tmp[0] = BinaryApp::create (BV_OP_XOR, tmp[0]->ref (), tmp[2], 0, 1); 
  
  tmp[2] = BinaryApp::create (BV_OP_AND, tmp[0], tmp[1], 0, 1);
  x86_64_assign_OF (from, data, tmp[2]);

  data.mc->add_assignment (from, (LValue *) dst->ref (), src->ref ());
  data.mc->add_assignment (from, (LValue *) src->ref (), 
			   temp->extract_bit_vector (0, src->get_bv_size ()));

  x86_64_compute_SF (from, data, dst);
  x86_64_compute_ZF (from, data, dst);
  x86_64_compute_AF (from, data, dst);
  x86_64_compute_PF (from, data, dst, &data.next_ma);

  dst->deref ();
  temp->deref ();
  src->deref ();
}

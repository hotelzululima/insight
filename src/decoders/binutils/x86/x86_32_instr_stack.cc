/*
 * Copyright (c) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#include <cassert>
#include <utils/bv-manip.hh>
#include "x86_32_translation_functions.hh"

using namespace std;


X86_32_TRANSLATE_2_OP(ENTER)
{
  Constant *nesting_level = dynamic_cast<Constant *> (op2);
  Constant *frame_size = dynamic_cast<Constant *> (op1);
  MicrocodeAddress from (data.start_ma);
  int operand_size = data.data16 ? 16 : 32;
  int stack_size = data.addr16 ? 16 : 32;

  assert (frame_size != NULL);
  assert (nesting_level != NULL);
  Expr *ebp = data.get_register (stack_size == 32 ? "ebp" : "bp");
  Expr *esp = data.get_register (stack_size == 32 ? "esp" : "sp");
  Expr *frame_temp = esp->ref ();

  x86_32_push (from, data, ebp->ref ());

  int nl = nesting_level->get_val () % 32;
  if (nl > 1)
    {
      Constant *dec = Constant::create (operand_size >> 3, 
					0, ebp->get_bv_size ());
      while (--nl)
	{
	  data.mc->add_assignment (from, (LValue *) ebp->ref (), 
				   BinaryApp::create (BV_OP_SUB, 
						      ebp->ref (),
						      dec->ref (),
						      0, ebp->get_bv_size ()));
	  x86_32_push (from, data, 
		       MemCell::create (ebp->ref (), 0, stack_size));
	}
      dec->deref ();
      x86_32_push (from, data, frame_temp->ref ());     
    }

  data.mc->add_assignment (from, (LValue *) ebp->ref (), frame_temp->ref ());
  data.mc->add_assignment (from, (LValue *) esp->ref (),
			   BinaryApp::create (BV_OP_SUB, 
					      esp->ref (),
					      frame_size->ref (), 
					      0, esp->get_bv_size ()),
			   data.next_ma);

  esp->deref ();
  ebp->deref ();
  frame_temp->deref ();
  nesting_level->deref ();
  frame_size->deref ();
}

X86_32_TRANSLATE_2_OP(ENTERW)
{
  data.data16 = true;
  x86_32_translate<X86_32_TOKEN(ENTER)> (data, op1, op2);
}

X86_32_TRANSLATE_2_OP(ENTERL)
{
  data.data16 = false;
  x86_32_translate<X86_32_TOKEN(ENTER)> (data, op1, op2);
}

X86_32_TRANSLATE_0_OP(LEAVE)
{
  MicrocodeAddress from (data.start_ma);
  LValue *ebp = data.get_register (data.addr16 ? "bp" : "ebp");
  LValue *esp = data.get_register (data.addr16 ? "sp" : "esp");

  data.mc->add_assignment (from, (LValue *) esp->ref (), ebp->ref ());
  x86_32_pop (from, data, (LValue *) ebp->ref (), &data.next_ma);
  esp->deref ();
  ebp->deref ();
}

X86_32_TRANSLATE_0_OP(LEAVEW)
{
  data.data16 = true;
  x86_32_translate<X86_32_TOKEN(LEAVE)> (data);
}

X86_32_TRANSLATE_0_OP(LEAVEL)
{
  data.data16 = false;
  x86_32_translate<X86_32_TOKEN(LEAVE)> (data);
}

static void
s_pop_all(MicrocodeAddress start, MicrocodeAddress end, 
	  x86_32::parser_data &data, const char *regs[]);

X86_32_TRANSLATE_0_OP(POPA)
{
  const char *regs[] = { "edi", "esi", "ebp", "esp", 
			 "ebx", "edx", "ecx", "eax" };

  s_pop_all (data.start_ma, data.next_ma, data, regs);
}

X86_32_TRANSLATE_0_OP(POPAW)
{
  const char *regs[] = { "di", "si", "bp", "sp", 
			 "bx", "dx", "cx", "ax" };
  s_pop_all (data.start_ma, data.next_ma, data, regs);
}

X86_32_TRANSLATE_0_OP(POPAL)
{
  x86_32_translate<X86_32_TOKEN(POPA)> (data);
}


X86_32_TRANSLATE_1_OP(POP)
{
  assert (op1->get_bv_size () == 64 ||
          op1->get_bv_size () == 32 ||
          op1->get_bv_size () == 16);

  x86_32_pop (data.start_ma, data, (LValue *) op1, &data.next_ma);
}


X86_32_TRANSLATE_1_OP(POPW)
{
  data.data16 = true;
  Expr *tmp = op1->extract_bit_vector (0, 16);
  x86_32_pop (data.start_ma, data, (LValue *) tmp, &data.next_ma);
  op1->deref ();
}

			/* --------------- */

X86_32_TRANSLATE_1_OP(POPL)
{
  x86_32_pop (data.start_ma, data, (LValue *) op1, &data.next_ma);
}

			/* --------------- */

void
x86_32_pop (MicrocodeAddress &start, x86_32::parser_data &data, LValue *op,
	    MicrocodeAddress *end)
{
  int stack_size = data.addr16 ? 16 : 32;
  int operand_size = data.data16 ? 16 : 32;
  LValue *esp = data.get_register (stack_size == 32 ? "esp" : "sp");

  if (! (op->is_RegisterExpr () && data.is_segment_register (op)))
    operand_size = op->get_bv_size ();

  Constant *inc = Constant::create (operand_size >> 3, 0, esp->get_bv_size ());
  data.mc->add_assignment (start, (LValue *) op->ref (), 
			   MemCell::create (esp->ref (), 0, 
					    op->get_bv_size ()));

  data.mc->add_assignment (start, (LValue *) esp->ref(), 
			   BinaryApp::create (BV_OP_ADD, esp->ref (), 
					      inc->ref (), 0,
					      esp->get_bv_size ()),
			   end);
  esp->deref ();
  inc->deref ();
  op->deref ();
}

static void
s_pop_all(MicrocodeAddress start, MicrocodeAddress end, 
	  x86_32::parser_data &data, const char *regs[])
{
  int i;
  LValue *reg;
  
  for (i = 0; i < 3; i++)
    {
      reg = data.get_register (regs[i]);
      x86_32_pop (start, data, reg);
    }

  reg = data.get_register (regs[i]); // should be (E)SP
  Expr *nval = BinaryApp::create (BV_OP_ADD, reg->ref (), 
				  reg->get_bv_size () >> 3);
  data.mc->add_assignment (start, reg, nval);

  for (i++; i < 7; i++)
    {
      reg = data.get_register (regs[i]);
      x86_32_pop (start, data, reg);
    }
  reg = data.get_register (regs[i]);
  x86_32_pop (start, data, reg, &end);
}

void
x86_32_push (MicrocodeAddress &start, x86_32::parser_data &data, Expr *op,
	     MicrocodeAddress *end)
{
  Expr *temp = NULL;
  int stack_size = data.addr16 ? 16 : 32; // FIXME: not sure it's ture
  int operand_size = data.data16 ? 16 : 32;

  if (op->is_RegisterExpr () && data.is_segment_register (op))
    {
      if (operand_size == 16)
	temp = op->ref ();
      else
	temp = Expr::createExtend (BV_OP_EXTEND_U, op->ref (), operand_size);
    }
  else if (op->is_Constant ())
    {
      Constant *c = dynamic_cast<Constant *> (op);
      word_t val = c->get_val ();
      temp = Constant::create (val, 0, operand_size);
    }
  else
    temp = op->ref ();

  Expr *esp = data.get_register (stack_size == 16 ? "sp" : "esp");
  data.mc->add_assignment (start, (LValue *) esp->ref(), 
			   BinaryApp::create (BV_OP_SUB, esp->ref (), 
					      temp->get_bv_size () >> 3, 0,
					      esp->get_bv_size ()));
  data.mc->add_assignment (start, 
			   MemCell::create (esp->ref (), 0, 
					    temp->get_bv_size ()), 
			   temp->ref (), 
			   end); 
  temp->deref ();
  op->deref ();
  esp->deref ();
}

X86_32_TRANSLATE_1_OP(PUSH)
{  
  x86_32_push (data.start_ma, data, (LValue *) op1, &data.next_ma);
}

X86_32_TRANSLATE_1_OP(PUSHW)
{
  data.data16 = true;
  x86_32_translate_with_size (data, op1, 16, 
			      x86_32_translate<X86_32_TOKEN(PUSH)>);
}

X86_32_TRANSLATE_1_OP(PUSHL)
{
  x86_32_translate<X86_32_TOKEN(PUSH)> (data, op1);
}


X86_32_TRANSLATE_0_OP(POPF)
{
  MicrocodeAddress from (data.start_ma);
#ifdef X86_32_USE_EFLAGS
  Expr *eflags = data.get_register ("eflags");
#else
  Expr *eflags = data.get_tmp_register (TMPREG (0), 32);
#endif  
  if (data.data16)
    Expr::extract_bit_vector (eflags, 0, 16);
  
#ifdef X86_32_USE_EFLAGS
  x86_32_pop (from, data, (LValue *) eflags->ref (), &data.next_ma);
#else
  x86_32_pop (from, data, (LValue *) eflags->ref ());

  const char *flags[] = { "cf", "pf", "af", "zf", "sf", "tf", "if", 
			  "df", "of", "iopl", "nt", "rf", "vm", "ac", "vif",
			  "vip", "id" };
  int nb_flags = sizeof (flags)/ sizeof (flags[0]);
  int size_offset[] = { 1, 0, 1, 2, 1, 4, 1, 6, 1, 7, 1, 8, 1, 9, 1, 10,
			1, 11, 2, 12, 1, 14, 1, 16, 1, 17, 1, 18, 1, 19,
			1, 20, 1, 21 };
  int i;
  if (data.data16)
    nb_flags = 11;
  
  for (i = 0; i < nb_flags - 1; i++)
    {
      int size = size_offset[2 * i];
      int offset = size_offset[2 * i + 1];
      
      data.mc->add_assignment (from, 
			       data.get_register (flags[i]),
			       Expr::createExtract (eflags->ref (), offset,
						    size));
    }
  int size = size_offset[2 * i];
  int offset = size_offset[2 * i + 1];
  data.mc->add_assignment (from, 
			   data.get_register (flags[i]),
			   Expr::createExtract (eflags->ref (), offset,
						size),
			   &data.next_ma);
#endif
  eflags->deref ();
}

X86_32_TRANSLATE_0_OP(POPFW)
{
  data.data16 = true;
  x86_32_translate<X86_32_TOKEN(POPF)> (data);
}

X86_32_TRANSLATE_0_OP(PUSHF)
{
  MicrocodeAddress from (data.start_ma);  
#ifdef X86_32_USE_EFLAGS
  Expr *eflags = data.get_register ("eflags");
#else
  const char *flags[] = { "cf", 0, "pf", 0, "af", 0, "zf", "sf", "tf", "if", 
			  "df", "of", "iopl", "nt", 0, "rf", "vm", "ac", "vif",
			  "vip", "id" };

  Expr *eflags = data.get_register ("cf");

  for (size_t i = 1; i < sizeof (flags) / sizeof (flags[0]); i++)
    {
      Expr *aux = flags[i] 
	? (Expr *) data.get_register (flags[i]) : (Expr *) Constant::zero (1);
      eflags = BinaryApp::createConcat (aux, eflags);
    }
  eflags = Expr::createExtend (BV_OP_EXTEND_U, eflags, 32); 
#endif

  if (data.data16)
    Expr::extract_bit_vector (eflags, 0, 16);
  else
    {
      Expr *tmp = BinaryApp::create (BV_OP_AND, eflags,
				     Constant::create (0x00FCFFFF, 0,
						       eflags->get_bv_size ()),
				     0, eflags->get_bv_size ());
      eflags = tmp;
    }
  x86_32_push (from, data, eflags, &data.next_ma);
}

X86_32_TRANSLATE_0_OP(PUSHFW)
{
  data.data16 = true;
  x86_32_translate<X86_32_TOKEN(PUSHF)> (data);
}

X86_32_TRANSLATE_0_OP(PUSHA)
{
  LValue *temp = data.get_tmp_register (TMPREG (0), data.data16 ? 16 : 32);
  MicrocodeAddress from (data.start_ma);
  const char *regs32[] = { "esp", "eax", "ecx", "edx", "ebx", "ebp", "esi", 
			   "edi" };
  const char *regs16[] = { "sp", "ax", "cx", "dx", "bx", "bp", "si", 
			   "di" };
  const char **regs = data.data16 ? regs16 : regs32;

  data.mc->add_assignment (from, (LValue *) temp->ref (), 
			   data.get_register (regs[0]));
  
  x86_32_push (from, data, data.get_register (regs[1]));
  x86_32_push (from, data, data.get_register (regs[2]));
  x86_32_push (from, data, data.get_register (regs[3]));
  x86_32_push (from, data, data.get_register (regs[4]));
  x86_32_push (from, data, temp->ref ());
  x86_32_push (from, data, data.get_register (regs[5]));
  x86_32_push (from, data, data.get_register (regs[6]));
  x86_32_push (from, data, data.get_register (regs[7]), &data.next_ma); 
  temp->deref ();
}

X86_32_TRANSLATE_0_OP(PUSHAW)
{
  data.data16 = true;
  x86_32_translate<X86_32_TOKEN(PUSHA)> (data);
}

X86_32_TRANSLATE_0_OP(PUSHAL)
{
  x86_32_translate<X86_32_TOKEN(PUSHA)> (data);
}


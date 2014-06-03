/*
 * Copyright (c) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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
#include "x86_translation_functions.hh"

using namespace std;


X86_TRANSLATE_2_OP(ENTER)
{
  Constant *frame_size    = dynamic_cast<Constant *> (op1);
  Constant *nesting_level = dynamic_cast<Constant *> (op2);

  assert (frame_size != NULL);
  assert (nesting_level != NULL);

  MicrocodeAddress from (data.start_ma);
  int stack_size   = data.addr_mode;
  int operand_size = data.data_mode;

  Expr *_bp = NULL; /* Base pointer register */
  Expr *_sp = NULL; /* Stack pointer register */

  switch (stack_size)
    {
    case x86::parser_data::MODE_16:
      _bp = data.get_register ("bp");
      _sp = data.get_register ("sp");
      break;

    case x86::parser_data::MODE_32:
      _bp = data.get_register ("ebp");
      _sp = data.get_register ("esp");
      break;

    case x86::parser_data::MODE_64:
      _bp = data.get_register ("rbp");
      _sp = data.get_register ("rsp");
      break;
    }

  assert(_bp != NULL);
  assert(_sp != NULL);

  Expr *frame_temp = _sp->ref ();
  x86_push (from, data, _bp->ref ());

  int nl = nesting_level->get_val () % 32;
  if (nl > 1)
    {
      Constant *dec = Constant::create (operand_size >> 3,
					0, _bp->get_bv_size ());
      while (--nl)
	{
	  data.mc->add_assignment (from, (LValue *) _bp->ref (),
				   BinaryApp::create (BV_OP_SUB,
						      _bp->ref (),
						      dec->ref (),
						      0, _bp->get_bv_size ()));
	  x86_push (from, data,
		       MemCell::create (_bp->ref (), 0, operand_size));
	}
      dec->deref ();
      x86_push (from, data, frame_temp->ref ());
    }

  data.mc->add_assignment (from, (LValue *) _bp->ref (), frame_temp->ref ());
  data.mc->add_assignment (from, (LValue *) _sp->ref (),
			   BinaryApp::create (BV_OP_SUB,
					      _sp->ref (),
					      frame_size->ref (),
					      0, _sp->get_bv_size ()),
			   data.next_ma);

  _sp->deref ();
  _bp->deref ();
  frame_temp->deref ();
  nesting_level->deref ();
  frame_size->deref ();
}

X86_TRANSLATE_2_OP(ENTERW)
{
  data.data_mode = x86::parser_data::MODE_16;
  x86_translate<X86_TOKEN(ENTER)> (data, op1, op2);
}

X86_TRANSLATE_2_OP(ENTERL)
{
  data.data_mode = x86::parser_data::MODE_32;
  x86_translate<X86_TOKEN(ENTER)> (data, op1, op2);
}

X86_TRANSLATE_2_OP(ENTERQ)
{
  data.data_mode = x86::parser_data::MODE_64;
  x86_translate<X86_TOKEN(ENTER)> (data, op1, op2);
}

X86_TRANSLATE_0_OP(LEAVE)
{
  MicrocodeAddress from (data.start_ma);
  int stack_size = data.addr_mode;

  Expr *_bp = NULL;
  Expr *_sp = NULL;

  switch (stack_size)
    {
    case x86::parser_data::MODE_16:
      _bp = data.get_register ("bp");
      _sp = data.get_register ("sp");
      break;

    case x86::parser_data::MODE_32:
      _bp = data.get_register ("ebp");
      _sp = data.get_register ("esp");
      break;

    case x86::parser_data::MODE_64:
      _bp = data.get_register ("rbp");
      _sp = data.get_register ("rsp");
      break;
    }

  assert (_bp != NULL);
  assert (_sp != NULL);

  data.mc->add_assignment (from, (LValue *) _sp->ref (), _bp->ref ());
  x86_pop (from, data, (LValue *) _bp->ref (), &data.next_ma);
  _sp->deref ();
  _bp->deref ();
}

X86_TRANSLATE_0_OP(LEAVEW)
{
  data.data_mode = x86::parser_data::MODE_16;
  x86_translate<X86_TOKEN(LEAVE)> (data);
}

X86_TRANSLATE_0_OP(LEAVEL)
{
  data.data_mode = x86::parser_data::MODE_32;
  x86_translate<X86_TOKEN(LEAVE)> (data);
}

X86_TRANSLATE_0_OP(LEAVEQ)
{
  data.data_mode = x86::parser_data::MODE_64;
  x86_translate<X86_TOKEN(LEAVE)> (data);
}

static void
s_pop_all(MicrocodeAddress start, MicrocodeAddress end,
	  x86::parser_data &data, const char *regs[]);

X86_TRANSLATE_0_OP(POPA)
{
  const char *regs32[] =
    { "edi", "esi", "ebp", "esp", "ebx", "edx", "ecx", "eax" };

  const char *regs16[] =
    { "di", "si", "bp", "sp", "bx", "dx", "cx", "ax" };

  const char **regs = NULL;
  switch (data.data_mode)
    {
    case x86::parser_data::MODE_16:
      regs = regs16;
      break;

    case x86::parser_data::MODE_32:
      regs = regs32;
      break;

    case x86::parser_data::MODE_64:
      /* POPA is not a valid instruction in 64-bits mode */
      regs = NULL;
      break;
    }

  assert(regs != NULL);

  s_pop_all (data.start_ma, data.next_ma, data, regs);
}

X86_TRANSLATE_0_OP(POPAW)
{
  const char *regs[] =
    { "di", "si", "bp", "sp", "bx", "dx", "cx", "ax" };

  s_pop_all (data.start_ma, data.next_ma, data, regs);
}

X86_TRANSLATE_0_OP(POPAL)
{
  x86_translate<X86_TOKEN(POPA)> (data);
}


X86_TRANSLATE_1_OP(POP)
{
  assert (op1->get_bv_size () == 64 ||
          op1->get_bv_size () == 32 ||
          op1->get_bv_size () == 16);

  x86_pop (data.start_ma, data, (LValue *) op1, &data.next_ma);
}


X86_TRANSLATE_1_OP(POPW)
{
  data.data_mode = x86::parser_data::MODE_16;
  Expr *tmp = op1->extract_bit_vector (0, 16);
  x86_pop (data.start_ma, data, (LValue *) tmp, &data.next_ma);
  op1->deref ();
}

X86_TRANSLATE_1_OP(POPL)
{
  x86_pop (data.start_ma, data, (LValue *) op1, &data.next_ma);
}

X86_TRANSLATE_1_OP(POPQ)
{
  x86_pop (data.start_ma, data, (LValue *) op1, &data.next_ma);
}

void
x86_pop (MicrocodeAddress &start,
	 x86::parser_data &data, LValue *op,
	 MicrocodeAddress *end)
{
  int operand_size = data.data_mode;

  Expr *_sp = NULL;

  switch (data.addr_mode)
    {
    case x86::parser_data::MODE_16:
      _sp = data.get_register ("sp");
      break;

    case x86::parser_data::MODE_32:
      _sp = data.get_register ("esp");
      break;

    case x86::parser_data::MODE_64:
      _sp = data.get_register ("rsp");
      break;
    }

  assert(_sp != NULL);

  if (! (op->is_RegisterExpr () && data.is_segment_register (op)))
    operand_size = op->get_bv_size ();

  Constant *inc = Constant::create (operand_size >> 3, 0, _sp->get_bv_size ());
  data.mc->add_assignment (start, (LValue *) op->ref (),
			   MemCell::create (_sp->ref (), 0,
					    op->get_bv_size ()));

  data.mc->add_assignment (start, (LValue *) _sp->ref(),
			   BinaryApp::create (BV_OP_ADD, _sp->ref (),
					      inc->ref (), 0,
					      _sp->get_bv_size ()),
			   end);
  _sp->deref ();
  inc->deref ();
  op->deref ();
}

static void
s_pop_all(MicrocodeAddress start, MicrocodeAddress end,
	  x86::parser_data &data, const char *regs[])
{
  int i;
  LValue *reg;

  for (i = 0; i < 3; i++)
    {
      reg = data.get_register (regs[i]);
      x86_pop (start, data, reg);
    }

  reg = data.get_register (regs[i]); // should be (R/E)SP
  Expr *nval = BinaryApp::create (BV_OP_ADD, reg->ref (),
				  reg->get_bv_size () >> 3);
  data.mc->add_assignment (start, reg, nval);

  for (i++; i < 7; i++)
    {
      reg = data.get_register (regs[i]);
      x86_pop (start, data, reg);
    }
  reg = data.get_register (regs[i]);
  x86_pop (start, data, reg, &end);
}

void
x86_push (MicrocodeAddress &start, x86::parser_data &data, Expr *op,
	     MicrocodeAddress *end)
{
  Expr *temp = NULL;
  int operand_size = data.data_mode;

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

  Expr *_sp = NULL;

  switch (data.addr_mode)
    {
    case x86::parser_data::MODE_16:
      _sp = data.get_register ("sp");
      break;

    case x86::parser_data::MODE_32:
      _sp = data.get_register ("esp");
      break;

    case x86::parser_data::MODE_64:
      _sp = data.get_register ("rsp");
      break;
    }

  assert(_sp != NULL);

  data.mc->add_assignment (start, (LValue *) _sp->ref(),
			   BinaryApp::create (BV_OP_SUB, _sp->ref (),
					      temp->get_bv_size () >> 3, 0,
					      _sp->get_bv_size ()));
  data.mc->add_assignment (start,
			   MemCell::create (_sp->ref (), 0,
					    temp->get_bv_size ()),
			   temp->ref (),
			   end);
  temp->deref ();
  op->deref ();
  _sp->deref ();
}

X86_TRANSLATE_1_OP(PUSH)
{
  x86_push (data.start_ma, data, (LValue *) op1, &data.next_ma);
}

X86_TRANSLATE_1_OP(PUSHW)
{
  data.data_mode = x86::parser_data::MODE_16;
  x86_translate_with_size (data, op1, 16,
			      x86_translate<X86_TOKEN(PUSH)>);
}

X86_TRANSLATE_1_OP(PUSHL)
{
  x86_translate<X86_TOKEN(PUSH)> (data, op1);
}

X86_TRANSLATE_1_OP(PUSHQ)
{
  x86_translate<X86_TOKEN(PUSH)> (data, op1);
}

X86_TRANSLATE_0_OP(POPF)
{
  MicrocodeAddress from (data.start_ma);
#ifdef X86_USE_EFLAGS
  Expr *eflags = data.get_register ("eflags");
#else
  Expr *eflags = data.get_tmp_register (TMPREG (0), 32);
#endif
  if (data.data_mode == 16)
    Expr::extract_bit_vector (eflags, 0, 16);

#ifdef X86_USE_EFLAGS
  x86_pop (from, data, (LValue *) eflags->ref (), &data.next_ma);
#else
  x86_pop (from, data, (LValue *) eflags->ref ());

  const char *flags[] = { "cf", "pf", "af", "zf", "sf", "tf", "if",
			  "df", "of", "iopl", "nt", "rf", "vm", "ac", "vif",
			  "vip", "id" };
  int nb_flags = sizeof (flags)/ sizeof (flags[0]);
  int size_offset[] = { 1, 0, 1, 2, 1, 4, 1, 6, 1, 7, 1, 8, 1, 9, 1, 10,
			1, 11, 2, 12, 1, 14, 1, 16, 1, 17, 1, 18, 1, 19,
			1, 20, 1, 21 };
  int i;
  if (data.data_mode == x86::parser_data::MODE_16)
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

X86_TRANSLATE_0_OP(POPFW)
{
  data.data_mode = x86::parser_data::MODE_16;
  x86_translate<X86_TOKEN(POPF)> (data);
}

X86_TRANSLATE_0_OP(PUSHF)
{
  MicrocodeAddress from (data.start_ma);
#ifdef X86_USE_EFLAGS
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

  if (data.data_mode == x86::parser_data::MODE_16)
    Expr::extract_bit_vector (eflags, 0, 16);
  else
    {
      Expr *tmp = BinaryApp::create (BV_OP_AND, eflags,
				     Constant::create (0x00FCFFFF, 0,
						       eflags->get_bv_size ()),
				     0, eflags->get_bv_size ());
      eflags = tmp;
    }
  x86_push (from, data, eflags, &data.next_ma);
}

X86_TRANSLATE_0_OP(PUSHFW)
{
  data.data_mode = x86::parser_data::MODE_16;
  x86_translate<X86_TOKEN(PUSHF)> (data);
}

X86_TRANSLATE_0_OP(PUSHA)
{
  LValue *temp = data.get_tmp_register (TMPREG (0), data.data_mode);
  MicrocodeAddress from (data.start_ma);

  const char *regs32[] =
    { "esp", "eax", "ecx", "edx", "ebx", "ebp", "esi", "edi" };

  const char *regs16[] =
    { "sp", "ax", "cx", "dx", "bx", "bp", "si", "di" };

  const char **regs = NULL;
  switch (data.data_mode)
    {
    case x86::parser_data::MODE_16:
      regs = regs16;
      break;

    case x86::parser_data::MODE_32:
      regs = regs32;
      break;

    case x86::parser_data::MODE_64:
      /* PUSHA is not a valid instruction in 64-bits mode */
      regs = NULL;
      break;
    }

  assert(regs != NULL);

  data.mc->add_assignment (from, (LValue *) temp->ref (),
			   data.get_register (regs[0]));

  x86_push (from, data, data.get_register (regs[1]));
  x86_push (from, data, data.get_register (regs[2]));
  x86_push (from, data, data.get_register (regs[3]));
  x86_push (from, data, data.get_register (regs[4]));
  x86_push (from, data, temp->ref ());
  x86_push (from, data, data.get_register (regs[5]));
  x86_push (from, data, data.get_register (regs[6]));
  x86_push (from, data, data.get_register (regs[7]), &data.next_ma);
  temp->deref ();
}

X86_TRANSLATE_0_OP(PUSHAW)
{
  data.data_mode = x86::parser_data::MODE_16;
  x86_translate<X86_TOKEN(PUSHA)> (data);
}

X86_TRANSLATE_0_OP(PUSHAL)
{
  x86_translate<X86_TOKEN(PUSHA)> (data);
}


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

#include <cassert>
#include "x86_32_translation_functions.hh"

using namespace std;

static void
s_pop_all(MicrocodeAddress start, MicrocodeAddress end, 
	  x86_32::parser_data &data, const char *regs[]);

			/* --------------- */

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

X86_32_TRANSLATE_1_OP(POP)
{
  assert (op1->get_bv_size () == 32 || op1->get_bv_size () == 16);

  x86_32_pop (data.start_ma, data, (LValue *) op1, &data.next_ma);
}


X86_32_TRANSLATE_1_OP(POPW)
{
  Expr::extract_bit_vector (op1, 0, 16);
  x86_32_pop (data.start_ma, data, (LValue *) op1, &data.next_ma);
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
  LValue *esp = x86_32_translate_esp (data);

  data.mc->add_assignment (start, op, 
			   MemCell::create (esp->ref (),
					    op->get_bv_offset (),
					    op->get_bv_size ()));
  data.mc->add_assignment (start, (LValue *) esp->ref(), 
			   BinaryApp::create (ADD, esp->ref (), 
					      op->get_bv_size () >> 3), 
			   end);
  esp->deref ();
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
  Expr *nval = BinaryApp::create (ADD, reg->ref (), reg->get_bv_size () >> 3);
  data.mc->add_assignment (start, reg, nval);

  for (; i < 6; i++)
    {
      reg = data.get_register (regs[i]);
      x86_32_pop (start, data, reg);
    }
  reg = data.get_register (regs[i]);
  x86_32_pop (start, data, reg, &end);
}

/*****************************************************************************/

void
x86_32_push (MicrocodeAddress &start, x86_32::parser_data &data, Expr *op,
	     MicrocodeAddress *end)
{
  LValue *esp = x86_32_translate_esp (data);

  data.mc->add_assignment (start, (LValue *) esp->ref(), 
			   BinaryApp::create (SUB, esp->ref (), 
					      op->get_bv_size () >> 3));
  data.mc->add_assignment (start, 
			   MemCell::create (esp->ref (),
					    op->get_bv_offset (),
					    op->get_bv_size ()), 
			   op, 
			   end); 
  esp->deref ();
}

X86_32_TRANSLATE_1_OP(PUSH)
{
  x86_32_push (data.start_ma, data, (LValue *) op1, &data.next_ma);
}

X86_32_TRANSLATE_1_OP(PUSHW)
{
  Expr::extract_bit_vector (op1, 0, 16);
  x86_32_translate<X86_32_TOKEN(PUSH)> (data, op1);
}

X86_32_TRANSLATE_1_OP(PUSHL)
{
  x86_32_translate<X86_32_TOKEN(PUSH)> (data, op1);
}

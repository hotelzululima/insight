/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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

#include "x86_translation_functions.hh"

using namespace std;

static void
s_loop (x86::parser_data &data, Expr *op1, Expr *cond)
{
  MicrocodeAddress from (data.start_ma);

  Expr *_cx = NULL;

  switch (data.addr_mode)
    {
    case x86::parser_data::MODE_16:
      _cx = data.get_register ("cx");
      break;

    case x86::parser_data::MODE_32:
      _cx = data.get_register ("ecx");
      break;

    case x86::parser_data::MODE_64:
      _cx = data.get_register ("rcx");
      break;
    }

  assert(_cx != NULL);

  int csize = _cx->get_bv_size ();
  Expr *ccond =
    BinaryApp::create (BV_OP_NEQ, _cx->ref (), Constant::zero(csize), 0, 1);

  if (cond == NULL)
    cond = ccond->ref ();
  else
    cond = BinaryApp::create (BV_OP_AND, ccond->ref (), cond, 0, 1);

  data.mc->add_assignment (from, (LValue *) _cx->ref (),
			   BinaryApp::create (BV_OP_SUB, _cx->ref (),
					      Constant::one (csize), 0, csize));

  MemCell *jmpaddr = dynamic_cast<MemCell *> (op1);
  assert (jmpaddr);
  assert (jmpaddr->get_addr ()->is_Constant ());
  MicrocodeAddress ja =
    dynamic_cast<Constant *>(jmpaddr->get_addr ())->get_val ();

  x86_if_then_else (from, data, cond->ref (), ja, data.next_ma);

  op1->deref ();
  cond->deref ();
  ccond->deref ();
  _cx->deref ();
}

X86_TRANSLATE_1_OP(LOOP)
{
  s_loop (data, op1, NULL);
}

X86_TRANSLATE_1_OP(LOOPL)
{
  x86_translate<X86_TOKEN(LOOP)> (data, op1);
}

X86_TRANSLATE_1_OP(LOOPE)
{
  s_loop (data, op1, data.get_flag ("zf"));
}

X86_TRANSLATE_1_OP(LOOPEL)
{
  x86_translate<X86_TOKEN(LOOPE)> (data, op1);
}

X86_TRANSLATE_1_OP(LOOPNE)
{
  s_loop (data, op1, UnaryApp::create (BV_OP_NOT, data.get_flag ("zf"), 0, 1));
}

X86_TRANSLATE_1_OP(LOOPNEL)
{
  x86_translate<X86_TOKEN(LOOPNE)> (data, op1);
}

X86_TRANSLATE_1_OP(LOOPW)
{
  data.addr_mode = x86::parser_data::MODE_16;
  s_loop (data, op1, NULL);
}

X86_TRANSLATE_1_OP(LOOPWL)
{
  x86_translate<X86_TOKEN(LOOPW)> (data, op1);
}

X86_TRANSLATE_1_OP(LOOPEW)
{
  data.addr_mode = x86::parser_data::MODE_16;
  s_loop (data, op1, data.get_flag ("zf"));
}

X86_TRANSLATE_1_OP(LOOPEWL)
{
  x86_translate<X86_TOKEN(LOOPEW)> (data, op1);
}

X86_TRANSLATE_1_OP(LOOPNEW)
{
  data.addr_mode = x86::parser_data::MODE_16;
  s_loop (data, op1, UnaryApp::create (BV_OP_NOT, data.get_flag ("zf"), 0, 1));
}

X86_TRANSLATE_1_OP(LOOPNEWL)
{
  x86_translate<X86_TOKEN(LOOPNEW)> (data, op1);
}


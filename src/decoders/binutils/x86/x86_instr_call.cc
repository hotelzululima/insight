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
#include <kernel/annotations/CallRetAnnotation.hh>
#include "x86_translation_functions.hh"

using namespace std;

X86_TRANSLATE_1_OP (CALL)
{
  address_t next = data.next_ma.getGlobal ();
  MicrocodeAddress start = data.start_ma;
  MemCell *mc = dynamic_cast<MemCell *> (op1);

  assert (mc != NULL);

  x86_push (start, data, Constant::create (next,0, data.arch->get_word_size ()));

  Expr *addr = mc->get_addr ();
  MicrocodeAddress here (start);
  if (addr->is_Constant ())
    {
      MicrocodeAddress fct (dynamic_cast<Constant *>(addr)->get_val ());
      data.mc->add_skip (start, fct);
    }
  else
    {
      data.mc->add_jump (start, addr ->ref ());
    }
  MicrocodeNode *start_node = data.mc->get_node (here);
  start_node->add_annotation (CallRetAnnotation::ID,
			      CallRetAnnotation::create_call (addr));
  mc->deref ();
}

X86_TRANSLATE_1_OP (CALLQ)
{
  assert (op1->get_bv_size() == 64);

  x86_translate<X86_TOKEN(CALL)> (data, op1);
}

X86_TRANSLATE_0_OP (RET)
{
  LValue *tmpr0 = data.get_tmp_register (TMPREG (0), data.arch->get_word_size ());
  MicrocodeAddress start = data.start_ma;
  x86_pop (start, data, tmpr0);

  MicrocodeNode *start_node = data.mc->get_node (start);
  start_node->add_annotation (CallRetAnnotation::ID,
			      CallRetAnnotation::create_ret ());
  data.mc->add_jump (start, tmpr0->ref ());
  if (data.has_prefix)
    data.has_prefix = false;
}

X86_TRANSLATE_0_OP (RETQ)
{
  x86_translate<X86_TOKEN(RET)> (data);
}

X86_TRANSLATE_0_OP (RETW)
{
  x86_translate<X86_TOKEN(RET)> (data);
}

X86_TRANSLATE_1_OP (RET)
{
  LValue *tmpr0 = data.get_tmp_register (TMPREG (0), data.arch->get_word_size ());
  MicrocodeAddress start = data.start_ma;
  x86_pop (start, data, tmpr0);

  int stack_size = data.addr_mode;

  LValue *_sp = NULL;
  switch (stack_size)
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

  assert (_sp != NULL);

  assert (op1->is_Constant ());
  Expr *inc = op1->extract_bit_vector (0, _sp->get_bv_size ());

  data.mc->add_assignment (start, (LValue *) _sp->ref(),
			   BinaryApp::create (BV_OP_ADD, _sp->ref (),
					      inc->ref (), 0,
					      _sp->get_bv_size ()));

  MicrocodeNode *start_node = data.mc->get_node (start);
  start_node->add_annotation (CallRetAnnotation::ID,
			      CallRetAnnotation::create_ret ());
  data.mc->add_jump (start, tmpr0->ref ());
  if (data.has_prefix)
    data.has_prefix = false;
  _sp->deref ();
  op1->deref ();
  inc->deref ();
}

X86_TRANSLATE_1_OP (RETQ)
{
  assert (op1->get_bv_size() == 64);

  x86_translate<X86_TOKEN(RET)> (data, op1);
}

X86_TRANSLATE_1_OP (RETW)
{
  x86_translate<X86_TOKEN(RET)> (data, op1);
}

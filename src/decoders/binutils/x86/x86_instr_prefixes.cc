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

#include "x86_translation_functions.hh"

using namespace std;

X86_TRANSLATE_0_OP(DATA16)
{
  x86_skip (data);
}

X86_TRANSLATE_PREFIX(ADDR16)
{
  if (start)
    {
      /* Saving current addressing mode and setting local mode to 16 */
      data.saved_addr_mode = data.addr_mode;
      data.addr_mode = x86::parser_data::MODE_16;
    }
  else
    {
      /* Restoring the addressing mode after the instruction */
      data.addr_mode = data.saved_addr_mode;
    }
}

X86_TRANSLATE_PREFIX(ADDR32)
{
  if (start)
    {
      /* Saving current addressing mode and setting local mode to 32 */
      data.saved_addr_mode = data.addr_mode;
      data.addr_mode = x86::parser_data::MODE_32;
    }
  else
    {
      /* Restoring the addressing mode after the instruction */
      data.addr_mode = data.saved_addr_mode;
    }
}

X86_TRANSLATE_PREFIX(DATA16)
{
  if (start)
    {
      /* Saving current data mode and setting local mode to 16 */
      data.saved_data_mode = data.data_mode;
      data.data_mode = x86::parser_data::MODE_16;
    }
  else
    {
      /* Restoring the data mode after the instruction */
      data.data_mode = data.saved_data_mode;
    }
}

X86_TRANSLATE_PREFIX(DATA32)
{
  if (start)
    {
      /* Saving current data mode and setting local mode to 32 */
      data.saved_data_mode = data.data_mode;
      data.data_mode = x86::parser_data::MODE_32;
    }
  else
    {
      /* Restoring the data mode after the instruction */
      data.data_mode = data.saved_data_mode;
    }
}

X86_TRANSLATE_PREFIX(LOCK)
{
  if (start)
    data.lock = true;
}

static void
s_start_rep (x86::parser_data &data)
{
  assert (! data.has_prefix);

  LValue *_cx = NULL;

  switch (data.addr_mode)
    {
    case x86::parser_data::MODE_16:
      _cx =  data.get_register ("cx");
      break;

    case x86::parser_data::MODE_32:
      _cx = data.get_register ("ecx");
      break;

    case x86::parser_data::MODE_64:
      _cx = data.get_register ("rcx");
      break;
    }

  assert(_cx != NULL);

  Expr *zero = Constant::zero (_cx->get_bv_size ());
  Expr *stopcond = BinaryApp::createEquality (_cx, zero);
  data.has_prefix = true;
  x86_if_then_else (data.start_ma, data, stopcond,
		       data.next_ma, data.start_ma + 1);
  data.start_ma++;
}

static void
s_end_rep (x86::parser_data &data, Expr *cond)
{
  if (! data.has_prefix)
    {
      cond->deref ();
      return;
    }
  MicrocodeAddress start (data.start_ma);

  LValue *_cx = NULL;
  switch (data.addr_mode)
    {
    case x86::parser_data::MODE_16:
      _cx =  data.get_register ("cx");
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
  Expr *stopcond = BinaryApp::createEquality (_cx->ref (),
					      Constant::zero (csize));

  data.mc->add_assignment (start, _cx,
			   BinaryApp::create (BV_OP_SUB, _cx->ref (),
					      Constant::one (csize), 0,
					      csize));

  if (cond)
    {
      cond = BinaryApp::createEquality (data.get_register ("zf"), cond);
      stopcond = BinaryApp::create (BV_OP_OR, stopcond, cond);
    }

  x86_if_then_else (start, data, stopcond, data.next_ma,
		       MicrocodeAddress (data.start_ma.getGlobal ()));

  data.has_prefix = false;
}

static void
s_rep (x86::parser_data &data, bool start, Expr *zf_val)
{
  if (start)
    s_start_rep (data);
  else
    s_end_rep (data, zf_val);
}

X86_TRANSLATE_PREFIX(REP)
{
  s_rep (data, start, NULL);
}

X86_TRANSLATE_PREFIX(REPE)
{
  s_rep (data, start, start ? NULL : Constant::zero (1));
}

X86_TRANSLATE_PREFIX(REPZ)
{
  s_rep (data, start, start ? NULL : Constant::zero (1));
}

X86_TRANSLATE_PREFIX(REPNE)
{
  s_rep (data, start, start ? NULL : Constant::one (1));
}

X86_TRANSLATE_PREFIX(REPNZ)
{
  s_rep (data, start, start ? NULL : Constant::one (1));
}

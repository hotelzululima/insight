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
s_mov (x86_32::parser_data &data, Expr *inc)
{
  MicrocodeAddress start (data.start_ma);
  MicrocodeAddress next = data.has_prefix ? start + 6 : data.next_ma;
  MicrocodeAddress ifaddr;
  LValue *si = data.get_register (data.addr16 ? "si" : "esi");
  LValue *di = data.get_register (data.addr16 ? "di" : "edi");
  LValue *df = data.get_flag ("df");

  data.mc->add_assignment (start, MemCell::create (di), MemCell::create (si),
			   start + 1);

  data.mc->add_skip (start + 1, start + 2, 
		     BinaryApp::create (EQ, df, Constant::zero ()));

  data.mc->add_skip (start + 1, start + 4,
		     BinaryApp::create (NEQ, df->ref (), Constant::zero ()));

  data.mc->add_assignment (start + 2, (LValue *) si->ref (), 
			   BinaryApp::create (ADD, si->ref (), inc->ref ()),
			   start + 3);

  data.mc->add_assignment (start + 3, (LValue *) di->ref (), 
			   BinaryApp::create (ADD, di->ref (), inc->ref ()), 
			   next);
  
  data.mc->add_assignment (start + 4, (LValue *) si->ref (), 
			   BinaryApp::create (SUB, si->ref (), inc->ref ()),
			   start + 5);

  data.mc->add_assignment (start + 5, (LValue *) di->ref (), 
			   BinaryApp::create (SUB, di->ref (), inc->ref ()), 
			   next);  
  if (data.has_prefix)
    data.start_ma = next;
  inc->deref ();
}

X86_32_TRANSLATE_0_OP(MOVSB)
{
  s_mov (data, Constant::one ());
}

X86_32_TRANSLATE_2_OP(MOVSB)
{
  x86_32_translate<X86_32_TOKEN(MOVSB)> (data);
  op1->deref ();
  op2->deref ();
}

X86_32_TRANSLATE_0_OP(MOVSW)
{
  s_mov (data, Constant::create (2));
}

X86_32_TRANSLATE_2_OP(MOVSW)
{
  x86_32_translate<X86_32_TOKEN(MOVSW)> (data);
  op1->deref ();
  op2->deref ();
}

X86_32_TRANSLATE_0_OP(MOVSD)
{
  s_mov (data, Constant::create (4));
}

X86_32_TRANSLATE_2_OP(MOVSD)
{
  x86_32_translate<X86_32_TOKEN(MOVSD)> (data);
  op1->deref ();
  op2->deref ();
}

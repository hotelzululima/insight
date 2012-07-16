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

X86_32_TRANSLATE_0_OP(CBW)
{
  data.mc->add_assignment (data.start_ma,
			   data.get_register ("ax"),
			   BinaryApp::create (EXTEND_S, 
					      data.get_register ("al"),
					      Constant::create (16)),
			   data.next_ma);
}

X86_32_TRANSLATE_0_OP(CBTW)
{
  x86_32_translate<X86_32_TOKEN (CBW)> (data);
}

X86_32_TRANSLATE_0_OP(CLC)
{
  x86_32_reset_CF (data.start_ma, data, NULL, &data.next_ma);
}

X86_32_TRANSLATE_0_OP(CLD)
{
  MicrocodeAddress from (data.start_ma);

  x86_32_reset_flag (from, data, "df", &data.next_ma);
}


X86_32_TRANSLATE_1_OP(CLFLUSH)
{
  Log::warningln ("CLFLUSH translated in NOP");
  x86_32_translate<X86_32_TOKEN (NOP)> (data);
  op1->deref ();
}

X86_32_TRANSLATE_0_OP(CLI)
{
  Log::warningln ("CLI translated in NOP");
  x86_32_translate<X86_32_TOKEN (NOP)> (data);
}


X86_32_TRANSLATE_0_OP(CLTS)
{
  Log::warningln ("CLTS translated in NOP");
  x86_32_translate<X86_32_TOKEN (NOP)> (data);
}

X86_32_TRANSLATE_0_OP(CMC)
{
  MicrocodeAddress from = data.start_ma;

  x86_32_assign_CF (from, data, 
		    UnaryApp::create (NOT, data.get_flag ("cf"), 0, 1), 
		    &data.next_ma);
}

X86_32_TRANSLATE_0_OP(CWDE)
{
  data.mc->add_assignment (data.start_ma,
			   data.get_register ("eax"),
			   BinaryApp::create (EXTEND_S, 
					      data.get_register ("ax"),
					      Constant::create (32)),
			   data.next_ma);
}

X86_32_TRANSLATE_0_OP(CWTL)
{
  x86_32_translate<X86_32_TOKEN (CWDE)> (data);
}


X86_32_TRANSLATE_0_OP(CPUID)
{
  Log::warningln ("CPUID translated in NOP");
  x86_32_translate<X86_32_TOKEN (NOP)> (data);
}

X86_32_TRANSLATE_0_OP(CWD)
{
  data.mc->add_assignment (data.start_ma,
			   data.get_register ("dx"),
			   BinaryApp::create (EXTEND_S, 
					      data.get_register ("ax"),
					      Constant::create (32), 16, 16),
			   data.next_ma);  
}

X86_32_TRANSLATE_0_OP(CDQ)
{
  data.mc->add_assignment (data.start_ma,
			   data.get_register ("edx"),
			   BinaryApp::create (EXTEND_S, 
					      data.get_register ("eax"),
					      Constant::create (64), 32, 32),
			   data.next_ma);
}

/*
X86_32_TRANSLATE_0_OP (RDTSC)
{
  Log::warningln ("RDSTC translated in NOP");
  x86_32_translate<X86_32_TOKEN (NOP)> (data);
}
*/


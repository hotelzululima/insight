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

#include "Architecture_X86_64.hh"

#include <kernel/Expressions.hh>

Architecture_X86_64::Architecture_X86_64() :
  Architecture (X86_64, LittleEndian, 64, 64)
{
  /* Changing default bitvector size to 64 */
  Expr::set_bv_default_size(64);

  /* Setting regular registers */
  add_register("rax", 64);
  add_register("rbx", 64);
  add_register("rcx", 64);
  add_register("rdx", 64);

  add_register("rip", 64);
  add_register("rbp", 64);
  add_register("rsp", 64);

  add_register("rsi", 64);
  add_register("rdi", 64);

  add_register("r8",  64);
  add_register("r9",  64);
  add_register("r10", 64);
  add_register("r11", 64);
  add_register("r12", 64);
  add_register("r13", 64);
  add_register("r14", 64);
  add_register("r15", 64);

  add_register("cs", 16);
  add_register("ds", 16);
  add_register("es", 16);
  add_register("fs", 16);
  add_register("gs", 16);
  add_register("ss", 16);

  /* Setting alias registers */
  add_register_alias("eax", "rax", 32, 0);
  add_register_alias("ebx", "rbx", 32, 0);
  add_register_alias("ecx", "rcx", 32, 0);
  add_register_alias("edx", "rdx", 32, 0);

  add_register_alias("eip", "rip", 32, 0);
  add_register_alias("ebp", "rbp", 32, 0);
  add_register_alias("esp", "rsp", 32, 0);

  add_register_alias("esi", "rsi", 32, 0);
  add_register_alias("edi", "rdi", 32, 0);

  add_register_alias("r8d",   "r8", 32, 0);
  add_register_alias("r9d",   "r9", 32, 0);
  add_register_alias("r10d", "r10", 32, 0);
  add_register_alias("r11d", "r11", 32, 0);
  add_register_alias("r12d", "r12", 32, 0);
  add_register_alias("r13d", "r13", 32, 0);
  add_register_alias("r14d", "r14", 32, 0);
  add_register_alias("r15d", "r15", 32, 0);

  add_register_alias("r8w",   "r8", 16, 0);
  add_register_alias("r9w",   "r9", 16, 0);
  add_register_alias("r10w", "r10", 16, 0);
  add_register_alias("r11w", "r11", 16, 0);
  add_register_alias("r12w", "r12", 16, 0);
  add_register_alias("r13w", "r13", 16, 0);
  add_register_alias("r14w", "r14", 16, 0);
  add_register_alias("r15w", "r15", 16, 0);

  add_register_alias("r8b",   "r8", 8, 0);
  add_register_alias("r9b",   "r9", 8, 0);
  add_register_alias("r10b", "r10", 8, 0);
  add_register_alias("r11b", "r11", 8, 0);
  add_register_alias("r12b", "r12", 8, 0);
  add_register_alias("r13b", "r13", 8, 0);
  add_register_alias("r14b", "r14", 8, 0);
  add_register_alias("r15b", "r15", 8, 0);

  add_register_alias("ax", "rax", 16, 0);
  add_register_alias("al", "rax", 8, 0);
  add_register_alias("ah", "rax", 8, 8);

  add_register_alias("bx", "rbx", 16, 0);
  add_register_alias("bl", "rbx", 8, 0);
  add_register_alias("bh", "rbx", 8, 8);

  add_register_alias("cx", "rcx", 16, 0);
  add_register_alias("cl", "rcx", 8, 0);
  add_register_alias("ch", "rcx", 8, 8);

  add_register_alias("dx", "rdx", 16, 0);
  add_register_alias("dl", "rdx", 8, 0);
  add_register_alias("dh", "rdx", 8, 8);

  add_register_alias("bp",  "rbp", 16, 0);
  add_register_alias("bpl", "rbp",  8, 0);
  add_register_alias("sp",  "rsp", 16, 0);
  add_register_alias("spl", "rsp",  8, 0);

  add_register_alias("si",  "rsi", 16, 0);
  add_register_alias("sil", "rsi",  8, 0);
  add_register_alias("di",  "rdi", 16, 0);
  add_register_alias("dil", "rdi",  8, 0);

#ifdef X86_64_USE_RFLAGS
  add_register("rflags", 64);
  add_register_alias("cf", "rflags", 1, 0);
  add_register_alias("pf", "rflags", 1, 2);
  add_register_alias("af", "rflags", 1, 4);
  add_register_alias("zf", "rflags", 1, 6);
  add_register_alias("sf", "rflags", 1, 7);
  add_register_alias("tf", "rflags", 1, 8);
  add_register_alias("if", "rflags", 1, 9);
  add_register_alias("df", "rflags", 1, 10);
  add_register_alias("of", "rflags", 1, 11);
  add_register_alias("iopl", "rflags", 2, 12);
  add_register_alias("nt", "rflags", 1, 14);
  add_register_alias("rf", "rflags", 1, 16);
  add_register_alias("vm", "rflags", 1, 17);
  add_register_alias("ac", "rflags", 1, 18);
  add_register_alias("vif", "rflags", 1, 19);
  add_register_alias("vip", "rflags", 1, 20);
  add_register_alias("id", "rflags", 1, 21);
#else
  add_register("cf", 1);
  add_register("pf", 1);
  add_register("af", 1);
  add_register("zf", 1);
  add_register("sf", 1);
  add_register("tf", 1);
  add_register("if", 1);
  add_register("df", 1);
  add_register("of", 1);
  add_register("iopl", 2);
  add_register("nt", 1);
  add_register("rf", 1);
  add_register("vm", 1);
  add_register("ac", 1);
  add_register("vif", 1);
  add_register("vip", 1);
  add_register("id", 1);
#endif
}

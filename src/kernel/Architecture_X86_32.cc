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

#include "Architecture_X86_32.hh"

Architecture_X86_32::Architecture_X86_32() : Architecture()
{
  this->  processor = X86_32;
  this->endianness = LittleEndian;

  /* Setting regular registers */
  add_register("eax", 32);
  add_register("ebx", 32);
  add_register("ecx", 32);
  add_register("edx", 32);

  add_register("ebp", 32);
  add_register("esp", 32);

  add_register("esi", 32);
  add_register("edi", 32);

  add_register("cs", 16);
  add_register("ds", 16);
  add_register("es", 16);
  add_register("fs", 16);
  add_register("gs", 16);
  add_register("ss", 16);

  add_register("eflags", 32);

  /* Setting alias registers */
  add_register_alias("ax", "eax", 16, 0);
  add_register_alias("al", "eax", 8, 0);
  add_register_alias("ah", "eax", 8, 8);

  add_register_alias("bx", "ebx", 16, 0);
  add_register_alias("bl", "ebx", 8, 0);
  add_register_alias("bh", "ebx", 8, 8);

  add_register_alias("cx", "ecx", 16, 0);
  add_register_alias("cl", "ecx", 8, 0);
  add_register_alias("ch", "ecx", 8, 8);

  add_register_alias("dx", "edx", 16, 0);
  add_register_alias("dl", "edx", 8, 0);
  add_register_alias("dh", "edx", 8, 8);

  add_register_alias("bp", "ebp", 16, 0);
  add_register_alias("sp", "esp", 16, 0);

  add_register_alias("si", "esi", 16, 0);
  add_register_alias("di", "edi", 16, 0);

  add_register_alias("cf", "eflags", 1, 0);
  add_register_alias("pf", "eflags", 1, 2);
  add_register_alias("af", "eflags", 1, 4);
  add_register_alias("zf", "eflags", 1, 6);
  add_register_alias("sf", "eflags", 1, 7);
  add_register_alias("tf", "eflags", 1, 8);
  add_register_alias("if", "eflags", 1, 9);
  add_register_alias("df", "eflags", 1, 10);
  add_register_alias("of", "eflags", 1, 11);
  add_register_alias("iopl", "eflags", 2, 12);
  add_register_alias("nt", "eflags", 1, 14);
  add_register_alias("rf", "eflags", 1, 16);
  add_register_alias("vm", "eflags", 1, 17);
  add_register_alias("ac", "eflags", 1, 18);
  add_register_alias("vif", "eflags", 1, 19);
  add_register_alias("vip", "eflags", 1, 20);
  add_register_alias("id", "eflags", 1, 21);
}

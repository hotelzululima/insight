/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
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

#include <decoders/binutils/msp430/msp430_instr.hh>

MSP430_TRANSLATE_1_OP(CALL) {
  int bytes = data.is_extended? 4 : 2;
  LValue *sp = data.get_register(MSP430_REG_SP);
  bool is_immediate = op1->is_Constant();
  bool has_postinc = data.has_postincrements();
  MicrocodeAddress static_dest = dynamic_cast<Constant *>(op1)->get_val();
  MicrocodeAddress dest = is_immediate && !has_postinc?
    static_dest : data.start_ma + 2;

  data.mc->add_assignment(data.start_ma, sp->ref(),
			  BinaryApp::create(BV_OP_SUB, sp->ref(),
					    Constant::create(bytes,
							     0, MSP430_SIZE_A),
					    0, MSP430_SIZE_A),
			  data.start_ma + 1, NULL);

  data.start_ma = data.start_ma + 1;

  data.mc->add_assignment(data.start_ma + 1, MemCell::create(sp,
							     0, bytes * 8),
			  Constant::create(data.next_ma.getGlobal(),
					   0, bytes * 8),
			  dest, NULL);
  if (has_postinc) {
    data.start_ma = data.start_ma + 1;

    if (is_immediate)
      data.next_ma = static_dest;

    data.finalize_postincrements(!is_immediate);
  }

  if (!is_immediate) {
    data.mc->add_jump(data.start_ma, op1, NULL);
  }

  op1->deref();
}

static void
s_translate_mov(msp430::parser_data &data, Expr *source, Expr *dest) {
  Expr *res = msp430_trim_source_operand(data, source);
  MicrocodeAddress next =
    data.has_postincrements()? data.start_ma + 1 : data.next_ma;

  data.mc->add_assignment(data.start_ma,
			  dynamic_cast<LValue *>(dest),
			  msp430_stretch_expr_to_dest_size(dest, res),
			  next, NULL);
  if (data.has_postincrements()) {
    data.start_ma = data.start_ma + 1;
    data.finalize_postincrements(false);
  }
}

MSP430_TRANSLATE_1_OP(CLR) {
  s_translate_mov(data, Constant::zero(data.operand_size), op1);
}

MSP430_TRANSLATE_2_OP(MOV) {
  s_translate_mov(data, op1, op2);
}

MSP430_TRANSLATE_2_OP(MOVA) {
  s_translate_mov(data, op1, op2);
}

MSP430_TRANSLATE_2_OP(MOVX) {
  s_translate_mov(data, op1, op2);
}

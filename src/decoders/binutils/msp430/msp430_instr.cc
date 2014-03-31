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
  int bytes = data.operand_size == MSP430_SIZE_A? 4 : 2;
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

static Expr *
s_operation_semantics(msp430::parser_data &data, BinaryOp op,
		      Expr *source, Expr *dest) {
  source = msp430_trim_source_operand(data, source);
  dest = msp430_trim_source_operand(data, dest);
  return BinaryApp::create(op, source, dest, 0, data.operand_size);
}

MSP430_TRANSLATE_2_OP(AND) {
  s_translate_mov(data,
		  s_operation_semantics(data, BV_OP_AND, op1, op2->ref()),
		  op2);
}

MSP430_TRANSLATE_2_OP(BIC) {
  s_translate_mov(data,
		  s_operation_semantics(data, BV_OP_AND,
					UnaryApp::create(BV_OP_NOT, op1,
							 0,
							 op1->get_bv_size()),
					op2->ref()),
		  op2);
}

MSP430_TRANSLATE_2_OP(BIS) {
  s_translate_mov(data,
		  s_operation_semantics(data, BV_OP_OR, op1, op2->ref()),
		  op2);
}

MSP430_TRANSLATE_1_OP(CLR) {
  s_translate_mov(data, Constant::zero(data.operand_size), op1);
}

MSP430_TRANSLATE_2_OP(MOV) {
  s_translate_mov(data, op1, op2);
}

MSP430_TRANSLATE_1_OP(PUSH) {
  RegisterExpr *sp = data.get_register(MSP430_REG_SP);
  int size = data.operand_size == MSP430_SIZE_A? 4 : data.operand_size / 8;

  data.mc->add_assignment(data.start_ma, sp->ref(),
			  BinaryApp::create(BV_OP_SUB, sp->ref(),
					    Constant::create(size, 0,
							     MSP430_SIZE_A),
					    0, MSP430_SIZE_A));
  Expr *source = msp430_trim_source_operand(data, op1);
  Expr *dest = MemCell::create(sp, 0, size * 8);
  source = msp430_stretch_expr_to_dest_size(dest, source);
  s_translate_mov(data, source, dest);
}

MSP430_TRANSLATE_1_OP(POP) {
  RegisterExpr *sp = data.get_register(MSP430_REG_SP);
  int size = data.operand_size == MSP430_SIZE_A? 4 : data.operand_size / 8;

  data.add_postincrement((RegisterExpr *) sp->ref());

  Expr *source = msp430_trim_source_operand(data, op1);
  Expr *dest = MemCell::create(sp, 0, size * 8);
  source = msp430_stretch_expr_to_dest_size(dest, source);
  s_translate_mov(data, source, dest);
}

/*** Static jumps ***/

static void
s_translate_static_jump(msp430::parser_data &data, Expr *op, Expr *guard,
			bool guard_jumps) {
  MemCell *memcell = dynamic_cast<MemCell *>(op);
  Constant *constant = dynamic_cast<Constant *>(memcell->get_addr());

  if (guard != NULL) {
    Expr *not_guard = UnaryApp::create(BV_OP_NOT, guard->ref(), 0, 1);

    data.mc->add_skip(data.start_ma, data.next_ma,
		      guard_jumps? not_guard : guard);

    if (!guard_jumps)
      guard = not_guard;
  }

  data.mc->add_skip(data.start_ma, MicrocodeAddress(constant->get_val()),
		    guard);
  op->deref();
}

MSP430_TRANSLATE_1_OP(JMP) {
  s_translate_static_jump(data, op1, NULL, false);
}

static Expr *
s_compute_cc_flag(msp430::parser_data &data, int bit) {
  Expr *sr = data.get_register(MSP430_REG_SR);
  Expr *ret = sr->extract_bit_vector(bit, 1);

  sr->deref();

  return ret;
}

MSP430_TRANSLATE_1_OP(JC) {
  s_translate_static_jump(data, op1,
			  s_compute_cc_flag(data, MSP430_FLAG_C), true);
}

MSP430_TRANSLATE_1_OP(JNC) {
  s_translate_static_jump(data, op1,
			  s_compute_cc_flag(data, MSP430_FLAG_C), false);
}

MSP430_TRANSLATE_1_OP(JZ) {
  s_translate_static_jump(data, op1,
			  s_compute_cc_flag(data, MSP430_FLAG_Z), true);
}

MSP430_TRANSLATE_1_OP(JNZ) {
  s_translate_static_jump(data, op1,
			  s_compute_cc_flag(data, MSP430_FLAG_Z), false);
}

MSP430_TRANSLATE_1_OP(JN) {
  s_translate_static_jump(data, op1,
			  s_compute_cc_flag(data, MSP430_FLAG_N), true);
}

MSP430_TRANSLATE_1_OP(JGE) {
  s_translate_static_jump(data, op1,
			  BinaryApp::create(BV_OP_XOR,
					    s_compute_cc_flag(data,
							      MSP430_FLAG_N),
					    s_compute_cc_flag(data,
							      MSP430_FLAG_V),
					    0, 1),
			  false);
}

MSP430_TRANSLATE_1_OP(JL) {
  s_translate_static_jump(data, op1,
			  BinaryApp::create(BV_OP_XOR,
					    s_compute_cc_flag(data,
							      MSP430_FLAG_N),
					    s_compute_cc_flag(data,
							      MSP430_FLAG_V),
					    0, 1),
			  true);
}

/*** Misc ***/

MSP430_TRANSLATE_0_OP(NOP) {
  data.mc->add_skip(data.start_ma, data.next_ma);
}

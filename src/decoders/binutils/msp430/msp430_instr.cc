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

static LValue *
s_flag_lvalue(msp430::parser_data &data, int bit) {
  LValue *sr = data.get_register(MSP430_REG_SR);
  LValue *ret = (LValue *) sr->extract_bit_vector(bit, 1);

  sr->deref();

  return ret;
}

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
s_translate_mov(msp430::parser_data &data, Expr *source, Expr *dest,
		bool leave_open) {
  Expr *res = msp430_trim_source_operand(data, source);
  MicrocodeAddress next = (leave_open || data.has_postincrements())?
    data.start_ma + 1 : data.next_ma;

  data.mc->add_assignment(data.start_ma,
			  dynamic_cast<LValue *>(dest),
			  msp430_stretch_expr_to_dest_size(dest, res),
			  next, NULL);
  data.start_ma = data.start_ma + 1;

  if (!leave_open && data.has_postincrements())
    data.finalize_postincrements(false);
}

static Expr *
s_operation_semantics(msp430::parser_data &data, BinaryOp op,
		      Expr *op1, Expr *op2, int dest_size) {
  op1 = msp430_trim_source_operand(data, op1);
  op2 = msp430_trim_source_operand(data, op2);
  return BinaryApp::create(op, op2, op1, 0, dest_size);
}

static void
s_update_flag(msp430::parser_data &data, Expr *val, LValue *flag,
	      bool leave_open) {
  MicrocodeAddress next = (leave_open || data.has_postincrements())?
    data.start_ma + 1 : data.next_ma;

  data.mc->add_assignment(data.start_ma, flag, val, next, NULL);
  data.start_ma = data.start_ma + 1;

  if (!leave_open && data.has_postincrements())
    data.finalize_postincrements(false);
}

/** pflags is the set of flags we should NOT update */
static void
s_translate_arithmetic_op(msp430::parser_data &data, BinaryOp op,
			  Expr *source, Expr *dest, int pflags,
			  bool leave_open, bool discard_result = false) {
  bool update_c = !(pflags & (1 << MSP430_FLAG_C));
  bool update_n = !(pflags & (1 << MSP430_FLAG_N));
  bool update_v = !(pflags & (1 << MSP430_FLAG_V));
  bool update_z = !(pflags & (1 << MSP430_FLAG_Z));
  int nupdates = update_c + update_n + update_v + update_z;
  int nupleft = nupdates;
  int size = data.operand_size;
  Expr *tmpr;

  if (update_c) {
    size++;
    tmpr = data.get_tmp_register(size);
  }
  else
    tmpr = dest->ref();

  s_translate_mov(data,
		  s_operation_semantics(data, op, source->ref(), tmpr->ref(),
					size),
		  tmpr->ref(),
		  leave_open || nupdates > 0);

  if (update_c) {
    if (!discard_result)
      s_translate_mov(data, tmpr->ref(), dest->ref(), false);

    s_update_flag(data, tmpr->extract_bit_vector(size - 1, 1),
		  s_flag_lvalue(data, MSP430_FLAG_C),
		  leave_open || nupleft > 1);

    if (discard_result) {
      dest->deref();
      dest = tmpr->extract_bit_vector(0, size - 1);
    }

    nupleft--;
  }

  if (update_n) {
    s_update_flag(data, dest->extract_bit_vector(dest->get_bv_size() - 1, 1),
		  s_flag_lvalue(data, MSP430_FLAG_N),
		  leave_open || nupleft > 1);
    nupleft--;
  }

  if (update_v) {
    s_update_flag(data, Constant::zero(1),
		  s_flag_lvalue(data, MSP430_FLAG_V),
		  leave_open || nupleft > 1);
    nupleft--;
  }

  if (update_z) {
    s_update_flag(data, BinaryApp::create(BV_OP_EQ, dest->ref(),
					  Constant::zero(dest->get_bv_size()),
					  0, 1),
		  s_flag_lvalue(data, MSP430_FLAG_Z),
		  leave_open || nupleft > 1);
    nupleft--;
  }

  tmpr->deref();
  source->deref();
  dest->deref();
}

MSP430_TRANSLATE_2_OP(ADD) {
  s_translate_arithmetic_op(data, BV_OP_ADD, op1, op2, (1 << MSP430_FLAG_V),
			    true);
  /* XXX Compute overflow flag */
  s_update_flag(data, Constant::zero(1),
		s_flag_lvalue(data, MSP430_FLAG_V), false);
}

MSP430_TRANSLATE_2_OP(AND) {
  s_translate_arithmetic_op(data, BV_OP_AND, op1, op2, (1 << MSP430_FLAG_C),
			    true);
  s_update_flag(data, UnaryApp::create(BV_OP_NOT,
				       s_flag_lvalue(data, MSP430_FLAG_Z),
				       0, 1),
		s_flag_lvalue(data, MSP430_FLAG_C), false);
}

MSP430_TRANSLATE_2_OP(BIC) {
  s_translate_arithmetic_op(data, BV_OP_AND,
			    UnaryApp::create(BV_OP_NOT, op1,
					     0, op1->get_bv_size()),
			    op2,
			    (1 << MSP430_FLAG_C) |
			    (1 << MSP430_FLAG_N) |
			    (1 << MSP430_FLAG_V) |
			    (1 << MSP430_FLAG_Z),
			    false);
}

MSP430_TRANSLATE_2_OP(BIS) {
  s_translate_arithmetic_op(data, BV_OP_OR, op1, op2,
			    (1 << MSP430_FLAG_C) |
			    (1 << MSP430_FLAG_N) |
			    (1 << MSP430_FLAG_V) |
			    (1 << MSP430_FLAG_Z),
			    false);
}

MSP430_TRANSLATE_2_OP(CMP) {
  s_translate_arithmetic_op(data, BV_OP_SUB, op1, op2, (1 << MSP430_FLAG_V),
			    true, true);
  /* XXX Compute overflow flag */
  s_update_flag(data, Constant::zero(1),
		s_flag_lvalue(data, MSP430_FLAG_V), false);
}

MSP430_TRANSLATE_1_OP(DEC) {
  msp430_translate<MSP430_TOKEN(SUB)>(data,
				      Constant::create(1, 0, data.operand_size),
				      op1);
}

MSP430_TRANSLATE_1_OP(DECD) {
  msp430_translate<MSP430_TOKEN(SUB)>(data,
				      Constant::create(2, 0, data.operand_size),
				      op1);
}

MSP430_TRANSLATE_1_OP(INC) {
  msp430_translate<MSP430_TOKEN(ADD)>(data,
				      Constant::create(1, 0, data.operand_size),
				      op1);
}

MSP430_TRANSLATE_1_OP(INCD) {
  msp430_translate<MSP430_TOKEN(ADD)>(data,
				      Constant::create(2, 0, data.operand_size),
				      op1);
}

MSP430_TRANSLATE_2_OP(SUB) {
  s_translate_arithmetic_op(data, BV_OP_SUB, op1, op2, (1 << MSP430_FLAG_V),
			    true);
  /* XXX Compute overflow flag */
  s_update_flag(data, Constant::zero(1),
		s_flag_lvalue(data, MSP430_FLAG_V), false);
}


MSP430_TRANSLATE_1_OP(CLR) {
  s_translate_mov(data, Constant::zero(data.operand_size), op1, false);
}

MSP430_TRANSLATE_2_OP(MOV) {
  s_translate_mov(data, op1, op2, false);
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
  s_translate_mov(data, source, dest, false);
}

MSP430_TRANSLATE_1_OP(POP) {
  RegisterExpr *sp = data.get_register(MSP430_REG_SP);
  int size = data.operand_size == MSP430_SIZE_A? 4 : data.operand_size / 8;

  data.add_postincrement((RegisterExpr *) sp->ref());

  Expr *source = msp430_trim_source_operand(data, op1);
  Expr *dest = MemCell::create(sp, 0, size * 8);
  source = msp430_stretch_expr_to_dest_size(dest, source);
  s_translate_mov(data, source, dest, false);
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

MSP430_TRANSLATE_1_OP(JC) {
  s_translate_static_jump(data, op1,
			  s_flag_lvalue(data, MSP430_FLAG_C), true);
}

MSP430_TRANSLATE_1_OP(JNC) {
  s_translate_static_jump(data, op1,
			  s_flag_lvalue(data, MSP430_FLAG_C), false);
}

MSP430_TRANSLATE_1_OP(JZ) {
  s_translate_static_jump(data, op1,
			  s_flag_lvalue(data, MSP430_FLAG_Z), true);
}

MSP430_TRANSLATE_1_OP(JNZ) {
  s_translate_static_jump(data, op1,
			  s_flag_lvalue(data, MSP430_FLAG_Z), false);
}

MSP430_TRANSLATE_1_OP(JN) {
  s_translate_static_jump(data, op1,
			  s_flag_lvalue(data, MSP430_FLAG_N), true);
}

MSP430_TRANSLATE_1_OP(JGE) {
  s_translate_static_jump(data, op1,
			  BinaryApp::create(BV_OP_XOR,
					    s_flag_lvalue(data, MSP430_FLAG_N),
					    s_flag_lvalue(data, MSP430_FLAG_V),
					    0, 1),
			  false);
}

MSP430_TRANSLATE_1_OP(JL) {
  s_translate_static_jump(data, op1,
			  BinaryApp::create(BV_OP_XOR,
					    s_flag_lvalue(data, MSP430_FLAG_N),
					    s_flag_lvalue(data, MSP430_FLAG_V),
					    0, 1),
			  true);
}

/*** Misc ***/

MSP430_TRANSLATE_0_OP(NOP) {
  data.mc->add_skip(data.start_ma, data.next_ma);
}

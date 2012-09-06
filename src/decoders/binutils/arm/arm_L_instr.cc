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

#include "arm_translation_functions.hh"
#include "utils/tools.hh"

using namespace std;

//1st
template<> void arm_translate<ARM_TOKEN(LDR)> (arm::parser_data &data,
    bool is_D_suffix, bool is_H_suffix, bool is_B_suffix, bool,
    std::string* cond, Expr *reg, Expr *mem)

{
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (is_D_suffix) {
    MemCell *src1 = (MemCell *) mem;
    Expr* address = src1->get_addr();
    MemCell* src2 = MemCell::create(BinaryApp::create (BV_OP_ADD, address->ref(), 4), src1->get_bv_offset (), src1->get_bv_size ());

    LValue* reg2 = data.get_adjacent_register (reg);

    data.mc->add_assignment(data.start_ma, (LValue*) reg, src1);
    data.mc->add_assignment(data.start_ma, (LValue*) reg2, src2, data.next_ma,
			    guard);

  } else if (is_H_suffix) {
    Expr* half_mem = TernaryApp::create (BV_OP_EXTRACT, mem, Constant::create(0, 0, BV_DEFAULT_SIZE),
        Constant::create(16, 0, BV_DEFAULT_SIZE));
    Expr *half_mem_zero_extend = 
      Expr::createExtend (BV_OP_EXTEND_U, half_mem, 32);

    data.mc->add_assignment(data.start_ma, (LValue*) reg, half_mem_zero_extend,
        data.next_ma, guard);
  } else if (is_B_suffix) {

    Expr* byte_mem = TernaryApp::create (BV_OP_EXTRACT, mem, Constant::create(0, 0, BV_DEFAULT_SIZE),
        Constant::create(8, 0, BV_DEFAULT_SIZE));

    Expr *byte_mem_zero_extend = 
      Expr::createExtend (BV_OP_EXTEND_U, byte_mem, 32);

    data.mc->add_assignment(data.start_ma, (LValue*) reg, byte_mem_zero_extend,
        data.next_ma, guard);
  } else {

    data.mc->add_assignment(data.start_ma, (LValue*) reg, mem, data.next_ma,
        guard);
  }
}

//2nd
template<> void 
arm_translate<ARM_TOKEN(LDR)> (arm::parser_data &data,
			       bool is_D_suffix, bool is_H_suffix, 
			       bool is_B_suffix, bool /*is_T_suffix */,
    std::string* cond, Expr *reg, Expr *mem, bool is_NOT_suffix)

{
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (is_D_suffix) {
    MemCell *src1 = (MemCell *) mem;
    Expr* address = src1->get_addr();
    MemCell* src2 = 
      MemCell::create(BinaryApp::create (BV_OP_ADD, address->ref(), 4),
		      src1->get_bv_offset (), src1->get_bv_size ());

    LValue* reg2 = data.get_adjacent_register (reg);

    data.mc->add_assignment(data.start_ma, (LValue*) reg, src1);

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, reg2, src2);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, reg2, src2, data.next_ma, guard);

  } else if (is_H_suffix) {
    Expr* half_mem = 
      TernaryApp::create (BV_OP_EXTRACT, mem, Constant::create(0, 0, BV_DEFAULT_SIZE),
        Constant::create(16, 0, BV_DEFAULT_SIZE));
    Expr *half_mem_zero_extend = 
      Expr::createExtend (BV_OP_EXTEND_U, half_mem, 32);

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, (LValue*) reg,
          half_mem_zero_extend);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, (LValue*) reg,
          half_mem_zero_extend, data.next_ma, guard);

  } else if (is_B_suffix) {
    Expr* byte_mem = 
      TernaryApp::create (BV_OP_EXTRACT, mem, Constant::create(0, 0, BV_DEFAULT_SIZE),
			  Constant::create(8, 0, BV_DEFAULT_SIZE));
    Expr *byte_mem_zero_extend = 
      Expr::createExtend (BV_OP_EXTEND_U, byte_mem, 32);

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, (LValue*) reg,
          byte_mem_zero_extend);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, (LValue*) reg,
          byte_mem_zero_extend, data.next_ma, guard);

  } else {

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, (LValue*) reg, mem);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, (LValue*) reg, mem, data.next_ma,
          guard);
  }
}

//3rd
template<> void 
arm_translate<ARM_TOKEN(LDR)> (arm::parser_data &data,
			       bool is_D_suffix, bool is_H_suffix, 
			       bool is_B_suffix, bool /*is_T_suffix*/,
			       std::string* cond, Expr *reg, Expr *mem, 
			       Expr* offset)

{
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (is_D_suffix) {
    MemCell *src1 = (MemCell *) mem;
    Expr* address = src1->get_addr();
    MemCell* src2 = 
      MemCell::create(BinaryApp::create (BV_OP_ADD, address->ref(), 4),
		      src1->get_bv_offset (), src1->get_bv_size ());

    LValue* reg2 = data.get_adjacent_register (reg);

    data.mc->add_assignment(data.start_ma, (LValue*) reg, src1);
    data.mc->add_assignment(data.start_ma, reg2, src2);

    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
        BinaryApp::create (BV_OP_ADD, mem_reg->ref(), offset), data.next_ma, guard);

  } else if (is_H_suffix) {

    Expr* half_mem = TernaryApp::create (BV_OP_EXTRACT, mem, 
					 Constant::create(0, 0, BV_DEFAULT_SIZE),
        Constant::create(16, 0, BV_DEFAULT_SIZE));
    Expr *half_mem_zero_extend = 
      Expr::createExtend (BV_OP_EXTEND_U, half_mem, 32);

    data.mc->add_assignment(data.start_ma, (LValue*) reg, half_mem_zero_extend);

    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
        BinaryApp::create (BV_OP_ADD, mem_reg->ref(), offset), data.next_ma, 
			    guard);

  } else if (is_B_suffix) {
    Expr* byte_mem = TernaryApp::create (BV_OP_EXTRACT, mem, 
					 Constant::create(0, 0, BV_DEFAULT_SIZE),
					 Constant::create(8, 0, BV_DEFAULT_SIZE));
    Expr *byte_mem_zero_extend = 
      Expr::createExtend (BV_OP_EXTEND_U, byte_mem, 32);

    data.mc->add_assignment(data.start_ma, (LValue*) reg, byte_mem_zero_extend);

    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
			    BinaryApp::create (BV_OP_ADD, mem_reg->ref(), 
					       offset), data.next_ma, 
			    guard);
  } else {
    data.mc->add_assignment(data.start_ma, (LValue*) reg, mem);
    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
			    BinaryApp::create (BV_OP_ADD, mem_reg->ref(), 
					       offset), data.next_ma, 
			    guard);
  }
}


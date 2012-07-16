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
template<> void 
arm_translate<ARM_TOKEN(STR)> (arm::parser_data &data,
			       bool is_D_suffix, bool is_H_suffix, 
			       bool is_B_suffix, bool /*is_T_suffix*/,
			       std::string* cond, Expr *reg, Expr *mem)

{
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (is_D_suffix) {
    MemCell *dst1 = (MemCell *) mem;
    Expr* address = dst1->get_addr();
    MemCell* dst2 = MemCell::create(BinaryApp::create(ADD, address->ref(), 4));

    LValue* reg2 = data.get_adjacent_register (reg);

    data.mc->add_assignment(data.start_ma, dst1, reg);
    data.mc->add_assignment(data.start_ma, dst2, reg2, data.next_ma, guard);

  } else if (is_H_suffix) {
    Expr* half_reg = TernaryApp::create(EXTRACT, reg, Constant::create(0),
        Constant::create(16));
    data.mc->add_assignment(data.start_ma, (LValue*) mem, half_reg,
        data.next_ma, guard);
  } else if (is_B_suffix) {

    Expr* byte_reg = TernaryApp::create(EXTRACT, reg, Constant::create(0),
        Constant::create(8));
    data.mc->add_assignment(data.start_ma, (LValue*) mem, byte_reg,
        data.next_ma, guard);
  } else {

    data.mc->add_assignment(data.start_ma, (LValue*) mem, reg, data.next_ma,
        guard);
  }
}

//2nd
template<> void 
arm_translate<ARM_TOKEN(STR)> (arm::parser_data &data,
			       bool is_D_suffix, bool is_H_suffix, 
			       bool is_B_suffix, bool /*is_T_suffix*/,
			       std::string* cond, Expr *reg, Expr *mem, 
			       bool is_NOT_suffix)

{
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (is_D_suffix) {
    MemCell *dst1 = (MemCell *) mem;
    Expr* address = dst1->get_addr();
    MemCell* dst2 = MemCell::create(BinaryApp::create(ADD, address->ref(), 4));

    LValue* reg2 = data.get_adjacent_register (reg);

    data.mc->add_assignment(data.start_ma, dst1, reg);

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, dst2, reg2);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, dst2, reg2, data.next_ma, guard);

  } else if (is_H_suffix) {
    Expr* half_reg = TernaryApp::create(EXTRACT, reg, Constant::create(0),
        Constant::create(16));

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, (LValue*) mem, half_reg);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, (LValue*) mem, half_reg,
          data.next_ma, guard);

  } else if (is_B_suffix) {
    Expr* byte_reg = TernaryApp::create(EXTRACT, reg, Constant::create(0),
        Constant::create(8));

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, (LValue*) mem, byte_reg);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, (LValue*) mem, byte_reg,
          data.next_ma, guard);

  } else {

    if (is_NOT_suffix) {
      data.mc->add_assignment(data.start_ma, (LValue*) mem, reg);

      Expr* mem_reg = ((BinaryApp*) ((BinaryApp*) mem)->get_arg1())->get_arg1();
      data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
          ((BinaryApp*) mem)->get_arg1()->ref(), data.next_ma, guard);

    } else
      data.mc->add_assignment(data.start_ma, (LValue*) mem, reg, data.next_ma,
          guard);
  }
}

//3rd
template<> void 
arm_translate<ARM_TOKEN(STR)> (arm::parser_data &data,
			       bool is_D_suffix, bool is_H_suffix, 
			       bool is_B_suffix, bool /*is_T_suffix*/,
			       std::string* cond, Expr *reg, Expr *mem, 
			       Expr* offset)

{
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (is_D_suffix) {
    MemCell *dst1 = (MemCell *) mem;
    Expr* address = dst1->get_addr();
    MemCell* dst2 = MemCell::create(BinaryApp::create(ADD, address->ref(), 4));

    LValue* reg2 = data.get_adjacent_register (reg);

    data.mc->add_assignment(data.start_ma, dst1, reg);
    data.mc->add_assignment(data.start_ma, dst2, reg2);

    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
        BinaryApp::create(ADD, mem_reg->ref(), offset), data.next_ma, guard);

  } else if (is_H_suffix) {

    Expr* half_reg = TernaryApp::create(EXTRACT, reg, Constant::create(0),
        Constant::create(16));
    data.mc->add_assignment(data.start_ma, (LValue*) mem, half_reg);

    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
        BinaryApp::create(ADD, mem_reg->ref(), offset), data.next_ma, guard);

  } else if (is_B_suffix) {
    Expr* byte_reg = TernaryApp::create(EXTRACT, reg, Constant::create(0),
        Constant::create(8));
    data.mc->add_assignment(data.start_ma, (LValue*) mem, byte_reg);

    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
        BinaryApp::create(ADD, mem_reg->ref(), offset), data.next_ma, guard);
  } else {
    data.mc->add_assignment(data.start_ma, (LValue*) mem, reg);

    Expr* mem_reg = ((MemCell*) mem)->get_addr();
    data.mc->add_assignment(data.start_ma, (LValue*) mem_reg->ref(),
        BinaryApp::create(ADD, mem_reg->ref(), offset), data.next_ma, guard);
  }
}


template<> void arm_translate<ARM_TOKEN(SUB)> (arm::parser_data &data,
    bool is_S_suffix, std::string* cond, Expr *op1, Expr *op2, Expr *op3)
{
  LValue *dst = (LValue *) op1;

  BinaryApp* src = BinaryApp::create(SUB, op2, op3);

  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (guard != NULL)
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);

  if (is_S_suffix)
    update_flags(data, guard, src, SUB_INS);
}

template<> void 
arm_translate<ARM_TOKEN(SUB8)> (arm::parser_data &data,
				std::string* /*prefix*/, std::string* cond, 
				Expr *op1, Expr *op2, Expr *op3)
{
  LValue *dst = (LValue *) op1;

  Expr* guard = data.arm_compute_cond_expr(*cond);

  Expr* first_operand = op2;
  Expr* second_operand = op3;
  Expr* first_operand_1 = TernaryApp::create(EXTRACT, first_operand,
      Constant::create(0), Constant::create(8));
  Expr* first_operand_2 = TernaryApp::create(EXTRACT, first_operand->ref(),
      Constant::create(8), Constant::create(8));
  Expr* first_operand_3 = TernaryApp::create(EXTRACT, first_operand->ref(),
      Constant::create(16), Constant::create(8));
  Expr* first_operand_4 = TernaryApp::create(EXTRACT, first_operand->ref(),
      Constant::create(24), Constant::create(8));

  Expr* second_operand_1 = TernaryApp::create(EXTRACT, second_operand,
      Constant::create(0), Constant::create(8));
  Expr* second_operand_2 = TernaryApp::create(EXTRACT, second_operand->ref(),
      Constant::create(8), Constant::create(8));
  Expr* second_operand_3 = TernaryApp::create(EXTRACT, second_operand->ref(),
      Constant::create(16), Constant::create(8));
  Expr* second_operand_4 = TernaryApp::create(EXTRACT, second_operand->ref(),
      Constant::create(24), Constant::create(8));

  Expr* add_result_1 =
      BinaryApp::create(SUB, first_operand_1, second_operand_1);
  Expr* add_result_2 =
      BinaryApp::create(SUB, first_operand_2, second_operand_2);
  Expr* add_result_3 =
      BinaryApp::create(SUB, first_operand_3, second_operand_3);
  Expr* add_result_4 =
      BinaryApp::create(SUB, first_operand_4, second_operand_4);

  Expr* add_result_part1 =
      BinaryApp::create(CONCAT, add_result_2, add_result_1);
  Expr* add_result_part2 =
      BinaryApp::create(CONCAT, add_result_4, add_result_3);

  Expr* add_result_whole = BinaryApp::create(CONCAT, add_result_part2,
      add_result_part1);

  Expr* src = add_result_whole;

  if (guard != NULL)
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);

}

template<> void 
arm_translate<ARM_TOKEN(SUB16)> (arm::parser_data &data,
				 std::string* /*prefix*/, std::string* cond, 
				 Expr *op1, Expr *op2, Expr *op3)
{
  LValue *dst = (LValue *) op1;

  Expr* guard = data.arm_compute_cond_expr(*cond);

  Expr* first_operand = op2;
  Expr* second_operand = op3;
  Expr* first_operand_1 = TernaryApp::create(EXTRACT, first_operand,
      Constant::create(0), Constant::create(16));
  Expr* first_operand_2 = TernaryApp::create(EXTRACT, first_operand->ref(),
      Constant::create(16), Constant::create(16));

  Expr* second_operand_1 = TernaryApp::create(EXTRACT, second_operand,
      Constant::create(0), Constant::create(16));
  Expr* second_operand_2 = TernaryApp::create(EXTRACT, second_operand->ref(),
      Constant::create(16), Constant::create(16));

  Expr* add_result_1 =
      BinaryApp::create(SUB, first_operand_1, second_operand_1);
  Expr* add_result_2 =
      BinaryApp::create(SUB, first_operand_2, second_operand_2);
  Expr* add_result_whole =
      BinaryApp::create(CONCAT, add_result_1, add_result_2);

  Expr* src = add_result_whole;

  if (guard != NULL)
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);
}

template<> void arm_translate<ARM_TOKEN(SDIV)> (arm::parser_data &data,
    Expr *op1, Expr *op2, Expr *op3)
{
  Expr* src = BinaryApp::create(SDIV, op2, op3);
  LValue* dst = (LValue*) op1;

  data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);
}

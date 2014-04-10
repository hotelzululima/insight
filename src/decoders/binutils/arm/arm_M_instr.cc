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

#include "arm_translation_functions.hh"

using namespace std;

template<> void arm_translate<ARM_TOKEN(MOV)> (arm::parser_data &data,
    bool is_S_suffix, std::string* cond, Expr *op1, Expr *op2)
{

  LValue *dst = (LValue *) op1;
  Expr *src = op2;
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (src->get_bv_size() > dst->get_bv_size())
    Expr::extract_with_bit_vector_of(src, dst);
  else if (src->get_bv_size() < dst->get_bv_size())
    Expr::extract_with_bit_vector_of((Expr *&) dst, src);

  if (is_S_suffix && MOV_INS)
  {
    data.mc->add_assignment(data.start_ma, dst, src);
    update_flags(data, guard, src, MOV_INS);
  }
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
}

template<> void arm_translate<ARM_TOKEN(MVN)> (arm::parser_data &data,
    bool is_S_suffix, std::string* cond, Expr *op1, Expr *op2)
{

  LValue *dst = (LValue *) op1;
  Expr *src = UnaryApp::create (BV_OP_NOT, op2);
  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (src->get_bv_size() > dst->get_bv_size())
    Expr::extract_with_bit_vector_of(src, dst);
  else if (src->get_bv_size() < dst->get_bv_size())
    Expr::extract_with_bit_vector_of((Expr *&) dst, src);

  if (is_S_suffix && MVN_INS)
  {
    data.mc->add_assignment(data.start_ma, dst, src);
    update_flags(data, guard, src, MVN_INS);
  }
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
}

template<> void arm_translate<ARM_TOKEN(MUL)> (arm::parser_data &data,
    bool is_S_suffix, std::string* cond, Expr *op1, Expr *op2, Expr *op3)
{

  LValue *dst = (LValue *) op1;

  Expr* guard = data.arm_compute_cond_expr(*cond);

  BinaryApp* src = BinaryApp::create (BV_OP_MUL_S, op2, op3);

  if (is_S_suffix && MUL_INS)
  {
    data.mc->add_assignment(data.start_ma, dst, src);
    update_flags(data, guard, src, MUL_INS);
  }
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
}

template<> void arm_translate<ARM_TOKEN(MLA)> (arm::parser_data &data,
    bool is_S_suffix, std::string* cond, Expr *op1, Expr *op2, Expr *op3,
    Expr *op4)
{

  LValue *dst = (LValue *) op1;
  //Expr* accumulate_operand = op4;

  Expr* guard = data.arm_compute_cond_expr(*cond);

  BinaryApp* mul_result = BinaryApp::create (BV_OP_MUL_S, op2, op3);
  BinaryApp* src = BinaryApp::create (BV_OP_ADD, mul_result, op4);

  if (is_S_suffix && MLA_INS)
  {
    data.mc->add_assignment(data.start_ma, dst, src);
    update_flags(data, guard, src, MLA_INS);
  }
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
}

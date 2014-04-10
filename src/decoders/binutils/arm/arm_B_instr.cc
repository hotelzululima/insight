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

template<> void arm_translate<ARM_TOKEN(BIC)> (arm::parser_data &data,
    bool is_S_suffix, std::string* cond, Expr *op1, Expr *op2, Expr *op3)
{
  LValue *dst = (LValue *) op1;

  Expr* not_oprnd2 = UnaryApp::create (BV_OP_NOT, op3);
  BinaryApp* src = BinaryApp::create (BV_OP_AND, op2, not_oprnd2);

  Expr* guard = data.arm_compute_cond_expr(*cond);

  if (is_S_suffix && BIC_INS)
  {
    data.mc->add_assignment(data.start_ma, dst, src);
    update_flags(data, guard, src, BIC_INS);
  }
  else
    data.mc->add_assignment(data.start_ma, dst, src, data.next_ma, guard);
}

template<> void arm_translate<ARM_TOKEN(B_OR_BYTE_SUFFIX)> (arm::parser_data &data,
    std::string* cond, int label) {
  RegisterExpr* r15 = (RegisterExpr*) data.get_register("r15");

  Expr* guard = data.arm_compute_cond_expr(*cond);

  data.mc->add_assignment(data.start_ma, (RegisterExpr*) r15, 
			  Constant::create(label, 0, r15->get_bv_size ()), 
			  data.next_ma, guard);
}

template<> void arm_translate<ARM_TOKEN(BL)> (arm::parser_data &data,
    std::string* cond, int label) {
  RegisterExpr* r14 = (RegisterExpr*) data.get_register("r14");
  RegisterExpr* r15 = (RegisterExpr*) data.get_register("r15");

  Expr* guard = data.arm_compute_cond_expr(*cond);

  data.mc->add_assignment(data.start_ma, r14, BinaryApp::create (BV_OP_SUB, 
								 r15, 4));
  data.mc->add_assignment(data.start_ma, (RegisterExpr*) r15->ref(),
			  Constant::create(label, 0, r15->get_bv_size ()), 
			  data.next_ma, guard);
}

template<> void arm_translate<ARM_TOKEN(BX)> (arm::parser_data &data,
    std::string* cond, Expr* reg) {
  RegisterExpr* r15 = (RegisterExpr*) data.get_register("r15");

  Expr* guard = data.arm_compute_cond_expr(*cond);

  data.mc->add_assignment(data.start_ma, (RegisterExpr*) r15, reg, data.next_ma,
      guard);
}

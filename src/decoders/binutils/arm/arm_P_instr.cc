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

template<> void arm_translate<ARM_TOKEN(PUSH)> (arm::parser_data &data,
    std::list<RegisterExpr*> *reg_list) {
  LValue *sp = arm_translate_sp(data);

  std::list<RegisterExpr*>::iterator iter;
  std::list<RegisterExpr*>::iterator iter2 = reg_list->begin();
  iter2++;

  for (iter = reg_list->begin(); iter != reg_list->end(); iter++) {

    data.mc->add_assignment(data.start_ma, (LValue *) sp->ref(),
        BinaryApp::create(SUB, sp->ref(), 4));

    if (iter2 == reg_list->end()) {
      data.mc->add_assignment(data.start_ma, MemCell::create(sp->ref(),
          (*iter)->get_bv_offset(), (*iter)->get_bv_size()), *iter,
          data.next_ma);
    } else {
      data.mc->add_assignment(data.start_ma, MemCell::create(sp->ref(),
          (*iter)->get_bv_offset(), (*iter)->get_bv_size()), *iter);
    }

    iter2++;

  }

  sp->deref(); //for the first time using
}


template<> void arm_translate<ARM_TOKEN(POP)> (arm::parser_data &data,
    std::list<RegisterExpr*> *reg_list) {
  LValue *sp = arm_translate_sp(data);

  std::list<RegisterExpr*>::iterator iter;
  std::list<RegisterExpr*>::iterator iter2 = reg_list->begin();
  iter2++;

  for (iter = reg_list->begin(); iter != reg_list->end(); iter++) {

    data.mc->add_assignment(data.start_ma, (LValue*) (*iter), MemCell::create(
        sp->ref(), (*iter)->get_bv_offset(), (*iter)->get_bv_size()));

    if (iter2 == reg_list->end()) {
      data.mc->add_assignment(data.start_ma, (LValue *) sp->ref(),
          BinaryApp::create(ADD, sp->ref(), 4), data.next_ma);
    } else {
      data.mc->add_assignment(data.start_ma, (LValue *) sp->ref(),
          BinaryApp::create(ADD, sp->ref(), 4));
    }

    iter2++;
  }
  sp->deref(); //for the first time using
}


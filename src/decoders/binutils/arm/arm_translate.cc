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

#include <cassert>
#include "arm_translate.hh"

using namespace std;

arm::parser_data::parser_data ()
{
  register_pairs["r0"] = "r1";
  register_pairs["r2"] = "r3";
  register_pairs["r4"] = "r5";
  register_pairs["r6"] = "r7";
  register_pairs["r8"] = "r9";
  register_pairs["r10"] = "r11";
  register_pairs["r12"] = "r13";
}

LValue *
arm::parser_data::get_register(const char *regname) const
{
  const RegisterDesc *rd = arch->get_register (regname);
  int offset = rd->get_window_offset ();
  int size = rd->get_window_size ();

  if (rd->is_alias ())
    rd = arch->get_register (rd->get_label ());

  return RegisterExpr::create (rd, offset, size);
}

LValue *
arm::parser_data::get_adjacent_register (const Expr *reg) const
{
  assert (reg->is_RegisterExpr ());
  std::string rname = dynamic_cast<const RegisterExpr *> (reg)->get_name ();
  assert (register_pairs.find (rname) != register_pairs.end ());
  rname = register_pairs.find (rname)->second;
  return get_register (rname.c_str ());
}

LValue *
arm::parser_data::get_flag (const char *flagname) const
{
  return get_register (flagname);
}


LValue *arm_translate_register(arm::parser_data &data,
                               const std::string &regname)
{
  return data.get_register (regname.c_str());
}

/* --------------- */

void arm_assign(arm::parser_data &, const LValue *, const Expr *)
{
}

Expr* arm::parser_data::arm_compute_cond_expr(string cond_code)
{
  RegisterExpr* z_flag;
  RegisterExpr*n_flag;
  RegisterExpr* c_flag;
  RegisterExpr* v_flag;

  if (cond_code == "eq") {
    z_flag = (RegisterExpr*) get_register("z");
    return BinaryApp::create(NEQ, z_flag, Constant::create(0));

  } else if (cond_code == "ne") {
    z_flag = (RegisterExpr*) get_register("z");
    return BinaryApp::create(EQ, z_flag, Constant::create(0));
  } else if (cond_code == "cs" || cond_code == "hs") {
    c_flag = (RegisterExpr*) get_register("c");
    return BinaryApp::create(NEQ, c_flag, Constant::create(0));
  } else if (cond_code == "cc" || cond_code == "lo") {
    c_flag = (RegisterExpr*) get_register("c");
    return BinaryApp::create(EQ, c_flag, Constant::create(0));
  } else if (cond_code == "mi") {
    n_flag = (RegisterExpr*) get_register("n");
    return BinaryApp::create(NEQ, n_flag, Constant::create(0));
  } else if (cond_code == "pl") {
    n_flag = (RegisterExpr*) get_register("n");
    BinaryApp::create(EQ, n_flag, Constant::create(0));
  } else if (cond_code == "vs") {
    v_flag = (RegisterExpr*) get_register("v");
    return BinaryApp::create(NEQ, v_flag, Constant::create(0));
  } else if (cond_code == "vc") {
    v_flag = (RegisterExpr*) get_register("v");
    return BinaryApp::create(EQ, v_flag, Constant::create(0));
  } else if (cond_code == "hi") {
    c_flag = (RegisterExpr*) get_register("c");
    Expr* c_set = BinaryApp::create(NEQ, c_flag, Constant::create(0));

    z_flag = (RegisterExpr*) get_register("z");
    Expr* z_clear = BinaryApp::create(EQ, z_flag, Constant::create(0));

    return BinaryApp::create(LAND, c_set, z_clear);
  } else if (cond_code == "ls") {
    c_flag = (RegisterExpr*) get_register("c");
    Expr* c_clear = BinaryApp::create(EQ, c_flag, Constant::create(0));

    z_flag = (RegisterExpr*) get_register("z");
    Expr* z_set = BinaryApp::create(NEQ, z_flag, Constant::create(0));

    return BinaryApp::create(LOR, c_clear, z_set);
  } else if (cond_code == "ge") {
    n_flag = (RegisterExpr*) get_register("n");

    v_flag = (RegisterExpr*) get_register("v");

    return BinaryApp::create(EQ, n_flag, v_flag);
  } else if (cond_code == "lt") {
    n_flag = (RegisterExpr*) get_register("n");

    v_flag = (RegisterExpr*) get_register("v");

    return BinaryApp::create(NEQ, n_flag, v_flag);
  } else if (cond_code == "gt") {
    z_flag = (RegisterExpr*) get_register("z");
    Expr* z_clear = BinaryApp::create(EQ, z_flag, Constant::create(0));

    n_flag = (RegisterExpr*) get_register("n");

    v_flag = (RegisterExpr*) get_register("v");

    Expr* n_v_the_same = BinaryApp::create(EQ, n_flag, v_flag);

    return BinaryApp::create(LAND, z_clear, n_v_the_same);

  } else if (cond_code == "le") {
    z_flag = (RegisterExpr*) get_register("z");
    Expr* z_set = BinaryApp::create(NEQ, z_flag, Constant::create(0));

    n_flag = (RegisterExpr*) get_register("n");

    v_flag = (RegisterExpr*) get_register("v");

    Expr* n_v_different = BinaryApp::create(NEQ, n_flag, v_flag);

    return BinaryApp::create(LOR, z_set, n_v_different);

  } else if (cond_code == "al") {
    return NULL; //NULL means unconditional
  }

  return NULL;
}

void update_flags(arm::parser_data &data, Expr* guard, Expr* run_time_result,
    UPDATE_FLAGS_FOR_INSTRUCTIONS ins)
{
  LValue* dst;
  RegisterExpr* n_flag;
  RegisterExpr* z_flag;
  RegisterExpr* c_flag;
  RegisterExpr* v_flag;
  Expr* src;

  //N Flag
  if (ins & N_FLAG) {
    dst = n_flag = (RegisterExpr*) data.get_flag("n");

    //result_less_than_zero
    src = BinaryApp::create(LT_S, run_time_result->ref(), Constant::create(0));

    if ( ((uword_t) ins) >> N_FLAG_BIT_POSITION )
      data.mc->add_assignment(data.start_ma, dst, src);
    else
    {
      if (guard != NULL)
            data.mc->add_assignment(data.start_ma, dst, src, data.next_ma,
                guard->ref());
          else
            data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);
    }
  }

  //Z flag
  if (ins & Z_FLAG) {
    dst = z_flag = (RegisterExpr*) data.get_flag("z");

    //result_equal_zero
    src = BinaryApp::create(EQ, run_time_result->ref(), Constant::create(0));

    if ( ((uword_t) ins) >> Z_FLAG_BIT_POSITION )
      data.mc->add_assignment(data.start_ma, dst, src);
    else
    {
      if (guard != NULL)
        data.mc->add_assignment(data.start_ma, dst, src, data.next_ma,
            guard->ref());
      else
        data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);
    }
  }

  //C flag
  if (ins & C_FLAG) {
    dst = c_flag = (RegisterExpr*) data.get_flag("c");

    word_t two_power_32 = (word_t) 1 << 32;
    word_t maximum_usigned_number = two_power_32 - 1;

    //carry_geq_maxiumum_number
    src
        = BinaryApp::create(GEQ_S, run_time_result->ref(), maximum_usigned_number);

    if ( ((uword_t) ins) >> C_FLAG_BIT_POSITION )
      data.mc->add_assignment(data.start_ma, dst, src);
    else
    {
      if (guard != NULL)
        data.mc->add_assignment(data.start_ma, dst, src, data.next_ma,
            guard->ref());
      else
        data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);
    }
  }

  //V flag
  if (ins & V_FLAG) {
    dst = v_flag = (RegisterExpr*) data.get_flag("v");

    word_t two_power_31 = (word_t) 1 << 31;
    word_t maximum_positive_number = two_power_31 - 1;
    word_t minimum_negative_number = -two_power_31;

    Expr* geq_positive_number = BinaryApp::create(GEQ_S, run_time_result->ref(),
        maximum_positive_number);
    Expr* leq_minimum_negative_number = BinaryApp::create(LEQ_S,
        run_time_result->ref(), minimum_negative_number);

    src = BinaryApp::create(LOR, geq_positive_number,
        leq_minimum_negative_number);

    if ( ((uword_t) ins) >> V_FLAG_BIT_POSITION )
      data.mc->add_assignment(data.start_ma, dst, src);
    else
    {
      if (guard != NULL)
        data.mc->add_assignment(data.start_ma, dst, src, data.next_ma,
            guard->ref());
      else
        data.mc->add_assignment(data.start_ma, dst, src, data.next_ma);
    }
  }
}

LValue *
arm_translate_sp (arm::parser_data &data)
{
  return data.get_register ("r13");
}

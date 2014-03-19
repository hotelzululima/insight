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

#include <cassert>
#include <string>
#include <sstream>
#include <io/expressions/expr-parser.hh>
#include <utils/logs.hh>
#include <utils/tools.hh>

#include "msp430_translate.hh"

using namespace std;

RegisterExpr *
msp430::parser_data::get_tmp_register (int size)
{
  ostringstream oss;
  oss << "tmpr" << current_tmp_register++ << "_" << size;
  string regname = oss.str ();
  if (! arch->has_tmp_register (regname))
    arch->add_tmp_register (regname, size);

  return get_register (regname.c_str ());
}

RegisterExpr *
msp430::parser_data::get_register (const char *regname) const
{
  assert (regname != NULL);

  const RegisterDesc *rd = arch->get_register (regname);
  int offset = rd->get_window_offset ();
  int size = rd->get_window_size ();

  if (rd->is_alias ())
    rd = arch->get_register (rd->get_label ());

  return RegisterExpr::create (rd, offset, size);
}


msp430::parser_data::parser_data (MicrocodeArchitecture *a, Microcode *out,
				  const std::string &inst,
				  address_t start, address_t next) {
  arch = a;
  instruction = inst;
  mc = out;
  start_ma = MicrocodeAddress(start);
  next_ma = MicrocodeAddress(next);
  current_tmp_register = 0;

  is_extended = 0;
  operand_size = 16;

  for (unsigned int i = 0;
       i < STATIC_ARRAY_COUNT(post_increment_registers);
       i++)
    post_increment_registers[i] = NULL;
}

msp430::parser_data::~parser_data() {
}

Expr *
msp430::parser_data::get_memory_reference (int disp, Expr *bis,
					   bool may_truncate)
{
  if (bis != NULL) {
    if (may_truncate) {
      /* We may need to truncate the address to 16-bit, so put it in a
	 temporary register */
      LValue *reg = get_tmp_register(MSP430_SIZE_A);
      MicrocodeAddress do_test = start_ma + 1;
      MicrocodeAddress test_target = start_ma + 2;
      Expr *cond =
	BinaryApp::create(BV_OP_LT_U, reg->ref(),
			  Constant::create(0x10000, 0, MSP430_SIZE_A), 0, 1);

      mc->add_assignment(start_ma, reg->ref(),
			 BinaryApp::create(BV_OP_ADD, bis,
					   Constant::create(disp,
							    0, MSP430_SIZE_A)),
			 do_test, NULL);
      mc->add_assignment(do_test, reg,
			 BinaryApp::create(BV_OP_AND, reg->ref(),
					   Constant::create(0xffff,
							    0, MSP430_SIZE_A)),
			 test_target, cond);
      mc->add_skip(do_test, test_target,
		   UnaryApp::create(BV_OP_NOT, cond->ref (), 0, 1));

      start_ma = start_ma + 2;
      bis = reg;
    } else
      bis = BinaryApp::create(BV_OP_ADD, bis,
			      Constant::create(disp, 0, MSP430_SIZE_A),
			      0, MSP430_SIZE_A);
  } else
    bis = Constant::create (disp, 0, MSP430_SIZE_A);

  return MemCell::create (bis, 0, MSP430_SIZE_A);
}

void
msp430::parser_data::add_postincrement(RegisterExpr *reg) {
  for (unsigned int i = 0;
       i < STATIC_ARRAY_COUNT(post_increment_registers);
       i++) {
    if (post_increment_registers[i] == NULL) {
      post_increment_registers[i] = reg;
      return;
    }
  }

  logs::fatal_error("Too many postincremented registers!");
}

void
msp430::parser_data::finalize_postincrements(void) {
  for (unsigned int i = 0;
       i < STATIC_ARRAY_COUNT(post_increment_registers);
       i++) {
    RegisterExpr *reg = post_increment_registers[i];
    int bytes_to_add = operand_size == 20? 4 : (operand_size / 8);

    if (reg != NULL) {
      mc->add_assignment(start_ma, reg->ref(),
			 BinaryApp::create(BV_OP_ADD, reg->ref(),
					   Constant::create(bytes_to_add,
							    0, MSP430_SIZE_A),
					   0, MSP430_SIZE_A),
			 start_ma + 1, NULL);
      start_ma = start_ma + 1;
    }
  }

  mc->add_skip(start_ma, next_ma);
}

void
msp430_set_operands_size (Expr *&dst, Expr *&src)
{
  if (dst->get_bv_size() < src->get_bv_size())
    Expr::extract_with_bit_vector_size_of (src, dst);
  else if (dst->get_bv_size() > src->get_bv_size())
    Expr::extract_with_bit_vector_size_of ((Expr *&) dst, src);
}

			/* --------------- */

static void
s_translate_zero_excess(msp430::parser_data &data, Expr *dest, int size) {
  int rest = MSP430_SIZE_A - size;

  if (rest > 0 && !dest->is_RegisterExpr())
    return;

  data.mc->add_assignment(data.start_ma,
			  dynamic_cast<LValue *>(dest->extract_bit_vector(size, rest)),
			  Constant::zero(rest), data.start_ma + 1, NULL);

  data.start_ma = data.start_ma + 1;
}

void
msp430_translate_with_size (msp430::parser_data &data,
			    Expr *source, Expr *dest, bool zero,
			    void (*tr) (msp430::parser_data &,Expr *, Expr *))
{
  int size = data.operand_size;
  Expr *tmp;

  if (zero)
    s_translate_zero_excess(data, dest, size);

  tmp = source->extract_bit_vector(0, size);
  source->deref();
  source = tmp;
  tmp = dest->extract_bit_vector(0, size);
  dest->deref();
  dest = tmp;

  tr (data, source, dest);
}

void
msp430_translate_with_size (msp430::parser_data &DEFAULT_DATA,
			    Expr *op1, bool zero,
			    void (*tr) (msp430::parser_data &, Expr *))
{
  int size = data.operand_size;
  Expr *tmp;

  if (zero)
    s_translate_zero_excess(data, tmp, size);

  tmp = op1->extract_bit_vector(0, size);
  op1->deref();

  tr (data, tmp);
}

			/* --------------- */

void
msp430_if_then_else (MicrocodeAddress start, msp430::parser_data &data,
		     Expr *cond,
		     MicrocodeAddress ifaddr, MicrocodeAddress elseaddr)
{
  data.mc->add_skip (start, ifaddr, cond);
  data.mc->add_skip (start, elseaddr,
		     UnaryApp::create (BV_OP_NOT, cond->ref (), 0, 1));
}

MSP430_TRANSLATE_0_OP(BAD)
{
  throw Decoder::UnknownMnemonic ("not an opcode at "
				  + data.start_ma.to_string ());
}

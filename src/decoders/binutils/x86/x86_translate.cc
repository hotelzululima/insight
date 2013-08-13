/*-
 * Copyright (C) 2010-2013, Centre National de la Recherche Scientifique,
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
#include "x86_translate.hh"

#define TMPREG(_i) ("tmpr" #_i)
#define TMP_REGISTERS_SHIFT 100
#define ANONYMOUS_EFLAGS 0

using namespace std;


LValue *
x86::parser_data::get_tmp_register (const char *id, int size) const
{
  ostringstream oss;
  assert (id != NULL);
  oss << id << "_" << size;
  string regname = oss.str ();
  if (! arch->has_tmp_register (regname))
    arch->add_tmp_register (regname, size);

  return get_register (regname.c_str ()); 
}

LValue *
x86::parser_data::get_register (const char *regname) const
{
  assert (regname != NULL);

  const RegisterDesc *rd = arch->get_register (regname);
  int offset = rd->get_window_offset ();
  int size = rd->get_window_size ();

  if (rd->is_alias ())
    rd = arch->get_register (rd->get_label ());

  return RegisterExpr::create (rd, offset, size);
}

LValue *
x86::parser_data::get_flag (const char *flagname) const
{
  assert (flagname != NULL);
  return get_register (flagname);
}


x86::parser_data::parser_data (MicrocodeArchitecture *a, Microcode *out, 
				  const std::string &inst, 
				  address_t start, address_t next) {
  arch = a;
  has_prefix = false;
  instruction = inst;
  mc = out;
  start_ma = MicrocodeAddress(start);
  next_ma = MicrocodeAddress(next);
  lock = false;

  switch (a->get_word_size())
    {
    case 64:
      data_mode = MODE_64;
      addr_mode = MODE_64;
      break;

    case 32:
      data_mode = MODE_32;
      addr_mode = MODE_32;
      break;

    default:
      assert(true);
    }

  data_segment = "ds";
  code_segment = "cs";
  stack_segment = "ss";

#define X86_CC(id,f) \
  condition_codes[X86_CC_ ## id] = expr_parser (f, a);
#include "x86_cc.def"
#undef X86_CC
  segment_registers.insert (a->get_register ("cs"));
  segment_registers.insert (a->get_register ("ds"));
  segment_registers.insert (a->get_register ("es"));
  segment_registers.insert (a->get_register ("fs"));
  segment_registers.insert (a->get_register ("gs"));
  segment_registers.insert (a->get_register ("ss"));
}

x86::parser_data::~parser_data() {
  for (int i = 0; i < NB_CC; i++)
    condition_codes[i]->deref ();
}

bool 
x86::parser_data::is_segment_register (const Expr *expr) 
{
  const RegisterExpr *reg = dynamic_cast<const RegisterExpr *> (expr);
  assert (reg != NULL);

  return 
    segment_registers.find (reg->get_descriptor ()) != segment_registers.end ();
}

Expr *
x86::parser_data::get_memory_reference (Expr *section, int disp, 
					   Expr *bis) const
{  
  if (section != NULL)
    {
      //cerr << "section registers are not yet supported" << endl;
      //section = MemCell::create (get_register (data_segment));
      section->deref ();
      //abort ();
    }

    
  if (bis)
    bis = BinaryApp::create (BV_OP_ADD, bis, 
			     Constant::create (disp, 0, bis->get_bv_size ()));
  else
    bis = Constant::create (disp, 0, arch->get_word_size ());
  
  //  return MemCell::create (BinaryApp::create (BV_OP_ADD, MemCell::create(section,
  // std::string ("segment")), bis));
  return MemCell::create (bis, 0, arch->get_word_size ());
}

/* -------------------------------------------------------------------------- */

void 
x86_skip (x86::parser_data &data)
{
  data.mc->add_skip (data.start_ma, data.next_ma); 
}

LValue * 
x86_translate_esp (x86::parser_data &data)
{
  return data.get_register ("esp");
}

void 
x86_set_operands_size (Expr *&dst, Expr *&src)
{
  if (dst->get_bv_size() < src->get_bv_size())
    Expr::extract_with_bit_vector_size_of (src, dst);
  else if (dst->get_bv_size() > src->get_bv_size())
    Expr::extract_with_bit_vector_size_of ((Expr *&) dst, src);
}


			/* --------------- */

static void
s_assign_flag (const char *flag, MicrocodeAddress &from, 
	       x86::parser_data &data, Expr *value, 
	       MicrocodeAddress *to = NULL)
{
  data.mc->add_assignment (from, data.get_flag (flag), value, to);
}

void 
x86_assign_flag (MicrocodeAddress &from, x86::parser_data &data, 
		 const char *flag, bool value, MicrocodeAddress *to)
{
  Constant *cst = value ? Constant::one (1) : Constant::zero (1);

  s_assign_flag (flag, from, data, cst, to);
}

void 
x86_set_flag (MicrocodeAddress &from, x86::parser_data &data, 
		 const char *flag, MicrocodeAddress *to)
{
  x86_assign_flag (from, data, flag, true, to);
}

void 
x86_reset_flag (MicrocodeAddress &from, x86::parser_data &data, 
		   const char *flag, MicrocodeAddress *to)
{
  x86_assign_flag (from, data, flag, false, to);
}

			/* --------------- */

void 
x86_reset_flags (MicrocodeAddress &from, x86::parser_data &data, 
		    const char **flags, MicrocodeAddress *to)
{
  for (; flags[1] != NULL; flags++)
    x86_reset_flag (from, data, *flags);
  x86_reset_flag (from, data,*flags, to);
}

			/* --------------- */

void 
x86_assign_AF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to )
{
  s_assign_flag ("af", from, data, expr, to);
}

void 
x86_compute_AF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  x86_assign_AF (from, data, value->extract_bit_vector (4, 1),  to);
}

void 
x86_reset_AF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_reset_flag (from, data, "af", to);
}

			/* --------------- */

void 
x86_assign_CF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{
  s_assign_flag ("cf", from, data, expr, to);
}

void 
x86_reset_CF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_reset_flag (from, data, "cf", to);
}

			/* --------------- */

void 
x86_assign_OF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{  
  s_assign_flag ("of", from, data, expr, to);
}

void 
x86_reset_OF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_reset_flag (from, data, "of", to);
}

			/* --------------- */

void 
x86_assign_PF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to )
{
  s_assign_flag ("pf", from, data, expr, to);
}

void 
x86_compute_PF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  int i;
  Expr *cond = Constant::one (1);

  for (i = 0; i < 8; i++)
    cond = BinaryApp::create (BV_OP_XOR, cond, 
			      Expr::createExtract (value->ref (), i, 1),
			      0, 1);
  data.mc->add_assignment (from, data.get_flag ("pf"), cond, to);  
}

void 
x86_reset_PF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_reset_flag (from, data, "pf", to);
}

			/* --------------- */

void 
x86_assign_SF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{
  s_assign_flag ("sf", from, data, expr, to);
}


void 
x86_compute_SF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  Expr *v = value->extract_bit_vector (value->get_bv_size () -1, 1);
  s_assign_flag ("sf", from, data, v, to);
}


void 
x86_reset_SF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_reset_flag (from, data, "sf", to);
}

			/* --------------- */

void 
x86_assign_ZF (MicrocodeAddress &from, x86::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{
  s_assign_flag ("zf", from, data, expr, to);
}

void 
x86_compute_ZF (MicrocodeAddress &from, x86::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  Expr *v = 
    BinaryApp::createEquality (value->ref (), 
			       Constant::zero (value->get_bv_size ()));
  x86_assign_ZF (from, data, v, to);
}

void 
x86_reset_ZF (MicrocodeAddress &from, x86::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_reset_flag (from, data, "zf", to);
}

			/* --------------- */

void
x86_translate_with_size (x86::parser_data &DEFAULT_DATA, 
			    Expr *op1, Expr *op2, int size,
			    void (*tr) (x86::parser_data &,Expr *, Expr *))
{
  Expr::extract_bit_vector (op1, 0, size);
  Expr::extract_bit_vector (op2, 0, size);
  tr (data, op1, op2);
}

void
x86_translate_with_size (x86::parser_data &DEFAULT_DATA, 
			    Expr *op1, int size,
			    void (*tr) (x86::parser_data &, Expr *))
{
  Expr::extract_bit_vector (op1, 0, size);
  tr (data, op1);
}

			/* --------------- */

void 
x86_if_then_else (MicrocodeAddress start, x86::parser_data &data,
		     Expr *cond,
		     MicrocodeAddress ifaddr, MicrocodeAddress elseaddr)
{
  data.mc->add_skip (start, ifaddr, cond);
  data.mc->add_skip (start, elseaddr, 
		     UnaryApp::create (BV_OP_NOT, cond->ref (), 0, 1));
}

X86_TRANSLATE_0_OP(BAD)
{
  throw Decoder::UnknownMnemonic ("not an opcode at " 
				  + data.start_ma.to_string ());
}

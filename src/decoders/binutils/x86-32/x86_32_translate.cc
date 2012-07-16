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
#include <string>
#include <sstream>
#include "x86_32_translate.hh"

#define TMPREG(_i) ("tmpr" #_i)
#define TMP_REGISTERS_SHIFT 100
#define ANONYMOUS_EFLAGS 0

using namespace std;


LValue *
x86_32::parser_data::get_tmp_register (const char *id, int size) const
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
x86_32::parser_data::get_register (const char *regname) const
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
x86_32::parser_data::get_flag (const char *flagname) const
{
  assert (flagname != NULL);
  return get_register (flagname);
}


x86_32::parser_data::parser_data (MicrocodeArchitecture *a, Microcode *out, 
				  const std::string &inst, 
				  address_t start, address_t next) {
  arch = a;
  has_prefix = false;
  instruction = inst;
  mc = out;
  start_ma = MicrocodeAddress(start);
  next_ma = MicrocodeAddress(next);
  data16 = false;
  addr16 = false;
  data_segment = "ds";
  code_segment = "cs";
  stack_segment = "ss";

#define X86_32_CC(id,f) \
  condition_codes[X86_32_CC_ ## id] = Expr::parse (a, f);
#include "x86_32_cc.def"
#undef X86_32_CC
}

x86_32::parser_data::~parser_data() {
  for (int i = 0; i < NB_CC; i++)
    condition_codes[i]->deref ();
}

Expr *
x86_32::parser_data::get_memory_reference (Expr *section, int disp, 
					   Expr *bis) const
{  
  if (section != NULL)
    {
      cerr << "section registers are not yet supported" << endl;
      //section = MemCell::create (get_register (data_segment));
      section->deref ();
      //abort ();
    }

    
  if (bis)
    bis = BinaryApp::create (ADD, bis, Constant::create (disp));
  else
    bis = Constant::create (disp);
  
  //  return MemCell::create (BinaryApp::create (ADD, MemCell::create(section,
  // std::string ("segment")), bis));
  return MemCell::create (bis);
}

/* -------------------------------------------------------------------------- */

void 
x86_32_skip (x86_32::parser_data &data)
{
  data.mc->add_skip (data.start_ma, data.next_ma); 
}

LValue * 
x86_32_translate_esp (x86_32::parser_data &data)
{
  return data.get_register ("esp");
}

void 
x86_32_set_operands_size (Expr *&dst, Expr *&src)
{
  if (dst->get_bv_size() < src->get_bv_size())
    Expr::extract_with_bit_vector_size_of (src, dst);
  else if (dst->get_bv_size() > src->get_bv_size())
    Expr::extract_with_bit_vector_size_of ((Expr *&) dst, src);
}

void 
x86_32_binary_op (MicrocodeAddress &from, x86_32::parser_data &data, 
		  BinaryOp op, LValue *dst, Expr *src, 
		  x86_32_compute_flag_proc **flags,
		  MicrocodeAddress *to)
{
  x86_32_set_operands_size ((Expr *&) dst, src);
  Expr *result = BinaryApp::create (op, dst->ref (), src, 0,
				    dst->get_bv_size ());

  data.mc->add_assignment (from, (LValue *) dst->ref (), result, NULL);
  for(; *flags; flags++)    
    (*flags) (from, data, dst, flags[1] ? NULL : to);
  dst->deref ();
}

			/* --------------- */

static void
s_assign_flag (const char *flag, MicrocodeAddress &from, 
	       x86_32::parser_data &data, Expr *value, 
	       MicrocodeAddress *to = NULL)
{
  data.mc->add_assignment (from, data.get_flag (flag), value, to);
}

void 
x86_32_assign_flag (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const char *flag, bool value, MicrocodeAddress *to)
{
  Constant *cst = value ? Constant::one (1) : Constant::zero (1);

  s_assign_flag (flag, from, data, cst, to);
}

void 
x86_32_set_flag (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const char *flag, MicrocodeAddress *to)
{
  x86_32_assign_flag (from, data, flag, true, to);
}

void 
x86_32_reset_flag (MicrocodeAddress &from, x86_32::parser_data &data, 
		   const char *flag, MicrocodeAddress *to)
{
  x86_32_assign_flag (from, data, flag, false, to);
}

			/* --------------- */

void 
x86_32_reset_flags (MicrocodeAddress &from, x86_32::parser_data &data, 
		    const char **flags, MicrocodeAddress *to)
{
  for (; flags[1] != NULL; flags++)
    x86_32_reset_flag (from, data, *flags);
  x86_32_reset_flag (from, data,*flags, to);
}

			/* --------------- */

void 
x86_32_assign_AF (MicrocodeAddress &from, x86_32::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to )
{
  s_assign_flag ("af", from, data, expr, to);
}

void 
x86_32_compute_AF (MicrocodeAddress &from, x86_32::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  x86_32_assign_AF (from, data, value->extract_bit_vector (4, 1),  to);
}

void 
x86_32_reset_AF (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_32_reset_flag (from, data, "af", to);
}

			/* --------------- */

void 
x86_32_assign_CF (MicrocodeAddress &from, x86_32::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{
  s_assign_flag ("cf", from, data, expr, to);
}

void 
x86_32_reset_CF (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_32_reset_flag (from, data, "cf", to);
}

			/* --------------- */

void 
x86_32_assign_OF (MicrocodeAddress &from, x86_32::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{  
  s_assign_flag ("of", from, data, expr, to);
}

void 
x86_32_reset_OF (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_32_reset_flag (from, data, "of", to);
}

			/* --------------- */

void 
x86_32_assign_PF (MicrocodeAddress &from, x86_32::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to )
{
  s_assign_flag ("pf", from, data, expr, to);
}

void 
x86_32_compute_PF (MicrocodeAddress &from, x86_32::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  int i;
  int offset = value->get_bv_offset ();
  Expr *cond = Constant::one (1);

  for (i = 0; i < 8; i++, offset++)
    cond = BinaryApp::create (XOR, cond, value->extract_bit_vector (offset, 1), 
			      0, 1);
  data.mc->add_assignment (from, data.get_flag ("pf"), cond, to);  
}

void 
x86_32_reset_PF (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_32_reset_flag (from, data, "pf", to);
}

			/* --------------- */

void 
x86_32_assign_SF (MicrocodeAddress &from, x86_32::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{
  s_assign_flag ("sf", from, data, expr, to);
}


void 
x86_32_compute_SF (MicrocodeAddress &from, x86_32::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  Expr *v = value->extract_bit_vector (value->get_bv_size () -1, 1);
  s_assign_flag ("sf", from, data, v, to);
}


void 
x86_32_reset_SF (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_32_reset_flag (from, data, "sf", to);
}

			/* --------------- */

void 
x86_32_assign_ZF (MicrocodeAddress &from, x86_32::parser_data &data, 
		  Expr *expr, MicrocodeAddress *to)
{
  s_assign_flag ("zf", from, data, expr, to);
}

void 
x86_32_compute_ZF (MicrocodeAddress &from, x86_32::parser_data &data, 
		   const Expr *value, MicrocodeAddress *to)
{
  Expr *v = 
    BinaryApp::create (EQ, value->ref (), 
		       Constant::zero (value->get_bv_size ()), 0, 1);
  x86_32_assign_ZF (from, data, v, to);
}

void 
x86_32_reset_ZF (MicrocodeAddress &from, x86_32::parser_data &data, 
		 const Expr *, MicrocodeAddress *to)
{
  x86_32_reset_flag (from, data, "zf", to);
}

			/* --------------- */

void
x86_32_translate_with_size (x86_32::parser_data &DEFAULT_DATA, 
			    Expr *op1, Expr *op2, int size,
			    void (*tr) (x86_32::parser_data &,Expr *, Expr *))
{
  Expr::extract_bit_vector (op1, 0, size);
  Expr::extract_bit_vector (op2, 0, size);
  tr (data, op1, op2);
}

void
x86_32_translate_with_size (x86_32::parser_data &DEFAULT_DATA, 
			    Expr *op1, int size,
			    void (*tr) (x86_32::parser_data &, Expr *))
{
  Expr::extract_bit_vector (op1, 0, size);
  tr (data, op1);
}

			/* --------------- */

void 
x86_32_if_then_else (MicrocodeAddress start, x86_32::parser_data &data,
		     Expr *cond,
		     MicrocodeAddress ifaddr, MicrocodeAddress elseaddr)
{
  data.mc->add_skip (start, ifaddr, cond);
  data.mc->add_skip (start, elseaddr, 
		     UnaryApp::create (NOT, cond->ref (), 0, 1));
}

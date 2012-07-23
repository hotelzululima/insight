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

#include <interpreters/concrete/ConcreteExprSemantics.hh>
#include <utils/bv-manip.hh>
#include <iostream>

/*! \ brief \todo integrer les bitfields dans les calculs */

#define BIN_OP_DEF(fun, op)                             \
  template<> ConcreteValue                              \
  ConcreteExprSemantics::                               \
  fun (ConcreteValue v1, ConcreteValue v2, int offset, int size) {	\
    word_t val = v1.get() op v2.get();	\
    val = BitVectorManip::extract_from_word (val, offset, size);	\
    return ConcreteValue(size, val);				\
  }

#define UN_OP_DEF(fun, op)                              \
  template<> ConcreteValue                              \
  ConcreteExprSemantics::                               \
  fun (ConcreteValue v, int offset, int size) {		\
    word_t val = BitVectorManip::extract_from_word (op v.get(), offset, size); \
    return ConcreteValue (size, val);				\
  }

/*****************************************************************************/

BIN_OP_DEF(ADD_eval, +);
BIN_OP_DEF(SUB_eval, -);
BIN_OP_DEF(AND_OP_eval, &);
BIN_OP_DEF(OR_eval,  |);
BIN_OP_DEF(LAND_eval, &&);
BIN_OP_DEF(LOR_eval,  ||);
BIN_OP_DEF(XOR_eval, ^);
BIN_OP_DEF(LSH_eval, <<);
BIN_OP_DEF(RSH_eval, >>);
BIN_OP_DEF(NEQ_eval,  !=);
BIN_OP_DEF(EQ_eval,  ==);
BIN_OP_DEF(MODULO_eval, %);

			/* --------------- */

static ConcreteValue DEFSZ (BV_DEFAULT_SIZE, BITS_PER_WORD);

static void
s_extend_signed_to_word_size (ConcreteValue &v);

static void
s_extend_unsigned_to_word_size (ConcreteValue &v);

template<> ConcreteValue 
ConcreteExprSemantics::MUL_S_eval (ConcreteValue v1, ConcreteValue v2, 
				   int offset, int size)
{
  s_extend_signed_to_word_size (v1);
  s_extend_signed_to_word_size (v2);

  ConcreteValue result (size, v1.get () * v2.get ());

  assert (offset == 0 && result.get_size () == size);

  return result;
}

template<> ConcreteValue 
ConcreteExprSemantics::MUL_U_eval (ConcreteValue v1, ConcreteValue v2, 
				   int offset, int size)
{
  s_extend_unsigned_to_word_size (v1);
  s_extend_unsigned_to_word_size (v2);

  ConcreteValue result (size, (uword_t) v1.get () * (uword_t) v2.get ());

  assert (offset == 0 && result.get_size () == size);

  return result;
}

			/* --------------- */

static word_t
s_cmp_s (ConcreteValue v1, ConcreteValue v2);

static word_t
s_cmp_u (ConcreteValue v1, ConcreteValue v2);

template<>
ConcreteValue 
ConcreteExprSemantics::LT_S_eval (ConcreteValue v1, ConcreteValue v2, 
				  int offset, int size)
{
  ConcreteValue result (size, s_cmp_s (v1, v2) < 0);

  assert (offset == 0 && result.get_size () == size);

  return result;
}

template<>
ConcreteValue 
ConcreteExprSemantics::LEQ_S_eval (ConcreteValue v1, ConcreteValue v2, 
				   int offset, int size)
{
  ConcreteValue result (size, s_cmp_s (v1, v2) <= 0);

  assert (offset == 0 && result.get_size () == size);

  return result;
}

template<>
ConcreteValue 
ConcreteExprSemantics::LT_U_eval (ConcreteValue v1, ConcreteValue v2, 
				  int offset, int size)
{
  ConcreteValue result (size, s_cmp_u (v1, v2) < 0);

  assert (offset == 0 && result.get_size () == size);

  return result;
}

template<>
ConcreteValue 
ConcreteExprSemantics::LEQ_U_eval (ConcreteValue v1, ConcreteValue v2, 
				   int offset, int size)
{
  ConcreteValue result (size, s_cmp_u (v1, v2) <= 0);

  assert (offset == 0 && result.get_size () == size);

  return result;
}


			/* --------------- */

template<>
ConcreteValue 
ConcreteExprSemantics::GT_S_eval(ConcreteValue v1, ConcreteValue v2, 
				 int offset, int size)
{
  return LT_S_eval (v2, v1, offset, size);
}

template<>
ConcreteValue 
ConcreteExprSemantics::GEQ_S_eval(ConcreteValue v1, ConcreteValue v2, 
				  int offset, int size)
{
  return LEQ_S_eval (v2, v1, offset, size);
}

template<>
ConcreteValue 
ConcreteExprSemantics::GT_U_eval(ConcreteValue v1, ConcreteValue v2, 
				 int offset, int size)
{
  return LT_U_eval (v2, v1, offset, size);
}

template<>
ConcreteValue 
ConcreteExprSemantics::GEQ_U_eval(ConcreteValue v1, ConcreteValue v2, 
				  int offset, int size)
{
  return LEQ_U_eval (v2, v1, offset, size);
}

			/* --------------- */

template<>
ConcreteValue 
ConcreteExprSemantics::POW_eval(ConcreteValue v1, ConcreteValue v2, 
				int, int)
{
  int size = v1.get_size();
  word_t x2 = v2.get();
  if (x2 == 0) return ConcreteValue(size, 1);
  word_t x1 = v1.get();
  word_t p = x1;
  while (x2 != 1) {
    if ((x2 % 2) == 1) {
      p = p * x1;
      x2--;
    } else {
      p = p * p;
      x2 = x2 / 2;
    }
  }
  return ConcreteValue(size, p);
}

template<>
ConcreteValue 
ConcreteExprSemantics::UDIV_eval(ConcreteValue v1, ConcreteValue v2,
				 int offset, int size)
{
  word_t val;
  // \todo semantique de unsigned
  if (v2.get() == 0)
    {
      Log::warning ("division by 0");
      val = 0;
    }
  else
    {
      val = v1.get() / v2.get();
    }

  val = BitVectorManip::extract_from_word (val, offset, size);
  return ConcreteValue (size, val);
}

template<>
ConcreteValue 
ConcreteExprSemantics::SDIV_eval(ConcreteValue v1, ConcreteValue v2,
				 int offset, int size)
{
  word_t val;

  if (v2.get() == 0)
    {
      Log::warning ("division by 0");
      val = 0;
    }
  else
    {
      val = v1.get() / v2.get();
    }

  val = BitVectorManip::extract_from_word (val, offset, size);

  return ConcreteValue(size, val);
}

template<>
ConcreteValue 
ConcreteExprSemantics::ROL_eval(ConcreteValue v, ConcreteValue rotate_number,
				int offset, int size)
{
  word_t val = v.get();
  int rotate = rotate_number.get();

  word_t val2 = (uword_t) val >> (sizeof(word_t) * 8 - v.get_size ());
  val = val << rotate;

  val = BitVectorManip::extract_from_word (val2 | val, offset, size);

  return ConcreteValue (size, val);
}

template<>
ConcreteValue 
ConcreteExprSemantics::ROR_eval(ConcreteValue v, ConcreteValue rotate_number,
				int offset, int size)
{
  word_t val = v.get();
  int rotate = rotate_number.get();

  word_t val2 = val << (sizeof(word_t) * 8 - v.get_size());
  val = (uword_t) val >> rotate;

  val = BitVectorManip::extract_from_word (val2 | val, offset, size);

  return ConcreteValue(size, val);
}

template<>
ConcreteValue 
ConcreteExprSemantics::CONCAT_eval(ConcreteValue v1, ConcreteValue v2,
				   int offset, int size)
{
  word_t val1 = v1.get();
  int size1 = v1.get_size();

  word_t val2 = v2.get();
  int size2 = v2.get_size();

  uword_t max = -1;

  //Clean val1: clear bits out of size (set = 0)
  uword_t mask1 = max >> (sizeof(word_t) * 8 - size1);
  word_t cleaned_val1 = val1 & mask1;

  //Shift left val1
  word_t shifted_val1 = cleaned_val1 << size2;

  //Clean val2: clear bits out of size (set = 0)
  uword_t mask2 = max >> (sizeof(word_t) * 8 - size2);
  word_t cleaned_val2 = val2 & mask2;

  
  return ConcreteValue(size, 
		       BitVectorManip::extract_from_word (shifted_val1 | 
							  cleaned_val2, 
							  offset, size));
}

UN_OP_DEF(NEG_eval, -);
UN_OP_DEF(NOT_eval, ~);
UN_OP_DEF(LNOT_eval, !);

template<>
ConcreteValue 
ConcreteExprSemantics::EXTRACT_eval(ConcreteValue v1, ConcreteValue v2, 
				    ConcreteValue v3, int offset, int size)
{
  word_t value = v1.get();
  int o = v2.get();
  int s = v3.get();

  value = value >> o;

  uword_t max = -1;
  word_t mask = max >> (sizeof(word_t) * 8 - s);

  return ConcreteValue(size, 
		       BitVectorManip::extract_from_word (value & mask, 
							  offset, size));
}

template<> ConcreteValue
ConcreteExprSemantics::extract_eval(ConcreteValue v,  int off, int size) {
  return expr_semantics_extract_eval<ConcreteValue, ConcreteExprSemantics>(v,
									   off, size);
}

template<>
ConcreteValue 
ConcreteExprSemantics::EXTEND_S_eval(ConcreteValue v1, ConcreteValue v2,
				     int offset, int size)
{
  int new_size = v2.get();

  ConcreteValue nv = 
    ConcreteValue(new_size, 
		  BitVectorManip::extend_signed (v1.get (),
						 v1.get_size()));
  if (size < new_size)
    nv = ConcreteExprSemantics::extract_eval (nv, offset, size);

  return nv;
}

template<>
ConcreteValue 
ConcreteExprSemantics::EXTEND_U_eval(ConcreteValue v1, ConcreteValue v2,
				     int offset, int size)
{
  int new_size = v2.get();

  ConcreteValue nv = 
    ConcreteValue(new_size, 
		  BitVectorManip::extend_unsigned (v1.get (),
						   v1.get_size()));

  if (size < new_size)
    nv = ConcreteExprSemantics::extract_eval (nv, offset, size);
  return nv;
}

template<> ConcreteValue
ConcreteExprSemantics::embed_eval(ConcreteValue v1, ConcreteValue v2, int off) {
  return expr_semantics_embed_eval<ConcreteValue, ConcreteExprSemantics>(v1,
									 v2,
									 off);
}


static word_t
s_cmp_s (ConcreteValue v1, ConcreteValue v2)
{
  assert (v1.get_size () == v2.get_size ());

  s_extend_signed_to_word_size (v1);
  s_extend_signed_to_word_size (v2);

  return v1.get() - v2.get ();
}

static word_t
s_cmp_u (ConcreteValue v1, ConcreteValue v2)
{
  assert (v1.get_size () == v2.get_size ());

  s_extend_unsigned_to_word_size (v1);
  s_extend_unsigned_to_word_size (v2);

  return v1.get() - v2.get ();
}

			/* --------------- */

static void
s_extend_signed_to_word_size (ConcreteValue &v)
{
  v = ConcreteValue (BITS_PER_WORD, 
		     BitVectorManip::extend_signed (v.get (), v.get_size ()));
		    
}

static void
s_extend_unsigned_to_word_size (ConcreteValue &v)
{
  v = ConcreteValue (BITS_PER_WORD, 
		     BitVectorManip::extend_unsigned (v.get (), v.get_size ()));
}

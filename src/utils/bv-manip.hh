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
#ifndef UTILS_BV_MANIP_HH
#define UTILS_BV_MANIP_HH

#include <kernel/Architecture.hh>

namespace BitVectorManip {

inline word_t
mask_first_bits (int nb_bits)
{
  word_t val = ~((word_t)0);
  if (nb_bits < (int) (8 * sizeof (word_t)))
    {
      val <<= nb_bits;
      val = ~val;
    }
  return val;
}

inline word_t
extract_from_word (word_t w, int offset, int size)
{
  return (w >> offset) & mask_first_bits (size);
}

inline word_t
unset_window (word_t w, int offset, int size)
{
  if (offset >= (int) (8 * sizeof (word_t)))
    return w;

  word_t mask = ~(mask_first_bits (size) << offset);

  return w & mask;
}

inline word_t
set_window (word_t w, int offset, int size)
{
  if (offset >= (int) (8 * sizeof (word_t)))
    return w;

  word_t mask = mask_first_bits (size) << offset;

  return w | mask;
}

inline word_t
assign_window (word_t dst, int offset, int size, word_t src)
{
  if (offset >= (int) (8 * sizeof (word_t)))
    return dst;

  dst = unset_window (dst, offset, size);
  src &= mask_first_bits (size);
  src <<= offset;

  return dst | src;
}

inline word_t
extend_signed (word_t val, int current_size)
{
  if (current_size == BITS_PER_WORD)
    return val;

  word_t tmpVal = val >> (current_size -1); // retrieve msb
  uword_t max = ~((uword_t)0);
  word_t new_val;

  if ((tmpVal & ((word_t) 1))) //If a(n-1) = 1;
    {
      word_t mask = max << current_size;
      new_val = val | mask;
    }
  else
    {
      word_t mask = max >> (BITS_PER_WORD - current_size);
      new_val = val & mask;
    }

  return new_val;
}

inline word_t
extend_unsigned (word_t val, int current_size)
{
  uword_t max = ~((uword_t)0);
  word_t mask = max >> (BITS_PER_WORD - current_size);

  return val & mask;
}

}

#endif /* UTILS_BV_MANIP_HH */

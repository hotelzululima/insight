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

#ifndef DOMAINS_EXPR_SEMANTICS_HH
#define DOMAINS_EXPR_SEMANTICS_HH

#include <kernel/Value.hh>

template <typename Value>
class ExprSemantics
{
public:
#define BINARY_OP(enumvalue, pp_string, is_commutative, is_associative) \
  static Value enumvalue ## _eval (Value v1, Value v2, int offset, int size);

#define UNARY_OP(enumvalue, pp_string) \
  static Value enumvalue ## _eval (Value v, int offset, int size);

#define TERNARY_OP(enumvalue, pp_string) \
  static Value enumvalue ## _eval (Value v1, Value v2, Value v3, \
                                   int offset, int size);

# include <kernel/expressions/Operators.def>
# undef BINARY_OP
# undef UNARY_OP
# undef TERNARY_OP

  /*! Embed v2 into v1 at offset off */
  static Value embed_eval(Value v1, Value v2, int off);
  static Value extract_eval(Value v, int off, int size);
};

#include <domains/ExprSemantics.ii>

#endif /* DOMAINS_EXPR_SEMANTICS_HH */

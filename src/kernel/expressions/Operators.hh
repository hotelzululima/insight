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
#ifndef KERNEL_EXPRESSIONS_OPERATORS_HH
#define KERNEL_EXPRESSIONS_OPERATORS_HH

#include <string>

/*****************************************************************************/
/*! \name Operator Definition
 *  \brief Define the operator of microcode language terms.
 *  Note that here is defined only the syntax. The semantic of operator is
 *  dependent on the interpretation mode and must not be defined here.       */
/*****************************************************************************/
/*@{*/

/*! \brief Binary Operators */
typedef enum
{
#define BINARY_OP(enumvalue, pp_string, is_commutative, is_associative) \
  enumvalue,
#include "Operators.def"
#undef BINARY_OP
  LAST_BINARY_OP
} BinaryOp;


/*! \brief Ternary Operators */
typedef enum
{
#define TERNARY_OP(enumvalue, pp_string) \
  enumvalue,
#include "Operators.def"
#undef TERNARY_OP
  LAST_TERNARY_OP
} TernaryOp;


/*! \brief Unary Operators */
typedef enum
{
#define UNARY_OP(enumvalue, pp_string) \
  enumvalue,
#include "Operators.def"
#undef UNARY_OP
  LAST_UNARY_OP
} UnaryOp;

/*! \todo Complete all operators */

/*@}*/

/*****************************************************************************/
/*! \name Operator Properties
 *  \brief Here are defined some syntactic properties.
 *  These properties can be used by syntactic manipulation of terms.         */
/*****************************************************************************/
/*@{*/

/*! \brief Tells whether an operator is associative or not */
bool binary_op_associative(BinaryOp op);

/*! \brief Tells whether an operator is commutative or not */
bool binary_op_commutative(BinaryOp op);

/*@}*/

/*****************************************************************************/
/*! \name Pretty printing
 *  \brief Pretty printing of operator symbols                               */
/*****************************************************************************/
/*@{*/

/*! \brief Pretty printing of unary operators */
std::string unary_op_to_string(UnaryOp op);

/*! \brief Pretty printing of binary operators */
std::string binary_op_to_string(BinaryOp op);
/*@}*/


/*! \brief Pretty printing of ternary- operators */
std::string ternary_op_to_string(TernaryOp op);
/*@}*/


#endif /* KERNEL_EXPRESSIONS_OPERATORS_HH */

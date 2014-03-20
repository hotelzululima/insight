/*
 * Copyright (c) 2010-2013, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#ifndef KERNEL_EXPRESSIONS_EXPRMATHSATSOLVER_HH
# define KERNEL_EXPRESSIONS_EXPRMATHSATSOLVER_HH

# include <config.h>

# if INTEGRATED_MATHSAT_SOLVER
#  include <mathsat.h>
#  include <stack>
#  include <kernel/expressions/ExprSolver.hh>

class ExprMathsatSolver : public ExprSolver
{
private:
  std::stack<msat_env> envstack;

  ExprMathsatSolver (const MicrocodeArchitecture *mca);

public:

  static const std::string &ident ();

  static void init (const ConfigTable &cfg)
    throw (UnknownSolverException);

  static void terminate ();

  static ExprSolver *create (const MicrocodeArchitecture *mca)
    throw (UnexpectedResponseException, UnknownSolverException);

  virtual ~ExprMathsatSolver ();

  virtual void add_assertion (const Expr *e)
    throw (UnexpectedResponseException);

  virtual Result check_sat (const Expr *e, bool preserve)
    throw (UnexpectedResponseException);

  virtual Result check_sat ()
    throw (UnexpectedResponseException);

  virtual void push ()
    throw (UnexpectedResponseException);

  virtual void pop ()
    throw (UnexpectedResponseException);

  virtual Constant *get_value_of (const Expr *var)
    throw (UnexpectedResponseException);
};

# else
#  warning "no MATHSAT API"
# endif /* INTEGRATED_MATHSAT_SOLVER */

#endif /* ! KERNEL_EXPRESSIONS_EXPRMATHSATSOLVER_HH */

/*
 * Copyright (c) 2010-2012, Centre National de la Recherche Scientifique,
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
#ifndef KERNEL_EXPRESSIONS_EXPRSOLVER_HH
# define KERNEL_EXPRESSIONS_EXPRSOLVER_HH

# include <stdexcept>
# include <kernel/Expressions.hh>
# include <utils/ConfigTable.hh>

class ExprSolver 
{
public:
  class SolverException : public std::runtime_error {
  public:
    SolverException (const std::string &msg) : runtime_error (msg) {
    }
  };

  class UnexpectedResponseException : public SolverException {
  public:
    UnexpectedResponseException (const std::string &msg) 
      : SolverException (msg) {
    }
  };

  class UnknownSolverException : public SolverException {
  public:
    UnknownSolverException (const std::string &msg) 
      : SolverException (msg) {
    }
  };

  static const std::string DEFAULT_COMMAND_PROP;
  static const std::string DEFAULT_NB_ARGS_PROP;
  static const std::string DEFAULT_ARG_PROP (int index);
  static const std::string DEBUG_TRACES_PROP;

  static void init (const ConfigTable &cfg);
  static void terminate ();

  static ExprSolver *create_default_solver (const MicrocodeArchitecture *mca)
    throw (UnexpectedResponseException, UnknownSolverException);

  enum Result { SAT, UNSAT, UNKNOWN };
 
  virtual ~ExprSolver ();

  virtual Result check_sat (const Expr *e, bool preserve) 
    throw (UnexpectedResponseException) = 0;

  virtual Constant *evaluate (const Expr *e, const Expr *context) 
    throw (UnexpectedResponseException);

  virtual void push () 
    throw (UnexpectedResponseException) = 0;
  virtual void pop () 
    throw (UnexpectedResponseException) = 0;
  virtual Constant *get_value_of (const Expr *var)
    throw (UnexpectedResponseException) = 0;

protected:
  ExprSolver (const MicrocodeArchitecture *mca);

  const MicrocodeArchitecture *mca;

  static bool debug_traces;
};

#endif /* ! KERNEL_EXPRESSIONS_EXPRSOLVER_HH */

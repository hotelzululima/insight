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
#ifndef KERNEL_EXPRESSIONS_EXPRPROCESSSOLVER_HH
# define KERNEL_EXPRESSIONS_EXPRPROCESSSOLVER_HH

# include <iostream>
# include <vector>
# include <kernel/expressions/ExprSolver.hh>

class ExprProcessSolver : public ExprSolver
{
protected:
  std::string command;
  std::istream *in;
  std::ostream *out;

  ExprProcessSolver (const MicrocodeArchitecture *mca, const std::string &cmd, 
		     std::istream *r, std::ostream *w);

public:
  static ExprProcessSolver *
  create (const MicrocodeArchitecture *mca, const std::string &cmd, 
	  const std::vector<std::string> &args)
    throw (UnexpectedResponseException, UnknownSolverException);

  virtual ~ExprProcessSolver ();

  virtual Result check_sat (const Expr *e, bool preserve)
    throw (UnexpectedResponseException);

  virtual Result check_sat ()
    throw (UnexpectedResponseException);
  virtual void add_assertion (const Expr *e)
    throw (UnexpectedResponseException);

  virtual void push () 
    throw (UnexpectedResponseException);
  virtual void pop () 
    throw (UnexpectedResponseException);
  virtual Constant *get_value_of (const Expr *var)
    throw (UnexpectedResponseException);

protected:
  bool init ();
  bool write_header ();
  bool read_status (bool allow_unsupported = false);
  bool send_command (const std::string &s, bool allow_unsupported = false);
  bool send_command (const char *s, bool allow_unsupported = false);
  std::string exec_command (const std::string &s);
  std::string exec_command (const char *s);
  bool declare_variable (const Expr *e);
  std::string get_result ();

};

#endif /* ! KERNEL_EXPRESSIONS_EXPRPROCESSSOLVER_HH */

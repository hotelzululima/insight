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
#include "ExprSolver.hh"

#include <kernel/expressions/ExprProcessSolver.hh>
#include <vector>

using namespace std;

const std::string ExprSolver::DEFAULT_COMMAND_PROP = 
  "kernel.expr.solver.default.command";

const std::string ExprSolver::DEFAULT_NB_ARGS_PROP =
  "kernel.expr.solver.default.nb_args";

const std::string 
ExprSolver::DEFAULT_ARG_PROP (int index) 
{
  ostringstream pref;
  pref << "solver.default.arg" << index;

  return pref.str ();
 }

static string default_solver_command;
static vector<string> default_solver_args;

void 
ExprSolver::init (const ConfigTable &cfg)
{
  default_solver_command = cfg.get (DEFAULT_COMMAND_PROP);

  int nb_args = cfg.get_integer (DEFAULT_NB_ARGS_PROP);

  for (int i = 0; i < nb_args; i++)
    default_solver_args.push_back (cfg.get (DEFAULT_ARG_PROP (i)));
}

void 
ExprSolver::terminate ()
{
}
  
ExprSolver *
ExprSolver::create_default_solver (const MicrocodeArchitecture *mca)
  throw (UnexpectedResponseException, UnknownSolverException)
{  
  return ExprProcessSolver::create (mca, default_solver_command,
				    default_solver_args);
}

ExprSolver::ExprSolver (const MicrocodeArchitecture *mca) : mca (mca)
{
}

ExprSolver::~ExprSolver ()
{
}

Constant * 
ExprSolver::evaluate (const Expr *e, const Expr *context) 
  throw (UnexpectedResponseException)
{
  Constant *result = NULL;
  Variable *var = Variable::create ("_unk", 0, e->get_bv_size ());
  Expr *phi = Expr::createAnd (Expr::createEquality (var, e->ref ()),
			       context->ref ( ));

  push ();
  if (check_sat (phi) == SAT)
    result = get_value_of (var);
  phi->deref ();
  var->deref ();
  pop ();

  return result;
}

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

static string default_solver_command;
static vector<string> default_solver_args;

void 
ExprSolver::init (const ConfigTable &cfg)
{
  default_solver_command = cfg.get ("solver.default.command");

  int nb_args = cfg.get_integer ("solver.default.nb_args");

  for (int i = 0; i < nb_args; i++)
    {
      ostringstream pref;
      pref << "solver.default.arg" << i;
      default_solver_args.push_back (cfg.get (pref.str ()));
    }
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

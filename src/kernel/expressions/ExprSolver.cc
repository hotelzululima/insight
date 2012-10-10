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

#include <utils/logs.hh>
#include <kernel/expressions/ExprProcessSolver.hh>
#include <vector>

using namespace std;

static const std::string PROP_PREFIX = "kernel.expr.solver";


const std::string ExprSolver::DEFAULT_COMMAND_PROP = 
  PROP_PREFIX + ".default.command";

const std::string ExprSolver::DEFAULT_ARGS_PROP =
  PROP_PREFIX + ".default.args";

const std::string ExprSolver::DEBUG_TRACES_PROP =
  PROP_PREFIX + ".debug-traces";

const std::string 
ExprSolver::DEFAULT_ARG_PROP (int index) 
{
  ostringstream pref;
  pref << PROP_PREFIX << ".default.arg" << index;

  return pref.str ();
}

bool ExprSolver::debug_traces = false;
static string default_solver_command;
static vector<string> default_solver_args;

void 
ExprSolver::init (const ConfigTable &cfg)
{
  default_solver_command = cfg.get (DEFAULT_COMMAND_PROP);
  string args = cfg.get (DEFAULT_ARGS_PROP);

  while (!args.empty ())
    {
      string::size_type p = args.find (' ');

      if (p == string::npos)
	{
	  default_solver_args.push_back (args);
	  break;
	}

      string tmp = args.substr (0, p );
      if (! tmp.empty ())
	default_solver_args.push_back (tmp);
    
      args = args.substr (p + 1, string::npos);
    }

  debug_traces = cfg.get_boolean (DEBUG_TRACES_PROP);
}

void 
ExprSolver::terminate ()
{
}
  
ExprSolver *
ExprSolver::create_default_solver (const MicrocodeArchitecture *mca)
  throw (UnexpectedResponseException, UnknownSolverException)
{  
  if (default_solver_command == "")
    throw UnknownSolverException (DEFAULT_COMMAND_PROP + " is not set.");
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
  std::vector<constant_t> *values = evaluate (e, context, 2);
  Constant *result = NULL;
  if (values->size () == 2)
    {
      if (debug_traces)
	{
	  logs::debug << "variable may have two values: " << endl
		      << values->at (0) << endl
		      << "and " << endl
		      << values->at (1) << endl;
	}
    }
  else if (values->size () == 1)
    {
      result = Constant::create (values->at (0), 0, e->get_bv_size ());
    }

  delete values;

  return result;
}

std::vector<constant_t> *
ExprSolver::evaluate (const Expr *e, const Expr *context, int nb_values) 
  throw (UnexpectedResponseException)
{
  std::vector<constant_t> *result = new std::vector<constant_t> ();
  if (nb_values == 0)   
    return result;

  if (debug_traces)    
    BEGIN_DBG_BLOCK ("evaluate : " + e->to_string () + " with context " + 
		     context->to_string ());
  
  Variable *var = Variable::create ("_unk", e->get_bv_size ());
  Expr *phi = Expr::createLAnd (Expr::createEquality (var->ref (), e->ref ()),
				context->ref ( ));

  push ();
  if (check_sat (phi, false) == SAT)
    {
      phi->deref ();
      while (nb_values != 0 && check_sat () == SAT)
	{
	  Constant *c = get_value_of (var);
	  if (debug_traces)
	    logs::debug << "value = " << *c << std::endl;

	  result->push_back (c->get_val ());
	  Expr *nc = Expr::createDisequality (var->ref (), c->ref ());
	  add_assertion (nc);	   
	  nc->deref ();
	  c->deref ();
	  nb_values--;
	}
    }
  else
    {
      phi->deref ();
    }

  pop ();
  var->deref ();
  if (debug_traces)
    END_DBG_BLOCK ();

  return result;
}

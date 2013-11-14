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
#include <cassert>

using namespace std;

static const std::string PROP_PREFIX = "kernel.expr.solver";
const std::string ExprSolver::SOLVER_NAME_PROP = PROP_PREFIX + ".name";
const std::string ExprSolver::DEBUG_TRACES_PROP = PROP_PREFIX + ".debug-traces";



struct SolverModule 
{
  void (*init) (const ConfigTable &cfg);
  const string & (*ident) ();
  ExprSolver *(*instantiate)(const MicrocodeArchitecture *mca);
  void (*terminate) ();
};

#define SOLVER_MODULE(C) \
  { &(C :: init), &(C :: ident), &(C :: create), &(C ::terminate) }

static SolverModule modules[] = {
  SOLVER_MODULE (ExprProcessSolver)  
};

static size_t nb_modules = sizeof (modules)/sizeof(modules[0]);

static SolverModule *default_solver = NULL;
bool ExprSolver::debug_traces = false;


void 
ExprSolver::init (const ConfigTable &cfg)
  throw (UnknownSolverException)
{
  string sname = cfg.get (SOLVER_NAME_PROP);
  debug_traces = cfg.get_boolean (DEBUG_TRACES_PROP);

  for (size_t i = 0; i < nb_modules; i++)
    {
      modules[i].init (cfg);
      if (modules[i].ident () == sname)
	default_solver = &modules[i];
    }
  if (sname != "" && default_solver == NULL)
    throw UnknownSolverException ("can not find solver '" + sname + "'.");

}

void 
ExprSolver::terminate ()
{
  default_solver = NULL;
  for (size_t i = 0; i < nb_modules; i++)
    modules[i].terminate ();
}
  
ExprSolver *
ExprSolver::create_default_solver (const MicrocodeArchitecture *mca)
  throw (UnexpectedResponseException, UnknownSolverException)
{  
  if (default_solver == NULL)
    throw UnknownSolverException ("no default solver has been specified.");

  return default_solver->instantiate (mca);
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
      while (nb_values > 0 && check_sat () == SAT)
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

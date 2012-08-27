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
#include "ExprProcessSolver.hh"

#include <io/expressions/smtlib-writer.hh>
#include <kernel/expressions/exprutils.hh>
#include <utils/Log.hh>

#include <tr1/unordered_set>
#include <ext/stdio_filebuf.h>
#include <csignal>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cassert>

#include <unistd.h>

using namespace std;
using namespace std::tr1;
using namespace exprutils;

#define MEMORY_VAR "MEM"

typedef __gnu_cxx::stdio_filebuf<char> file_buffer;

static bool
s_create_pipe (const std::string &cmd, const vector<string> &args,
	       FILE **rwstreams);

ExprProcessSolver::ExprProcessSolver (const MicrocodeArchitecture *mca, 
				      const string &cmd, 
				      istream *r, ostream *w)
  : ExprSolver (mca), command (cmd), in (r), out (w)
{
}

ExprProcessSolver * 
ExprProcessSolver::create (const MicrocodeArchitecture *mca, 
			   const std::string &cmd, 
			   const std::vector<std::string> &args)
  throw (UnexpectedResponseException, UnknownSolverException)
{
  FILE *pipestreams[2] = {NULL, NULL};
  ExprProcessSolver *result = NULL;

  if (s_create_pipe (cmd, args, pipestreams))
    {
      istream *i = new istream (new file_buffer (pipestreams[0], 
						 std::ios_base::in));
      ostream *o = new ostream (new file_buffer (pipestreams[1], 
						 std::ios_base::out));      
      result = new ExprProcessSolver (mca, cmd, i, o);
      if (! result->init ())
	{
	  delete (result);
	  result = NULL;
	}
    }

  return result;      
}

ExprProcessSolver::~ExprProcessSolver ()
{
}

ExprSolver::Result 
ExprProcessSolver::check_sat (const Expr *e) 
  throw (UnexpectedResponseException)
{
  ExprSolver::Result result = ExprSolver::UNSAT;
    
  declare_variable (e);
  
  if (log::debug_is_on)
    {
      ostringstream oss;
      
      oss << "(assert ";       
      smtlib_writer (oss, e, MEMORY_VAR, 
		     8 * mca->get_reference_arch ()->address_range);
      oss << ") " << endl;
      log::debug << "SMT command " << oss.str () << endl;
      *out << oss.str () << endl;
    }
  else
    {
      *out << "(assert "; 	  
      smtlib_writer (*out, e, MEMORY_VAR, 
		     8 * mca->get_reference_arch ()->address_range);
      *out << ") " << endl;
    }

  if (read_status ())
    {
      string res = exec_command ("(check-sat)");
      if (res == "sat") 
	result = ExprSolver::SAT;
      else if (res == "unsat") 
	result = ExprSolver::UNSAT;
      else if (res == "unknown") 
	result = ExprSolver::UNKNOWN;
      else 
	throw UnexpectedResponseException ("check-sat: " + res);
    }
  
  return result;
}

bool 
ExprProcessSolver::init ()
{
  return write_header ();
}

string 
ExprProcessSolver::exec_command (const std::string &s)
{
  return exec_command (s.c_str ());
}

string 
ExprProcessSolver::exec_command (const char *s)
{
  log::debug << "SMT command " << s << endl;
  *out << s << endl;
  out->flush ();

  return get_result ();
}

bool 
ExprProcessSolver::send_command (const char *s)
{
  log::debug << "SMT command " << s << endl;
  *out << s << endl;
  out->flush ();

  return read_status ();
}

bool 
ExprProcessSolver::send_command (const std::string &s)
{
  return send_command (s.c_str ());
}

bool 
ExprProcessSolver::write_header ()
{
  return (send_command ("(set-option :print-success true) ") &&
	  send_command ("(set-logic QF_AUFBV) "));
}

bool 
ExprProcessSolver::read_status ()
{
  string st = get_result ();

  if (st == "success")
    return true;
  else if (st == "failure")
    return false;

  throw UnexpectedResponseException ("read-status: " + st);
}

bool 
ExprProcessSolver::declare_variable (const Expr *e)
{
  typedef unordered_set<const Expr *> ExprSet;
  const Architecture *arch = mca->get_reference_arch ();
  {
    ostringstream oss;

    oss << "(declare-fun " << MEMORY_VAR << " () (Array "
       << "(_ BitVec " << (8 * arch->address_range) << " ) "
       << "(_ BitVec 8 ) "
	<< ")) ";
    if (! send_command (oss.str ()))      
      return false;
  }

  ExprSet vars = collect_subterms_of_type<ExprSet, Variable> (e, true);

  for (ExprSet::const_iterator i = vars.begin (); i != vars.end (); i++)
    {
      const Variable *v = dynamic_cast<const Variable *>(*i);
      ostringstream oss;
      assert (v != NULL);
      oss << "(declare-fun " << v->get_id () << " () "
	  << "(_ BitVec " << v->get_bv_size () << ") " 
	  << ") " << endl;	  
      if (! send_command (oss.str ()))      
	return false;
    }

  vars = collect_subterms_of_type<ExprSet, RegisterExpr> (e, true);
  unordered_set<const RegisterDesc *> cache;
  for (ExprSet::const_iterator i = vars.begin (); i != vars.end (); i++)
    {
      const RegisterExpr *reg = dynamic_cast<const RegisterExpr *>(*i);

      assert (reg != NULL);

      const RegisterDesc *regdesc = reg->get_descriptor ();
      
      if (! (cache.find (regdesc) == cache.end ()))
	continue;
      
      assert (! regdesc->is_alias ());
      ostringstream oss;
      oss << "(declare-fun " << regdesc->get_label () << " () "
	  << "(_ BitVec " << regdesc->get_register_size () << ") " 
	  << ") " << endl;
      if (! send_command (oss.str ()))      
	return false;
      cache.insert (regdesc);
    }
  return true;
}

string 
ExprProcessSolver::get_result ()
{
  string result;

  getline (*in, result);
  return result;
}

void 
ExprProcessSolver::push ()
  throw (UnexpectedResponseException)
{
  if (! send_command ("(push 1)"))
    throw UnexpectedResponseException ("push: failure");
}

void 
ExprProcessSolver::pop ()
  throw (UnexpectedResponseException)
{
  if (! send_command ("(pop 1)"))
    throw UnexpectedResponseException ("pop: failure");
}

Constant * 
ExprProcessSolver::get_value_of (const Expr *)
  throw (UnexpectedResponseException)
{
  throw UnexpectedResponseException("get_value_of: not implemented");
}


static bool 
s_create_pipe (const std::string &cmd, const vector<string> &args,
	       FILE **rwstreams)
{
  int parent_child_pipe[2];
  int child_parent_pipe[2];

  if (pipe (parent_child_pipe) == -1 || pipe (child_parent_pipe) == -1)
    {
      perror ("can't create pipe to solver");
      return false;
    }
  
  pid_t cpid = fork();
  if (cpid == -1) 
    {
      perror ("fork to solver");
      return false;
    }

  if (cpid == 0) 
    {
      int fid;

      /* Child code */
      close (parent_child_pipe[1]); // close write part of P --> C
      close (child_parent_pipe[0]); // close read part of C --> P      
      close (0); // close stdin
      fid = dup (parent_child_pipe[0]); // associate read part of P --> C to stdin
      if (fid < 0)
	{
	  perror("dup stdin pipe");
	  return false;
	}

      close (1); // close stdout
      fid = dup (child_parent_pipe[1]); // associate write part of C --> P to stdout
      if (fid < 0)
	{
	  perror("dup stdout pipe");
	  return false;
	}

      close (parent_child_pipe[0]); // close useless fd
      close (child_parent_pipe[1]); // close useless fd
      int nb_args = args.size ();
      char **tmp = new char *[nb_args + 2];
      tmp[0] = ::strdup (cmd.c_str ());
      for (int i = 0; i < nb_args; i++)
	tmp[i + 1] = ::strdup (args[i].c_str ());
      tmp[nb_args + 1] = NULL;
      if (execvp (cmd.c_str (), tmp) < 0)
	kill (getppid (), SIGCHLD);
    } 
  else 
    {
      /* Parent code */
      close (parent_child_pipe[0]); // close read part of P --> C
      close (child_parent_pipe[1]); // close write part of C --> P
      rwstreams[0] = fdopen (child_parent_pipe[0], "r");
      rwstreams[1] = fdopen (parent_child_pipe[1], "w");
    }

  return true;
}


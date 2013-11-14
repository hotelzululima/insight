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
#include <io/expressions/expr-parser.hh>
#include <utils/logs.hh>

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
typedef ExprSolver::UnexpectedResponseException UnexpectedResponseException;

#define MEMORY_VAR "MEM"

typedef __gnu_cxx::stdio_filebuf<char> file_buffer;

static const std::string SOLVER_NAME = "process";

static const std::string PROP_PREFIX = "kernel.expr.solver." + SOLVER_NAME;
const std::string ExprProcessSolver::COMMAND_PROP = PROP_PREFIX + ".command";
const std::string ExprProcessSolver::ARGS_PROP = PROP_PREFIX + ".args";

static string default_solver_command;
static vector<string> default_solver_args;

const string &
ExprProcessSolver::ident ()
{
  return SOLVER_NAME;
}

void 
ExprProcessSolver::init (const ConfigTable &cfg)
{
  default_solver_command = cfg.get (COMMAND_PROP);
  string args = cfg.get (ARGS_PROP);

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
}

void 
ExprProcessSolver::terminate ()
{
  default_solver_command = "";
  default_solver_args = vector<string>();
}

static bool
s_create_pipe (const std::string &cmd, const vector<string> &args,
	       FILE **rwstreams, pid_t *p_cpid);

ExprProcessSolver::ExprProcessSolver (const MicrocodeArchitecture *mca, 
				      const string &cmd, 
				      istream *r, ostream *w, pid_t cpid)
  : ExprSolver (mca), command (cmd), in (r), out (w), childpid (cpid)
{
}

ExprSolver * 
ExprProcessSolver::create (const MicrocodeArchitecture *mca)
  throw (UnexpectedResponseException, UnknownSolverException)
{
  pid_t cpid;
  FILE *pipestreams[2] = {NULL, NULL};
  ExprProcessSolver *result = NULL;
  const std::string &cmd = default_solver_command;
  const std::vector<std::string> &args = default_solver_args;

  if (s_create_pipe (cmd, args, pipestreams, &cpid))
    {
      istream *i = new istream (new file_buffer (pipestreams[0], 
						 std::ios_base::in));
      ostream *o = new ostream (new file_buffer (pipestreams[1], 
						 std::ios_base::out));      
      result = new ExprProcessSolver (mca, cmd, i, o, cpid);
      try
	{
	  if (! result->init ())
	    {
	      delete (result);
	      result = NULL;
	    }
	}
      catch (UnexpectedResponseException &e)
	{
	  delete (result);
	  result = NULL;
	}
    }

  return result;      
}

ExprProcessSolver::~ExprProcessSolver ()
{
  fclose (((file_buffer *) in->rdbuf ())->file ());
  fclose (((file_buffer *) out->rdbuf ())->file ());
  kill (childpid, SIGTERM);
  
  delete in->rdbuf ();
  delete out->rdbuf ();
  delete in;
  delete out;
}

ExprSolver::Result 
ExprProcessSolver::check_sat (const Expr *e, bool preserve) 
  throw (UnexpectedResponseException)
{
  if (debug_traces)
    BEGIN_DBG_BLOCK ("check_sat : " + e->to_string ());
  if (preserve)
    push ();
  ExprSolver::Result result = ExprSolver::UNKNOWN;
    
  declare_variable (e);

  if (debug_traces)
    {
      logs::debug << "(assert ";
      smtlib_writer (logs::debug, e, MEMORY_VAR, 
		     mca->get_address_size (), 
		     mca->get_endian (), true);
      logs::debug << ") " << endl;
    }
  *out << "(assert ";  
  smtlib_writer (*out, e, MEMORY_VAR, mca->get_address_size (), 
		 mca->get_endian (), true);
  *out << ") " << endl;

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
      if (debug_traces)
	logs::debug << res << endl;
    }
  if (preserve)
    pop ();

  if (debug_traces)
    END_DBG_BLOCK ();

  return result;
}

void 
ExprProcessSolver::add_assertion (const Expr *e)
  throw (UnexpectedResponseException) 
{
  if (debug_traces)
    {
      logs::debug << "(assert ";
      smtlib_writer (logs::debug, e, MEMORY_VAR, 
		     mca->get_address_size (), 
		     mca->get_endian (), true);
      logs::debug << ") " << endl;
    }

  *out << "(assert ";  
  smtlib_writer (*out, e, MEMORY_VAR, mca->get_address_size (), 
		 mca->get_endian (), true);
  *out << ") " << endl;

  if (! read_status ())
    throw UnexpectedResponseException ("error while adding assertion" + 
				       e->to_string ());
}

ExprSolver::Result 
ExprProcessSolver::check_sat ()
  throw (UnexpectedResponseException)
{
  ExprSolver::Result result = UNKNOWN;

  string res = exec_command ("(check-sat)");
  if (res == "sat") 
    result = ExprSolver::SAT;
  else if (res == "unsat") 
    result = ExprSolver::UNSAT;
  else if (res == "unknown") 
    result = ExprSolver::UNKNOWN;
  else 
    throw UnexpectedResponseException ("check-sat: " + res);

  return result;
}

bool
ExprProcessSolver::init () throw (UnexpectedResponseException)
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
  if (debug_traces)
    logs::debug << s << endl;
  *out << s << endl;
  out->flush ();

  return get_result ();
}

bool 
ExprProcessSolver::send_command (const char *s, bool allow_unsupported)
{
  if (debug_traces)
    logs::debug << s << endl;
  *out << s << endl;
  out->flush ();

  return read_status (allow_unsupported);
}

bool 
ExprProcessSolver::send_command (const std::string &s, bool allow_unsupported)
{
  return send_command (s.c_str (), allow_unsupported);
}

bool
ExprProcessSolver::write_header ()
  throw (UnexpectedResponseException)
{
  return (send_command ("(set-option :print-success true) ") &&
	  send_command ("(set-option :produce-models true) ") &&
	  send_command ("(set-option :interactive-mode false) ", true) &&
	  send_command ("(set-logic QF_AUFBV) "));
}

bool 
ExprProcessSolver::read_status (bool allow_unsupported)
  throw (UnexpectedResponseException)
{
  string st = get_result ();

  if (st == "success" || (st == "unsupported" && allow_unsupported))
    return true;
  else if (st == "failure")
    return false;

  throw UnexpectedResponseException ("read-status: " + st);
}

bool 
ExprProcessSolver::declare_variable (const Expr *e)
{
  typedef unordered_set<const Expr *> ExprSet;
  {
    ostringstream oss;

    oss << "(declare-fun " << MEMORY_VAR << " () (Array "
	<< "(_ BitVec " << mca->get_address_size () << " ) "
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
	  << ") ";	  
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
	  << ") ";
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

static bool
s_parse_result_line (const string &line, vector< pair<string,string> > &result)
{
  list<int> pos;
  string::const_iterator c = line.begin ();
  enum { RFP, RSP, RE, RSE, RPE, RPV, RV, RCP } st = RFP;
  pair<string,string> couple;
  string::size_type i;

  for (i = 0; i < line.size (); i++, c++)
    {
      if (st == RFP)
	{
	  if (*c == '(') 
	    st = RSP;
	  else if (! isspace (*c))
	    return false;	    
	}	 
      else if (st == RSP)
	{
	  if (*c == '(') 
	    st = RE;
	  else if (*c == ')')
	    break;
	  else if (! isspace (*c))
	    return false;	    
	}
      else if (st == RE)
	{
	  if (isspace (*c))
	    continue;
	  if (*c == ')')
	    return false;
	  pos.push_front (i);
	  st = (*c == '(')  ? RPE : RSE;
	}
      else if (st == RSE)
	{
	  if (*c == '(' || *c == ')')
	    return false;
	  if (isspace (*c))
	    {
	      int spos = pos.front ();
	      pos.pop_front();
	      couple.first = line.substr (spos, i - spos);
	      st = RV;
	    }
	}
      else if (st == RPE)
	{
	  if (*c == '(')
	    pos.push_front (i);
	  else if (*c == ')')
	    {
	      int spos = pos.front ();
	      pos.pop_front();
	      if (pos.empty ())
		{
		  st = RV;
		  couple.first = line.substr (spos, i - spos + 1);  
		}
	    }
	}
      else if (st == RV)
	{
	  if (pos.empty ())
	    {
	      if (*c == '#' || *c == '(' || isalnum (*c))
		{
		  pos.push_front (i);
		  if (*c == '(')
		    st = RPV;
		}
	      else if (! isspace (*c))
		return false;
	    }
	  else if (isspace (*c) || *c == ')')
	    {
	      int spos = pos.front ();
	      pos.pop_front();
	      couple.second = line.substr (spos, i - spos);
	      result.push_back (couple);
	      st = (*c == ')') ? RSP : RCP;
	    }
	  else if (*c == '(')
	    return false;
	}
      else if (st == RPV)
	{
	  if (*c == '(')
	    pos.push_front (i);
	  else if (*c == ')')
	    {
	      int spos = pos.front ();
	      pos.pop_front();
	      if (pos.empty ())
		{
		  couple.second = line.substr (spos, i - spos + 1);
		  result.push_back (couple);
		  st = RCP;
		}
	    }
	}
      else if (st == RCP)
	{
	  if (*c == ')')
	    st = RSP;
	  else if (! isspace (*c))
	    return false;
	}
    }

  if (st != RSP || i != line.size () - 1)
    result.clear ();

  return ! result.empty ();
}

Constant * 
ExprProcessSolver::get_value_of (const Expr *e)
  throw (UnexpectedResponseException)
{
  Constant *result = NULL;
  ostringstream oss;
  oss << "(get-value (";
  smtlib_writer (oss, e, MEMORY_VAR, mca->get_address_size (), 
		 mca->get_endian (), false);
  oss << "))";

  string res = exec_command (oss.str ());
  vector< pair<string,string> > couples;
  if (s_parse_result_line (res, couples))
    {
      if (couples.size () > 1)
	throw UnexpectedResponseException ("get_value_of: " + res);
      string value = couples[0].second;
      if (value[0] == '#')
	{
	  if (value[1] == 'x' || value[1] == 'b')
	    {
	      value[0] = '0';
	      Constant *c = (Constant *) expr_parser (value, mca);
	      assert (c->is_Constant ());
	      result = Constant::create (c->get_val (), 0, 
					 e->get_bv_size ());
	      c->deref ();
	    }
	  else
	    {
	      throw UnexpectedResponseException ("get_value_of: " + res);
	    }
	}
      else if (value == "false")
	result = Constant::False ();
      else if (value == "true")
	result = Constant::True ();
      else if (value.find ("(_ bv") == 0)
	{
	  string::size_type spi = value.find (' ', 5);
	  string val = value.substr (5, spi - 5);
	  long ival = strtoll (val.c_str (), NULL, 0);
	  string szstr = value.substr (spi + 1, value.find (')') - spi - 1);
	  long isz = strtoll (szstr.c_str(), NULL, 0);
	  result = Constant::create (ival, 0, isz);
	}
      else
	throw UnexpectedResponseException ("get_value_of: " + res);
    }

  if (result == NULL)
    throw UnexpectedResponseException ("get_value_of: " + res);
  return result;
}


static bool 
s_create_pipe (const std::string &cmd, const vector<string> &args,
	       FILE **rwstreams, pid_t *p_cpid)
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
      setpgid (0, 0);

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
      *p_cpid = cpid;
      close (parent_child_pipe[0]); // close read part of P --> C
      close (child_parent_pipe[1]); // close write part of C --> P
      rwstreams[0] = fdopen (child_parent_pipe[0], "r");
      rwstreams[1] = fdopen (parent_child_pipe[1], "w");
    }

  return true;
}


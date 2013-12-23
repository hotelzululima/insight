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
#include "ExprMathsatSolver.hh"

#if INTEGRATED_MATHSAT_SOLVER
#include <kernel/expressions/ExprVisitor.hh>
#include <kernel/expressions/exprutils.hh>
#include <utils/logs.hh>
#include <vector>
#include <map>
#include <tr1/unordered_set>
#include <iomanip>
#include <cassert>

using namespace std;
using namespace std::tr1;
using namespace exprutils;

static const std::string MEMORY_VAR = "MEM";
static const std::string SOLVER_NAME = "mathsat";

static const std::string PROP_PREFIX = "kernel.expr.solver." + SOLVER_NAME;
static msat_config MATHSAT_CONFIG;

class Expr2MathsatVisitor : public ConstExprVisitor 
{
  msat_env &env;
  const string &memvar;
  int addrsize;
  Architecture::endianness_t endian;
  msat_term result;
  map<string,msat_decl> variables;

  typedef msat_term (*binary_operator) (msat_env, msat_term, msat_term);
  typedef msat_term (*binary_operator_int) (msat_env, size_t, msat_term);
public:


  Expr2MathsatVisitor (msat_env &me, const string &mv, int bpa, 
		       Architecture::endianness_t e)
    : ConstExprVisitor (), env (me), memvar (mv), addrsize (bpa), endian (e) {}

  ~Expr2MathsatVisitor () { }


  virtual msat_term make_constant (word_t val, int bv_size) {    
    ostringstream oss;
    int base;
    if (bv_size % 8 == 0)
      {
	base = 16;
	oss << setw (bv_size / 4) << setfill ('0') << hex << val;
      }
    else
      {
	int sz = bv_size;
	base = 2;
	while (sz--)
	  oss << dec << (0x1 & (val >> sz));
      }
    string str = oss.str ();
    const char *s = str .c_str ();
    msat_term result = msat_make_bv_number (env, s, bv_size, base);

    return result;
  }

  virtual void visit (const Constant *c) {    
    result = make_constant (c->get_val (), c->get_bv_size ());
  }

  virtual void visit (const RandomValue *) {
    logs::error << "RandomValue should not be sent to SMT solver." << endl;
    abort ();
  }

  virtual void visit (const Variable *v) {
    msat_decl decl = msat_find_decl (env, v->get_id ().c_str ());
    assert (!MSAT_ERROR_DECL (decl));
    result = msat_make_constant (env, decl);
  }

  void extract_bv_window (const Expr *e) {
    size_t msb = e->get_bv_offset () + e->get_bv_size () - 1;
    size_t lsb = e->get_bv_offset ();

    result = msat_make_bv_extract (env, msb, lsb, result);
  }

  void extend_bv_window (int bv_size, const Expr *arg, bool with_sign) {
    int ext = (bv_size - arg->get_bv_size ());
    if (ext <= 0)
      return;

    if (with_sign)
      result = msat_make_bv_sext (env, ext, result);
    else 
      result = msat_make_bv_zext (env, ext, result);
  }

  void extend_bv_window (const Expr *e, const Expr *arg, bool with_sign) {
    extend_bv_window (e->get_bv_size (), arg, with_sign);
  }

  bool has_boolean_bv (const Expr *e) {
    return e->get_bv_offset () == 0 && e->get_bv_size () == 1;
  }

  void output_boolean (const Expr *e) {
    e->acceptVisitor (this);

    msat_term cst;

    if (e->get_bv_size () == 1)
      cst = make_constant (1, 1);
    else 
      cst = make_constant (0, e->get_bv_size ());

    result = msat_make_equal (env, result, cst);
    if (e->get_bv_size () > 1)
      result = msat_make_not (env, result);
  }

  virtual void visit (const UnaryApp *e) {
    e->get_arg1 ()->acceptVisitor (this);

    if (e->get_op () == BV_OP_NOT)
      result = msat_make_bv_not (env, result);
    else
      {
	assert (e->get_op () == BV_OP_NEG);
	result = msat_make_bv_neg (env, result);
	extend_bv_window (e, e->get_arg1 (), true);
      }

    if (e->get_bv_offset () != 0 || 
	e->get_bv_size () != e->get_arg1 ()->get_bv_size ())
      extract_bv_window (e);
    if (MSAT_ERROR_TERM (result))
      {
	logs::error << "MathSat: " 
		    << msat_last_error_message (env) << "." << endl;
	abort ();
      }
  }

  bool need_extract (const BinaryApp *e) {
    bool result = true;

    if (e->get_op () == BV_OP_CONCAT)
      {
	result = (e->get_bv_offset () != 0 ||
		  (e->get_bv_size () < e->get_arg1 ()->get_bv_size () + 
		   e->get_arg2 ()->get_bv_size ()));
      }
    else if (e->get_op () != BV_OP_EXTEND_U && e->get_op () != BV_OP_EXTEND_S)
      result = (e->get_bv_offset () != 0 ||
		e->get_bv_size () != e->get_arg1 ()->get_bv_size ());
    return result;
  }

  static msat_term msat_make_bv_neq (msat_env e, msat_term t1, msat_term t2) {
    return msat_make_not (e, msat_make_equal (e, t1, t2));
  }

  static msat_term msat_make_bv_uge (msat_env e, msat_term t1, msat_term t2) {
    return msat_make_not (e, msat_make_bv_ult (e, t1, t2));
  }

  static msat_term msat_make_bv_ugt (msat_env e, msat_term t1, msat_term t2) {
    return msat_make_not (e, msat_make_bv_uleq (e, t1, t2));
  }

  static msat_term msat_make_bv_sge (msat_env e, msat_term t1, msat_term t2) {
    return msat_make_not (e, msat_make_bv_slt (e, t1, t2));
  }

  static msat_term msat_make_bv_sgt (msat_env e, msat_term t1, msat_term t2) {
    return msat_make_not (e, msat_make_bv_sleq (e, t1, t2));
  }
    
  virtual void visit (const BinaryApp *e) {
    binary_operator mop;
    binary_operator_int mopi;
    BinaryOp op = e->get_op ();
    bool extract = need_extract (e); 	  	
    bool extend = false;
    bool ite = false;
    bool with_sign = false;
    msat_term arg[3];
    switch (op)
      {
      case BV_OP_AND: 
	mop = msat_make_bv_and;	
	goto output_binary_1;
      case BV_OP_OR:
	mop = msat_make_bv_or;
	goto output_binary_1;
      case BV_OP_MUL_S: 
	with_sign = true;
      case BV_OP_MUL_U: 
	mop = msat_make_bv_times; extend = true; 
	goto output_binary_1;
      case BV_OP_ADD: 
	mop = msat_make_bv_plus; extend = true; 
	goto output_binary_1;
      case BV_OP_SUB: 
	mop = msat_make_bv_minus; extend = true; 
	goto output_binary_1;
      case BV_OP_LSH: 
	mop = msat_make_bv_lshl; 
	goto output_binary_1;
      case BV_OP_RSH_U: 
	mop = msat_make_bv_lshr; 
	goto output_binary_1;
      case BV_OP_RSH_S: 
	mop = msat_make_bv_ashr; 
	goto output_binary_1;
      case BV_OP_MODULO:
	mop = msat_make_bv_urem; 
	goto output_binary_1; // to be fix with signed mod.
      case BV_OP_DIV_S: 
	mop = msat_make_bv_sdiv; 
	goto output_binary_1;
      case BV_OP_DIV_U: 
	mop = msat_make_bv_udiv; 
	goto output_binary_1;
      case BV_OP_CONCAT: 
	mop = msat_make_bv_concat; 
	goto output_binary_1;
      case BV_OP_XOR: 
	mop = msat_make_bv_xor; 
	goto output_binary_1;


      case BV_OP_NEQ: 
	mop = msat_make_bv_neq;
	extract = false; 
	ite = true;
	goto output_binary_1;

      case BV_OP_EQ: 
	mop = msat_make_equal;
	extract = false; 
	ite = true;
	goto output_binary_1;

      case BV_OP_GEQ_U: 
	mop = msat_make_bv_uge;
	extract = false; 
	ite = true;
	goto output_binary_1;
      case BV_OP_GEQ_S: 
	ite = true;
	mop = msat_make_bv_sge;
	extract = false; 
	goto output_binary_1;
      case BV_OP_LT_U: 
	ite = true;
	mop = msat_make_bv_ult;
	extract = false; 
	goto output_binary_1;
      case BV_OP_LT_S: 
	mop = msat_make_bv_slt;
	extract = false; 
	ite = true;
	goto output_binary_1;
      case BV_OP_GT_U: 
	mop = msat_make_bv_ugt;
	extract = false; 
	ite = true;
	goto output_binary_1;
      case BV_OP_GT_S: 
	mop = msat_make_bv_sgt;
	extract = false; 
	ite = true;
	goto output_binary_1;
      case BV_OP_LEQ_U: 
	mop = msat_make_bv_uleq;
	extract = false; 
	ite = true;
	goto output_binary_1;
      case BV_OP_LEQ_S: 
	mop = msat_make_bv_sleq;
	extract = false; 
	ite = true;
	goto output_binary_1;

      output_binary_1:
	e->get_arg1 ()->acceptVisitor (this);
	if (extend)
	  extend_bv_window (e, e->get_arg1 (), with_sign);
	arg[0] = result;
	
	e->get_arg2 ()->acceptVisitor (this);
	if (extend)
	  extend_bv_window (e, e->get_arg2 (), with_sign);
	arg[1] = result;
	result = mop (env, arg[0], arg[1]);

	if (extract)
	  extract_bv_window (e);
	if (ite)
	  {
	    msat_term F = make_constant (0, 1);
	    msat_term T = make_constant (1, 1);
	    result = msat_make_term_ite (env, result, T, F);
	  }
 	break;

      case BV_OP_ROR: 
	mopi = msat_make_bv_ror;
	goto output_binary_2;
      case BV_OP_ROL: 
	mopi = msat_make_bv_rol;
	goto output_binary_2;
      case BV_OP_EXTEND_U: 
	mopi = msat_make_bv_zext;
	goto output_binary_2;
      case BV_OP_EXTEND_S: 
	mopi = msat_make_bv_sext;
	goto output_binary_2;
      output_binary_2:
	{
	  Constant *c = dynamic_cast <Constant *> (e->get_arg2 ());
	  assert (c != NULL);
	  size_t val = c->get_val ();
	  if (op == BV_OP_EXTEND_U || op == BV_OP_EXTEND_S)
	    val = c->get_val () - e->get_arg1 ()->get_bv_size ();
	  e->get_arg1 ()->acceptVisitor (this);
	  result = mopi (env, val, result);
	}

	if (extract)
	  extract_bv_window (e);
	break;

      case BV_OP_POW:
      default:
	assert (op != BV_OP_POW);
      }
    if (MSAT_ERROR_TERM (result))
      {
	logs::error << "MathSat: " 
		    << msat_last_error_message (env) << "." << endl;
	abort ();
      }
  }

  virtual void visit (const TernaryApp *e) {
    assert (e->get_op () == BV_OP_EXTRACT);
    Constant *expr_offset = dynamic_cast <Constant *> (e->get_arg2 ());
    Constant *expr_size = dynamic_cast <Constant *> (e->get_arg3 ());

    assert (expr_offset != NULL || expr_size != NULL);
    constant_t offset = expr_offset->get_val ();
    constant_t size = expr_size->get_val ();

    e->get_arg1 ()->acceptVisitor (this);
    result = msat_make_bv_extract (env, (offset + size - 1), offset, result);

    if (offset != e->get_bv_offset () || size != e->get_bv_size ())
      extract_bv_window (e);
  }

  virtual string stringof (const msat_term &t) { 
    char *s = msat_to_smtlib2_term (env, t); 
    string res (s);
    msat_free (s);
    return res;
  }

  virtual void visit (const MemCell *e) {
    if (e->get_bv_size () == 8 && e->get_bv_offset () == 0)
      {
	// to be fixed !!!

	e->get_addr ()->acceptVisitor (this);

	extend_bv_window (addrsize, e->get_addr (), false);

	msat_decl memdecl = msat_find_decl (env, memvar.c_str ());
	assert (!MSAT_ERROR_DECL (memdecl));
	msat_term mem = msat_make_constant (env, memdecl);
	result = msat_make_array_read (env, mem, result);
	if (MSAT_ERROR_TERM (result))
	  {
	    logs::error<< msat_last_error_message (env) << endl;
	  }
      }
    else
      {
	int nb_bytes = (e->get_bv_offset () + e->get_bv_size ()) / 8;
	if (e->get_bv_size () % 8 != 0)
	  nb_bytes++;	
	Expr *addr = e->get_addr ()->ref ();
	Expr *bv = MemCell::create (addr->ref (), 0, 8);

	for (int i = 1; i < nb_bytes; i++)
	  {
	    Expr *a = BinaryApp::create (BV_OP_ADD, addr->ref (), i);
	    Expr *byte = MemCell::create (a, 0, 8);
	    Expr *tmp;
	    Expr *aux[2];
	    if (endian == Architecture::LittleEndian)
	      {
		aux[0] = byte;
		aux[1] = bv;
	      }
	    else
	      {
		aux[0] = bv;
		aux[1] = byte;
	      }
	    tmp = BinaryApp::create (BV_OP_CONCAT, aux[0], aux[1], 
				     0, 8 * (i + 1));
	    bv = tmp;
	  }
	addr->deref ();
	bv = Expr::createExtract (bv, e->get_bv_offset (), e->get_bv_size ());
	bv->acceptVisitor (this);
	bv->deref ();
      }
  }

  virtual void visit (const RegisterExpr *e) {
    const RegisterDesc *rd = e->get_descriptor ();
    
    msat_decl decl = msat_find_decl (env, rd->get_label ().c_str ());
    assert (!MSAT_ERROR_DECL (decl));
    result = msat_make_constant (env, decl);
    
    if (! (e->get_bv_offset () == 0 && 
	   e->get_bv_size () == rd->get_register_size ()))
      extract_bv_window (e);
  }

  virtual void visit (const QuantifiedExpr *) {
    abort ();
  }  

  static msat_term 
  translate (msat_env &env, const Expr *ep,
	     const string &memvar, int addrsize, 
	     Architecture::endianness_t endian, bool as_boolean) {
    Expr2MathsatVisitor e2m (env, memvar, addrsize, endian);
    Expr *e = ep->ref ();
    exprutils::simplify (&e);

    if (as_boolean)
      e2m.output_boolean (e); 
    else
      e->acceptVisitor (&e2m);
    e->deref ();
    
    return e2m.result;    
  }
};


ExprMathsatSolver::ExprMathsatSolver (const MicrocodeArchitecture *mca)
  : ExprSolver (mca), envstack ()
{
  msat_env env = msat_create_env (MATHSAT_CONFIG);
  envstack.push (env);
}

ExprMathsatSolver::~ExprMathsatSolver ()
{
  msat_destroy_env (envstack.top ());  
}

const std::string &
ExprMathsatSolver::ident ()
{
  return SOLVER_NAME;
}

void 
ExprMathsatSolver::init (const ConfigTable &)
  throw (UnknownSolverException)
{
  MATHSAT_CONFIG = msat_create_default_config ("QF_AUFBV");

  /* Check msat_create_default_config() result */
  if (MSAT_ERROR_CONFIG(MATHSAT_CONFIG) == true)
    throw UnknownSolverException ("failed creating MathSAT default config");

  msat_set_option(MATHSAT_CONFIG, "model_generation", "true");
  msat_set_option(MATHSAT_CONFIG, "proof_generation", "true");
  msat_set_option(MATHSAT_CONFIG, "bool_model_generation", "true");

  if (debug_traces)
    {
      msat_set_option(MATHSAT_CONFIG, "debug.api_call_trace", "3");
      msat_set_option(MATHSAT_CONFIG, "verbosity", "2");
    }
}

void 
ExprMathsatSolver::terminate ()
{
  msat_destroy_config (MATHSAT_CONFIG);
}

ExprSolver *
ExprMathsatSolver::create (const MicrocodeArchitecture *mca)
  throw (UnexpectedResponseException, UnknownSolverException)
{
  return new ExprMathsatSolver (mca);
}

void 
ExprMathsatSolver::add_assertion (const Expr *e)
  throw (UnexpectedResponseException)
{
  msat_env env = envstack.top ();
  msat_term formula = 
    Expr2MathsatVisitor::translate (env, e, MEMORY_VAR, 
				    mca->get_address_size (), 
				    mca->get_endian (), true);

  if (msat_assert_formula (env, formula) != 0)
    throw UnexpectedResponseException ("error while adding assertion" + 
				       e->to_string ());
  if (debug_traces)
    {
      char *smtlib2expr = msat_to_smtlib2_term (env, formula);
      logs::debug << "(assert " << smtlib2expr << ") " << endl;
      msat_free (smtlib2expr);
    }
}

static int
s_declare_variables (const Expr *e, msat_env &env, int addrsize)
{
  typedef unordered_set<const Expr *> ExprSet;

  msat_type byte = msat_get_bv_type (env, 8);
  msat_type memaddr = msat_get_bv_type (env, addrsize);
  msat_type memory = msat_get_array_type (env, memaddr, byte);
  msat_decl decl = msat_declare_function (env, MEMORY_VAR.c_str (), memory);
  assert (! MSAT_ERROR_DECL (decl));

  ExprSet vars = collect_subterms_of_type<ExprSet, Variable> (e, true);

  for (ExprSet::const_iterator i = vars.begin (); i != vars.end (); i++)
    {
      const Variable *v = dynamic_cast<const Variable *>(*i);
      assert (v != NULL);

      const char *vname = v->get_id ().c_str ();
      decl = msat_find_decl (env, vname);
      if (! MSAT_ERROR_DECL (decl))
	{
	  logs::error << 	msat_decl_repr (decl) << endl;
	}

      msat_type vtype = msat_get_bv_type (env, v->get_bv_size ());
      decl = msat_declare_function (env, vname, vtype);
      if (MSAT_ERROR_DECL (decl))
	{
	  logs::error << 	msat_type_repr (vtype) << " " <<
	    msat_last_error_message (env) << endl;
	  abort ();
	}
    }

  vars = collect_subterms_of_type<ExprSet, RegisterExpr> (e, true);
  unordered_set<const RegisterDesc *> cache;
  for (ExprSet::const_iterator i = vars.begin (); i != vars.end (); i++)
    {
      const RegisterExpr *reg = dynamic_cast<const RegisterExpr *>(*i);

      assert (reg != NULL);

      const RegisterDesc *regdesc = reg->get_descriptor ();
      
      assert (! regdesc->is_alias ());

      msat_type vtype = msat_get_bv_type (env, regdesc->get_register_size ());
      const char *vname = regdesc->get_label ().c_str ();
      msat_declare_function (env, vname, vtype);
    }

  

  return 0;
}

ExprSolver::Result 
ExprMathsatSolver::check_sat (const Expr *e, bool preserve) 
    throw (UnexpectedResponseException)
{
  if (debug_traces)
    BEGIN_DBG_BLOCK ("check_sat : " + e->to_string ());
  if (preserve)
    push ();

  msat_env env = envstack.top ();
  s_declare_variables (e, env, mca->get_address_size ());

  add_assertion (e);
  ExprSolver::Result result = check_sat ();
  if (preserve)
    pop ();

  if (debug_traces)
    END_DBG_BLOCK ();

  return result;
}

ExprSolver::Result 
ExprMathsatSolver::check_sat ()
  throw (UnexpectedResponseException)
{
  ExprSolver::Result result;
  msat_env env = envstack.top ();

  switch (msat_solve (env))
    {
    case MSAT_SAT: result = ExprSolver::SAT; break;
    case MSAT_UNSAT: result = ExprSolver::UNSAT; break;
    default: result = ExprSolver::UNKNOWN; break;
    }

  return result;
}

void 
ExprMathsatSolver::push () 
  throw (UnexpectedResponseException)
{
  msat_env env = envstack.top ();
  msat_env newenv = 
    msat_create_env (MATHSAT_CONFIG);
  envstack.push (newenv);
  if (msat_push_backtrack_point (newenv) != 0)
    throw UnexpectedResponseException (msat_last_error_message (env));
}

void 
ExprMathsatSolver::pop () 
  throw (UnexpectedResponseException)
{
  msat_env env = envstack.top ();
  if (msat_pop_backtrack_point (env) != 0)
    throw UnexpectedResponseException (msat_last_error_message (env));
  msat_destroy_env (env);
  envstack.pop ();
}

Constant *
ExprMathsatSolver::get_value_of (const Expr *e)
  throw (UnexpectedResponseException)
{
  msat_env env = envstack.top ();
  msat_term msat_e = 
    Expr2MathsatVisitor::translate (env, e, MEMORY_VAR, 
				    mca->get_address_size (), 
				    mca->get_endian (), false);

  msat_term val = msat_get_model_value (env, msat_e);
  
  if (MSAT_ERROR_TERM(val))
    throw UnexpectedResponseException (msat_last_error_message (env));

  if (! msat_term_is_number (env, val))
    {
      ostringstream oss;
      char *s = msat_to_smtlib2_term (env, val); 
      char *se = msat_to_smtlib2_term (env, msat_e); 
      oss << "get_value_of: mathsat return value is not a number '" 
	  << s << "' for '" << se << "'";
      msat_free (s);
      msat_free (se);

      throw UnexpectedResponseException (oss.str ());
    }
  mpq_t out;
  mpz_t num;
  mpq_init (out);
  mpz_init (num);
  msat_term_to_number (env, val, out);
  mpq_get_num (num, out);
  mpq_clear (out);
  Constant *result = Constant::create (mpz_get_ui (num), 0, 
				       e->get_bv_size ());
  
  mpz_clear (num);

  return result;
}

#endif


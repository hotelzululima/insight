/*-
 * Copyright (C) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS AND CONTRIBUTORS ``AS IS''
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <iostream>
#include <stdio.h>
#include <utils/tools.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/ConditionalSet.hh>
#include <kernel/expressions/FormulaUtils.hh>
#include "Slicing.hh"

using namespace std;
using namespace FormulaUtils;

/*****************************************************************************/
// Computation of the dependencies of an expression
/*****************************************************************************/

class ExtractLValueVisitor : public ConstBottomUpApplyVisitor
{
public:
  ExtractLValueVisitor () : result (), lv (NULL) { }
  list<const LValue *> result;
  const LValue *lv;
  
  void pre (const Formula *F) 
  {
    if (lv == NULL)
      lv = dynamic_cast<const LValue *> (F);
  }
  
  void apply (const Formula *F) 
  {
    if (lv == NULL)
      return;

    if (lv == F)
      {
	result.push_back (lv);
	lv = NULL;
      }
  }
};

list<const LValue *> dependencies(Expr *e)
{
  ExtractLValueVisitor ev;
  e->acceptVisitor (ev);

  return ev.result;
}

static list<const LValue *> 
nested_dependencies(const Expr * e) 
{
  return collect_subterms_of_type<list<const LValue *>, LValue> (e, false);
}

/*****************************************************************************/
// LocatedLValue implementation
/*****************************************************************************/

LocatedLValue::LocatedLValue(const LocatedLValue &other) :
  pp (other.pp), lv ((LValue *) other.lv->ref ())
{
}

LocatedLValue::LocatedLValue(MicrocodeAddress addr, const LValue *lv) :
  pp (ConcreteProgramPoint (addr)),
  lv ((LValue *)lv->ref ())
{
}

LocatedLValue::~LocatedLValue()
{
  lv->deref ();
}

const ConcreteProgramPoint &
LocatedLValue::get_ProgramPoint () const
{
  return pp;
}

const LValue *
LocatedLValue::get_LValue () const
{
  return lv;
}

/*****************************************************************************/
// DataDependencyLocalContext implementation
/*****************************************************************************/

DataDependencyLocalContext::DataDependencyLocalContext(DataDependency *fixpoint_structure) :
  fixpoint_structure(fixpoint_structure)
{
  the_lvalues = Constant::False ();
}

/*****************************************************************************/

DataDependencyLocalContext::DataDependencyLocalContext(const DataDependencyLocalContext &other) :
  fixpoint_structure(other.fixpoint_structure)
{
  the_lvalues = other.the_lvalues->ref ();
}

DataDependencyLocalContext::~DataDependencyLocalContext()
{
  the_lvalues->deref ();
}
/*****************************************************************************/

bool conditional_rewrite_memref_aux(const Expr *addr, const Formula *value, Formula **phi);
static Formula *
crm_apply_bin_op(BinaryOp op, const Formula *A, const Formula *B);

/* Replace any memory reference of form [x] in phi by (IF (x==addr) THEN value ELSE [x])
 * and propagate the replacement all along the terms. */
bool conditional_rewrite_memref(const Expr *addr, const Formula *value, Formula **phi)
{
  Variable *X = Variable::create ("X");
  bool modified = conditional_rewrite_memref_aux(addr, value, phi);
  Formula * m_pattern = 
    Formula::Equality(Variable::create ("TERM_VALUE"), (Expr *) X->ref ());

  VarList free_variables; 
  free_variables.push_back(X);
  bottom_up_rewrite_pattern_and_assign (phi, m_pattern, free_variables, X);
  X->deref ();
  m_pattern->deref ();

  return modified;
}

static Formula * 
crm_apply_bin_op(BinaryOp op, const Formula *arg1, const Formula *arg2)
{
  Variable *Varg1 = Variable::create ("ARG1");
  Variable *Varg2 = Variable::create ("ARG2");
  Formula *arg2_pattern = arg2->ref ();
  Formula *p = 
    Formula::Equality(Variable::create ("TERM_VALUE"), Varg2->ref ());
  VarList free_variables; 
  free_variables.push_back(Varg2);
  Formula * v =
    Formula::Equality(Variable::create ("TERM_VALUE"),
		      BinaryApp::create (op, Varg1->ref (), Varg2->ref ()));
  bottom_up_rewrite_pattern_and_assign (&arg2_pattern, p, free_variables, v );
  p->deref ();
  v->deref ();

  Formula *result = arg1->ref ();
  p = Formula::Equality(Variable::create ("TERM_VALUE"), Varg1->ref ());
  free_variables.clear(); 
  free_variables.push_back(Varg1);
  bottom_up_rewrite_pattern_and_assign (&result, p, free_variables, 
					arg2_pattern);
  p->deref ();
  arg2_pattern->deref ();
  Varg1->deref ();
  Varg2->deref ();

  return result;
}

bool conditional_rewrite_memref_aux(const Expr *addr, const Formula *value, Formula **phi)
{
  if ((*phi)->is_Expr())
    {
      if (((Expr *) *phi)->is_MemCell())
        {
	  MemCell *mc = (MemCell *)(*phi);
	  Expr *tv = Variable::create ("TERM_VALUE");
	  
          *phi = 
	    Formula::IfThenElse(Formula::Equality(addr->ref (), 
						  mc->get_addr()->ref ()),
				Formula::Equality(tv->ref (), 
						  (Expr *) value->ref ()),
				Formula::Equality(tv->ref (), mc->ref ()));
	  tv->deref ();
	  mc->deref ();

          return true;
        }

      if (((Expr *) *phi)->is_UnaryApp())
        {
	  UnaryApp *ua = (UnaryApp *) *phi;
	  Variable *tv = Variable::create ("TERM_VALUE");
	  Variable *ARG = Variable::create ("ARG");
          Formula *arg1 = (Formula *) ua->get_arg1()->ref ();
          bool arg1_modified = 
	    conditional_rewrite_memref_aux(addr, value, &arg1);
          Formula *p = Formula::Equality(tv->ref (), ARG->ref ());
	  VarList free_variable; 
	  free_variable.push_back(ARG);
          Formula *v =
            Formula::Equality(tv->ref (),
			      UnaryApp::create (ua->get_op(), ARG->ref ()));
          bool modified = 
	    bottom_up_rewrite_pattern_and_assign (&arg1, p, free_variable, v);
          *phi = arg1;
          modified = arg1_modified || modified ;

	  p->deref ();
	  v->deref ();
          ua->deref ();
	  ARG->deref ();
	  tv->deref ();

          return modified;
        }

      if (((Expr *) *phi)->is_BinaryApp())
        {
	  BinaryApp *ba = (BinaryApp *) * phi;
          Formula *arg1 = (Formula *) ba->get_arg1 ()->ref ();
          bool arg1_modified = 
	    conditional_rewrite_memref_aux(addr, value,  & arg1);

          Formula *arg2 = (Formula *) ba->get_arg2 ()->ref ();
          bool arg2_modified = 
	    conditional_rewrite_memref_aux(addr, value,  & arg2);

          Formula * new_phi = crm_apply_bin_op(ba->get_op(), arg1, arg2);
          *phi = new_phi;

	  arg1->deref();
	  arg2->deref();
	  ba->deref ();

          return arg1_modified || arg2_modified;
        }

      Formula * phi_sav = *phi;
      *phi = Formula::Equality(Variable::create ("TERM_VALUE"), 
			       (Expr *) (*phi)->ref ());
      phi_sav->deref ();

      return true;
    }

  if ((*phi)->is_NegationFormula())
    {
      Formula *neg = ((NegationFormula *) * phi)->get_neg ()->ref ();
      if (conditional_rewrite_memref_aux(addr, value, &neg))
        {
	  (*phi)->deref ();
	  *phi = NegationFormula::create (neg);

          return true;
        }
      else
	{
	  neg->deref ();
	}

      return false;
    }

  if ((*phi)->is_ConjunctiveFormula())
    {
      bool modified = false;
      vector<Formula *> clauses = 
	((ConjunctiveFormula *) * phi)->get_clauses_copy();
      for (vector<Formula *>::iterator c = clauses.begin(); c != clauses.end(); 
	   c++)
        {
          if (conditional_rewrite_memref_aux(addr, value, &(*c)))
            modified = true;
        }

      if (modified)
        {
	  (*phi)->deref ();
          *phi = ConjunctiveFormula::create (clauses);
        }
      else
	{
	  for (vector<Formula *>::iterator c = clauses.begin(); 
	       c != clauses.end(); c++)
	    (*c)->deref ();
	}
      return modified;
    }

  if ((*phi)->is_DisjunctiveFormula())
    {
      bool modified = false;
      vector<Formula *> clauses = 
	((DisjunctiveFormula *) * phi)->get_clauses_copy();
      for (vector<Formula *>::iterator c = clauses.begin(); c != clauses.end(); 
	   c++)
        {
          if (conditional_rewrite_memref_aux(addr, value, &(*c)))
            modified = true;
          //new_phi->add_clause((Formula *)(*c)->clone());
        }
      if (modified)
        {
	  (*phi)->deref ();
          *phi = DisjunctiveFormula::create (clauses);
        }
      else
	{
	  for (vector<Formula *>::iterator c = clauses.begin(); 
	       c != clauses.end(); c++)
	    (*c)->deref ();
	}
      return modified;
    }

  if ((*phi)->is_QuantifiedFormula())
    {
      QuantifiedFormula *ephi = (QuantifiedFormula *) *phi;
      Formula *body = ephi->get_body ()->ref ();

      if (conditional_rewrite_memref_aux(addr, value, &body))
        {
	  Variable *nv = (Variable *) ephi->get_variable ()->ref ();

	  *phi = QuantifiedFormula::create (ephi->is_exist (), nv, body);

	  ephi->deref ();
          return true;
        }
      else
	{
	  body->deref ();
	}
      return false;
    }

  return false;
}

/*****************************************************************************/

DataDependencyLocalContext *
DataDependencyLocalContext::run_backward (StaticArrow *arr)
{
  Statement *stmt = arr->get_stmt ();

  if (stmt->is_External () || stmt->is_Jump () || stmt->is_Skip ())
    {
      DataDependencyLocalContext *new_context = 
	new DataDependencyLocalContext (*this);
      if (!DataDependency::ConsiderJumpCond () || 
	  DataDependency::OnlySimpleSets ()) 
	return new_context;

      Expr *cond = arr->get_condition ();
      if (!cond->eval_level0 ()) 
	{
    	  Formula *new_lvalues = 
	    ConjunctiveFormula::create (cond->ref (), 
					new_context->the_lvalues->ref ());
    	  new_context->the_lvalues->deref ();
          new_context->the_lvalues = new_lvalues;
        }

      return new_context;
    }

  if (! stmt->is_Assignment ())
    Log::fatal_error("slicing: run_backward : statement type unknown");

  // The processing of assignment of form LV := RV (where LV is a left-value 
  // and RV is a term) is twofold:
  // - if LV appear in the current dependencies, then it must be replaced by 
  //   the set of dependencies of RV (note that this replacement is conditional
  //   when LV is a memory reference)
  // - if LV appears in a term, then it must be replaced by RV (in a conditional
  //   way also when LV is a memory reference).
  LValue *lval = ((Assignment *) stmt)->get_lval ();
  Expr *rval = ((Assignment *) stmt)->get_rval ();
  DataDependencyLocalContext *new_context = 
    new DataDependencyLocalContext (*this);

  Formula *deps = Constant::False ();
  list<const LValue *> depends = dependencies (rval);
  for (list<const LValue *>::iterator elt = depends.begin(); elt != depends.end(); 
       elt++) {
    ConditionalSet::cs_add(&(deps), *elt);
  }

  if (lval->is_RegisterExpr())
    {
      // Here one replaces lval in new_context->the_lvalues by
      // - the dependencies of rval when lval appears in the occurencies EltSymbol = lval
      // - directly rval anywhere else

      Formula *reg_pattern = 
	Formula::Equality(ConditionalSet::EltSymbol (), lval->ref ());

      // The variable TMP is used to hide form EltSymbol = lval when one replaces lval by rval.
      Variable *tmp = Variable::create ("TMP");
      bottom_up_rewrite_pattern_and_assign (&(new_context->the_lvalues),
					    reg_pattern, VarList (), tmp);
      reg_pattern->deref ();
      reg_pattern = lval;
      bottom_up_rewrite_pattern_and_assign (&(new_context->the_lvalues), 
					    reg_pattern, VarList (), rval);

      // Here one replaces the occurences of EltSymbol = lval by the 
      // dependencies of rval.
      replace_variable_and_assign (&(new_context->the_lvalues), tmp, deps);
      tmp->deref ();
    }

  if (lval->is_MemCell())
    {
      Variable *elt_addr = Variable::create ("ELT_ADDR");
      Variable *X = Variable::create ("X");
      // 1. Formally replace all occurencies of "EltSymbol = [x]" for any 
      // expr x by "ELT_ADDR = x" (ELT_ADDR is a new variable)
      Formula *m_pattern = 
	Formula::Equality(ConditionalSet::EltSymbol (), 
			  MemCell::create (X->ref ()));
      VarList free_variables;
      free_variables.push_back(X);

      Formula *tmp = Formula::Equality(elt_addr->ref (), X->ref ());
      bottom_up_rewrite_pattern_and_assign (&(new_context->the_lvalues),
					    m_pattern, free_variables, tmp);
      tmp->deref ();
      m_pattern->deref ();

      // 2. Replace any memory reference of form [x] in phi by (IF (x==addr) THEN value ELSE [x])
      //    and propagate the replacement all along the terms.
      //    Note that the previous operation (1) makes avoid doing that on original terms of form EltSymbol = [x].
      //    Indeed this last case is treated separately, because in this case, when x=addr, [x] must not be replaced
      //    by the term value, but by the set of all the dependencies of the term value.
      conditional_rewrite_memref(((MemCell *) lval)->get_addr(), rval, 
				 &(new_context->the_lvalues));

      // 3. As mentionned above, here we replace the original occurences of EltSymbol = [x] by
      //    (IF (x == addr) THEN { Conditional set encoding dependencies of values} ELSE EltSymbol = [x])
      m_pattern = Formula::Equality(elt_addr->ref (), X->ref ());
      tmp =
	Formula::IfThenElse(Formula::Equality(((MemCell *) lval)->get_addr()->ref (), X->ref ()),
			    deps->ref (),  
			    Formula::Equality(ConditionalSet::EltSymbol (),
					      MemCell::create (X->ref ())));
      bottom_up_rewrite_pattern_and_assign (&(new_context->the_lvalues), 
					    m_pattern, free_variables, tmp);
      tmp->deref ();
      m_pattern->deref ();
      X->deref ();
      elt_addr->deref ();
    }

  // Finally, assignments may have also condition, it is processed here.
  Expr *cond = arr->get_condition();
  if (DataDependency::ConsiderJumpCond() && !DataDependency::OnlySimpleSets() && !cond->eval_level0())
    {
      Formula *new_lvalues = 
	ConjunctiveFormula::create (cond->ref (), 
				    new_context->the_lvalues->ref ());
      new_context->the_lvalues->deref ();
      new_context->the_lvalues = new_lvalues;
    }

  FormulaUtils::simplify_level0(&(new_context->the_lvalues));
  rewrite_in_DNF (&(new_context->the_lvalues));

  if (DataDependency::OnlySimpleSets()) {
    Formula * old = new_context->the_lvalues;
    new_context->the_lvalues = 
      ConditionalSet::cs_flatten (new_context->the_lvalues);
    old->deref ();
  }
  deps->deref ();

  return new_context;
}

/*****************************************************************************/

bool DataDependencyLocalContext::merge(DataDependencyLocalContext *other)
{
  return ConditionalSet::cs_union(&(the_lvalues), other->the_lvalues);
}

/*****************************************************************************/

DataDependencyLocalContext * 
DataDependency::get_local_context(ConcreteProgramPoint pp)
{
  DataDependencyLocalContext *result = NULL;
  map<ConcreteProgramPoint, DataDependencyLocalContext *>::iterator pair = 
    the_fixpoint.find(pp);

  if (pair != the_fixpoint.end())
    result = pair->second;
  return result;
}

/*****************************************************************************/

void 
DataDependency::update_from_program_point (ConcreteProgramPoint pp)
{
  MicrocodeNode *target_node = the_program->get_node (pp.to_address ());

  for (pair<StmtArrow *, MicrocodeNode *> pred = 
	 the_program->get_first_predecessor(target_node);
       pred.first != 0 && pred.second != 0;
       pred = the_program->get_next_predecessor (target_node, pred.first))
    {
      if (pred.first->is_dynamic())
        Log::warningln ("Caution: I ignore all the dynamic arrows "
			"for analysis");
      pending_arrows.push_back((StaticArrow *) pred.first);
    }
}

/*****************************************************************************/

DataDependency::DataDependency (Microcode *prg, list<LocatedLValue> seeds) :
  the_program (prg),
  fixpoint_reached (false)
{
  prg->regular_form ();
  prg->optimize ();

  for (list<LocatedLValue>::iterator llv = seeds.begin (); llv != seeds.end (); 
       llv++)
    {
      ConcreteProgramPoint pp = llv->get_ProgramPoint ();
      DataDependencyLocalContext *ctxt = get_local_context (pp);

      if (ctxt == NULL)
        {
	  if (the_fixpoint.find (pp) != the_fixpoint.end ())
	    delete the_fixpoint[pp];
          ctxt = new DataDependencyLocalContext (this);
          the_fixpoint[pp] = ctxt;
        }
      ConditionalSet::cs_add (ctxt->get_watched_lvalues (), llv->get_LValue ());

      update_from_program_point (pp);
    }
}

DataDependency::~DataDependency()
{
  std::map<ConcreteProgramPoint, DataDependencyLocalContext *>::iterator i =
    the_fixpoint.begin ();
  std::map<ConcreteProgramPoint, DataDependencyLocalContext *>::iterator end =
    the_fixpoint.end ();
  for (; i != end; i++)
    delete (*i).second;
}

/*****************************************************************************/

bool DataDependency::consider_jump_cond_flag = false;
bool DataDependency::only_simple_sets_flag = false;

void DataDependency::ConsiderJumpCondMode(bool set) { consider_jump_cond_flag = set; };
bool DataDependency::ConsiderJumpCond() { return consider_jump_cond_flag; };
void DataDependency::OnlySimpleSetsMode(bool set) { only_simple_sets_flag = set; };
bool DataDependency::OnlySimpleSets() { return only_simple_sets_flag; };

/*****************************************************************************/

// \todo to be moved anywhere else
void print_expressions(std::vector<Expr*> * expr_lst, int verb) {
  Log::emph ("{ ", verb);
  for (int i=0; i<(int) expr_lst->size(); i++) {
    Log::emph ((*expr_lst)[i]->pp() + " ", verb);
    (*expr_lst)[i]->deref ();
  }
  Log::emph (" }", verb);
}

// \todo to be moved anywhere else
void print_expressions(list<Expr*> * expr_lst, int verb) {
  Log::emph ("{ ", verb);
  for (list<Expr*>::iterator i=expr_lst->begin(); i != expr_lst->end(); i++) {
    Log::emph ((*i)->pp(), verb);
    (*i)->deref ();
  }
  Log::emph (" }", verb);
}


bool DataDependency::InverseStep()
{
  if (fixpoint_reached || pending_arrows.size() == 0) {
    fixpoint_reached = true;
    return true;
  }

  StaticArrow * the_arrow = pending_arrows.front();
  pending_arrows.pop_front();
  DataDependencyLocalContext * target_context = 
    get_local_context(ConcreteProgramPoint(the_arrow->get_concrete_target()));

  if (target_context == NULL)
    {
      Log::fatal_error("DataDependency: DataDependency: should be a "
		       "context here");
    }

  DataDependencyLocalContext * new_context = 
    target_context->run_backward (the_arrow);

  Log::separator(2);
  Log::print ("Running backward arrow ", 2);
  Log::emphln ("< " + the_arrow->pp() + " >", 2);
  Log::println ("New context at pp " + the_arrow->get_origin().pp() + " :", 2);
  Log::println ((*(new_context->get_watched_lvalues()))->pp("\t"), 2);
  Log::print ("Maximum dependencies at pp " + the_arrow->get_origin().pp() 
	      + " : ", 2);

  std::vector<Expr*> upper_set =
    ConditionalSet::cs_possible_values((*(new_context->get_watched_lvalues())));
  print_expressions(&upper_set,2);
  Log::println("",2);

  ConcreteProgramPoint origin_pp (the_arrow->get_origin());
  DataDependencyLocalContext *origin_context = get_local_context (origin_pp);
  bool need_update = true;

  if (origin_context != NULL)
    {
      need_update = origin_context->merge(new_context);
      delete new_context;
    }
  else
    {
      if (the_fixpoint.find (origin_pp) != the_fixpoint.end ())
	delete the_fixpoint[origin_pp];
      the_fixpoint[origin_pp] = new_context;
    }
  
  if (need_update) 
    update_from_program_point (origin_pp);
  fixpoint_reached = (pending_arrows.size () == 0);

  return fixpoint_reached;
}

void 
DataDependency::ComputeFixpoint (int max_step_nb)
{
  while (!fixpoint_reached && max_step_nb--)
    InverseStep ();

  if (max_step_nb > 0) 
    Log::emphln ("DataDependency: Fixpoint Reached!", 2);
}

Formula * 
DataDependency::get_dependencies (ConcreteProgramPoint pp, int max_step_nb) 
{
  Formula *result;
  DataDependencyLocalContext *ctxt = get_local_context (pp);

  ComputeFixpoint (max_step_nb);

  if (ctxt != NULL)
    result =  (*(ctxt->get_watched_lvalues()))->ref ();
  else
    result = Constant::False ();

  return result;
}

std::vector<Expr*> 
DataDependency::get_simple_dependencies(ConcreteProgramPoint pp, 
					int max_step_nb) 
{
  Formula *result = get_dependencies (pp, max_step_nb);
  std::vector<Expr*> simple_result = 
    ConditionalSet::cs_possible_values (result);
  result->deref ();

  return simple_result;
}

/*****************************************************************************/

std::vector<StmtArrow*> 
DataDependency::slice_it (Microcode *prg, MicrocodeAddress seed_loc, 
			  const Expr * seed) 
{
  list<const LValue*> seeds = nested_dependencies (seed);
  list<LocatedLValue> llvs;
  for (list<const LValue*>::iterator s = seeds.begin (); s != seeds.end (); s++)
    llvs.push_back (LocatedLValue (seed_loc, *s));
  std::vector<StmtArrow*> result = DataDependency::slice_it (prg, llvs);

  return result;
}

std::vector<StmtArrow*> 
DataDependency::slice_it(Microcode *prg, std::list<LocatedLValue> seeds) {
  DataDependency::ConsiderJumpCondMode(true);
  DataDependency::OnlySimpleSetsMode(true);

  DataDependency invfix(prg, seeds);
  std::vector<MicrocodeNode *> * nodes = prg->get_nodes();
  int max_step_nb = nodes->size();
  invfix.ComputeFixpoint(max_step_nb);

  vector<StmtArrow*> result;

  Log::separator(2);
  Log::println ( "Dependencies:", 2 );

  for (int n=0; n<(int) nodes->size(); n++) 
    {
      Log::print ( (*nodes)[n]->get_loc().pp(), 2 );
      Log::print ( " <== ", 2 );
      std::vector<Expr*> deps = 
	invfix.get_simple_dependencies((*nodes)[n]->get_loc(), max_step_nb);
      print_expressions(& deps, 2);
      Log::println("", 2);

      std::vector<LValue*> lv_deps;

      std::vector<StmtArrow *> * succs = (*nodes)[n]->get_successors();
      for (int s=0; s<(int) succs->size(); s++) 
	{
	  if (! (*succs)[s]->get_stmt()->is_Assignment()) 
	    continue;

	  LValue * the_lv = ((Assignment *) (*succs)[s]->get_stmt())->get_lval();
	  Option<MicrocodeAddress> tgtopt = (*succs)[s]->extract_target();
	  if (!tgtopt.hasValue()) 
	    continue;

	  MicrocodeAddress addr = tgtopt.getValue();
	  std::vector<Expr*> tgt_deps = 
	    invfix.get_simple_dependencies (addr, max_step_nb);
	  bool influence = false;
	  for (int d=0; d<(int) tgt_deps.size(); d++) 
	    {
	      if ((tgt_deps[d]->contains(the_lv)) ||                    // Case 1: one dependency contains the modified lv
		  (tgt_deps[d]->is_MemCell() && the_lv->is_MemCell()))  // Case 2: the modified lv is a memory reference and there is a memory reference in the dependency (brutal!)
		{ influence = true; break; }
	    }
	  for (int d=0; d<(int) tgt_deps.size(); d++) 
	    tgt_deps[d]->deref ();
	  if (influence) {
	    Log::emphln ((*succs)[s]->pp(), 2);
	    result.push_back((*succs)[s]);
	  }
	  else
	    Log::println ( (*succs)[s]->pp(), 2);
	}	
    }
  Log::separator(2);

  return result;
}

/* if arr has not already been explored, push it into pending */
bool DD_u_explore(vector<StmtArrow*> * explored, list<StmtArrow*> * pending, StmtArrow * arr) {
  for (int i=0; i < (int) explored->size(); i++)
    if (*((*explored)[i]) == (*arr)) return false;
  pending->push_back(arr);
  explored->push_back(arr);
  return true;
}

Option<bool> DD_u_follow_edge(Microcode * prg, StmtArrow * arr, list<StmtArrow*> * pending_arrows, vector<StmtArrow*> * explored_arrows) {
  Option<MicrocodeAddress> tgtopt = arr->extract_target();
  if (!tgtopt.hasValue()) { return Option<bool>(true); } // Unresolved dynamic jump : true.
  MicrocodeAddress addr = tgtopt.getValue();
  MicrocodeNode * tgt_node;
  try { tgt_node = prg->get_node(addr); } catch (...) { return Option<bool>(false); } // Absent node: ignored
  vector<StmtArrow *> * succs = tgt_node->get_successors();
  for (int s=0; s<(int) succs->size(); s++)
    DD_u_explore(explored_arrows, pending_arrows, (*succs)[s]);
  return Option<bool>();
}

bool 
DataDependency::statement_used (Microcode *prg, StmtArrow *arr) 
{
  if (! arr->get_stmt ()->is_Assignment ()) 
    {
      // optim: add skip with condition true
      return true;
    }

  LValue * the_lv = ((Assignment *) arr->get_stmt())->get_lval();
  if (!the_lv->is_RegisterExpr ()) 
    {
      // optim: for MemCells one can do simple but efficient things
      return true;
    }

  RegisterExpr * the_reg = (RegisterExpr *) the_lv;

  list<StmtArrow*> pending_arrows;
  vector<StmtArrow*> explored_arrows;

  // initialisation of pending arrows:
  Option<MicrocodeAddress> tgtopt = arr->extract_target();
  if (!tgtopt.hasValue()) { return true; } // Dynamic jump
  MicrocodeAddress addr = tgtopt.getValue();
  MicrocodeNode * tgt_node;
  try { tgt_node = prg->get_node(addr); } catch (...) { return true; } // Absent node: anything is possible
  vector<StmtArrow *> * succs = tgt_node->get_successors();
  for (int s=0; s<(int) succs->size(); s++)
    DD_u_explore(&explored_arrows, &pending_arrows, (*succs)[s]);

  while (pending_arrows.size() > 0) {
    StmtArrow * new_arr = pending_arrows.front(); pending_arrows.pop_front();
        // 1. follow the edge if it is not an assignment (i.e. add the edges succeding to new_arr and loop)
    // (if it of form jump expr (dynamic jump) return true);
    if (!new_arr->get_stmt()->is_Assignment()) {
      Option<bool> follow = DD_u_follow_edge(prg, new_arr, & pending_arrows, & explored_arrows);
      try { if (follow.getValue() == true) return true; } catch(...) {}
      continue;
    }

    // 2. otherwise, the edge is of form lv := expr;
    // 2.1 if the_reg is used by expr return true
    Expr * e = ((Assignment *) new_arr->get_stmt())->get_rval();
    if (e->contains(the_reg)) return true;
    // 2.2 if the_reg is contained in lv but not equal to lv, return true;
    LValue * lv = ((Assignment *) new_arr->get_stmt())->get_lval();
    if ((!the_reg->equal(lv)) && lv->contains(the_reg)) return true;
    // 2.3 if the_reg is equal to lv continue (without following the edge)
    if (the_reg->equal(lv)) continue;
    // 2.4 otherwise, add the edge succeding to new_arr if it has not already been explored and loop
    DD_u_follow_edge(prg, new_arr, & pending_arrows, & explored_arrows);
  }

  return false;
}

std::vector<StmtArrow *> 
DataDependency::useless_statements (Microcode * prg) 
{
  vector<StmtArrow*> result;
  vector<MicrocodeNode *> *nodes = prg->get_nodes ();

  for (int n = 0; n< (int) nodes->size (); n++) 
    {
      vector<StmtArrow *> *succs = (*nodes)[n]->get_successors ();
    for (int s = 0; s<(int) succs->size (); s++) 
      {
	if (! DataDependency::statement_used (prg, (*succs)[s])) 
	    result.push_back ((*succs)[s]);
      }
    }

  return result;
}

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
#include <analyses/Wp.hh>

#include <list>
#include <set>
#include <kernel/expressions/exprutils.hh>
#include <kernel/microcode/MicrocodeNode.hh>
#include <kernel/Microcode.hh>
#include <utils/graph.hh>
#include <utils/logs.hh>

using namespace std;
using namespace exprutils;

typedef std::list<const MemCell *> MemCellContainer;

/*! construct subsets and their complements */
template <typename T>
std::vector< std::pair<T, T> > 
construct_all_subsets(const T &s) 
{
  std::vector< std::pair<T, T > > subsets;
  std::vector<bool> belongs;
  for (unsigned int i = 0; i < s.size() + 1; i++) 
    belongs.push_back (false);

  while (!belongs[s.size()])
    {      
      int i = 0;
      T subset;
      T complement;
      for (typename T::const_iterator e = s.begin (); e != s.end (); e++, i++)
	{
	  if (belongs[i]) 
	    subset.push_back(*e);
	  else 
	    complement.push_back(*e);
	}
      subsets.push_back(std::pair<T, T >(subset, complement));

      unsigned int k = 0;
      do {
    	  belongs[k] = !belongs[k];
    	  k++;
      }
      while ((!belongs[k - 1]) && (k < (s.size() + 1)));
    }

  return subsets;
}

Expr * weakest_precondition(Expr * post, Statement *stmt)
{
  if (stmt->is_Skip())
    return post;

  if (stmt->is_Jump())
    return post;

  logs::check ("weakest_precondition: unknown statement",
	      stmt->is_Assignment());

  Assignment *assmt = dynamic_cast<Assignment *>(stmt);

  if (assmt->get_lval()->is_RegisterExpr())
    {
      Expr *original_cpy = post->ref ();
      Expr *result = 
	replace_subterm (original_cpy, assmt->get_lval(), assmt->get_rval());
      if (result != original_cpy) 
	original_cpy->deref ();
      return result;
    }

  const MemCell *mc = dynamic_cast<const MemCell *>(assmt->get_lval());
  assert (mc != NULL);



  // 1. construct the list of all memory references appearing in this
  MemCellContainer all_memrefs = 
    collect_subterms_of_type<MemCellContainer, MemCell> (post, true);

  if (all_memrefs.size() == 0) 
    return post;

  // 2. construct the list of all the subsets of memory references (to be 
  // replaced by an enumerator)
  vector< pair<MemCellContainer, MemCellContainer > > all_subsets = 
    construct_all_subsets(all_memrefs);

  // 3. construct the expr
  vector<Expr *> phi_clauses;

  Expr *phi = Constant::True ();
  for (vector< pair<MemCellContainer, MemCellContainer > >::iterator
	 subset = all_subsets.begin();
       subset != all_subsets.end();
       subset++)
    {

      // Hypothesis : all addresses of all memcell in *subset are equal to 
      // those of mc
      // and all the other ones are different from those of mc
      Expr * hyp = Constant::True ();  // true by default
      for (MemCellContainer::iterator mcel = (*subset).first.begin(); 
	   mcel != (*subset).first.end(); mcel++) 
	{
	  Expr *c = BinaryApp::createEquality (mc->get_addr()->ref (),
					       (*mcel)->get_addr()->ref ());
	  hyp = BinaryApp::createLAnd (c, hyp);
	}

      for (MemCellContainer::iterator mcel = (*subset).second.begin(); 
	   mcel != (*subset).second.end(); mcel++) 
	{
	  Expr *c = 
	    Expr::createDisequality (mc->get_addr()->ref (),
				     (*mcel)->get_addr()->ref ());
	  hyp = Expr::createLAnd (c, hyp);
	}

      // Replace all the terms pointed by elements of subset by the right 
      // member of assmt
      Expr * psi = post->ref ();
      for (MemCellContainer::iterator mcel = (*subset).first.begin(); 
	   mcel != (*subset).first.end(); mcel++)
	replace_subterm (psi, *mcel, (Expr *) assmt->get_rval());

      phi = Expr::createLAnd (Expr::createImplies (hyp, psi), phi);
    }

  simplify_level0 ((Expr **) &phi);

  return phi;
}

/*****************************************************************************/

Expr * weakest_precondition(Expr * post, StmtArrow *arrow)
{
  Expr *phi = 
    Expr::createImplies (arrow->get_condition(),
			 weakest_precondition(post, arrow->get_stmt()));
  simplify_level0 (&phi);
  if (logs::debug_is_on)
    {
      logs::debug << string (79 ,'*') << endl
		 << "Backward step on :" << endl
		 << phi->to_string () << endl;
    }
  return phi;
}

Expr * weakest_precondition(Expr * post, MCPath &p)
{
  Expr * phi = post;
  for (MCPath_reverse_iterator arr = p.rbegin(); arr != p.rend(); ++arr) {
      Expr * new_phi = weakest_precondition(phi, *arr);
      if (phi != post && phi != new_phi) { // \todo comment phi pourrait etre != de this ?...
	phi->deref ();
	phi = new_phi;
      }
    }
  return phi;
}


class SequentialisationVisitor : public GraphVisitor<MicrocodeNode, StmtArrow> {

public:

  list<MCPath> segments;
  Microcode *prg;

  SequentialisationVisitor(Microcode *p) : prg(p) {};
  ~SequentialisationVisitor() {};

  bool has_invariant(MicrocodeAddress a)
  {
    return prg->get_node(a)->is_annotated() ;
  };

  void process(MicrocodeNode * , StmtArrow *)
  {
    try
      {
        if (has_invariant(current_path_get_target()))
          {
            MicrocodeAddress start = current_path_get_last_annotation().getValue();
            MicrocodeAddress final = current_path_get_target();
            MCPath path = current_path_extract(start, final);
            cout << "SEGMENT" << start.pp() << "-" << final.pp() << ":\n" << path.pp() << endl;
            segments.push_back(path);
            cout << segments.size() << endl;
          }
      }
    catch (OptionNoValueExc &)
      {
        logs::warning << "process: unable to extract target" << endl;
      }
  };

  bool go_further(MicrocodeNode *, StmtArrow *)
  {
    return true;
  };

  void back_step_impasse() {}
  void traversal_over() {}

  void back_step_loop(StmtArrow *)
  {
    MicrocodeAddress final = current_path_get_target();
    MCPath path = current_path_extract(final, final);
    cout << "LOOP " << final.pp() << "-" << final.pp() << ":\n" << path.pp() << endl;
    segments.push_back(path);
    bool found_invariant = false;
    for (MCPath_iterator arr = path.begin(); arr != path.end(); arr++)
      if (has_invariant((*arr)->get_origin()))
        {
          found_invariant = true;
          break;
        }
    if (!found_invariant)
      logs::warning << "Loop without invariant" << endl;
  };

  bool continue_run()
  {
    return true;
  };

  Option<MicrocodeAddress> current_path_get_last_annotation()
  {
    for (list< vector<StmtArrow *> >::reverse_iterator arrows = current_path->rbegin(); arrows != current_path->rend(); ++arrows)
      {
        MicrocodeAddress a = arrows->back()->get_origin();
        if (has_invariant(a)) return Option<MicrocodeAddress>(a);
      }
    return Option<MicrocodeAddress>();
  };

  MicrocodeAddress current_path_get_target()
  {
    logs::check("current_path_get_last_annotation: current path empty", current_path->size() > 0);
    return current_path->back().back()->extract_target().getValue();
  };

  MCPath current_path_extract(MicrocodeAddress start, MicrocodeAddress end)
  {
    MCPath subpath(prg);
    for (list< vector<StmtArrow *> >::iterator arrows = current_path->begin(); arrows != current_path->end(); arrows++) {
        StmtArrow *a = arrows->back();
        if (subpath.size() > 0) {
            subpath.push_back(a);
            if (a->extract_target().getValue().equals(end))
              return subpath;
        }
        else {
            if (a->get_origin().equals(start)) subpath.push_back(a);
            if (a->extract_target().getValue().equals(end) &&
		subpath.size() > 0)
              return subpath;
        }
    }
    logs::warning << "current_path_extract: cannot find bounds" << endl;
    cout << start.pp() << "-" << end.pp() << endl;
    return subpath;
  };
};

list<MCPath> sequencialize(Microcode * prg)
{
  SequentialisationVisitor v(prg);
  prg->depth_first_run(prg->get_node(prg->entry_point()), v);
  return v.segments;
}

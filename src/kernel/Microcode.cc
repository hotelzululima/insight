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

#include <kernel/Microcode.hh>

#include <assert.h>
#include <map>
#include <list>
#include <set>
#include <vector>
#include <algorithm>
#include <kernel/annotations/NextInstAnnotation.hh>
#include <decoders/DecoderFactory.hh>
#include <utils/Option.hh>
#include <utils/logs.hh>

using namespace std;

Microcode::Microcode () :
  MicrocodeStore (),
  GraphInterface<MicrocodeNode, StmtArrow, NodeStore> (),
  nodes (),
  opt_nodes (),
  start (MicrocodeAddress::null_addr ()),
  arrow_callbacks ()
{
}

Microcode::Microcode (const Microcode &prg) :
  MicrocodeStore (prg),
  GraphInterface<MicrocodeNode, StmtArrow, NodeStore> (),
  nodes (),
  opt_nodes (),
  start (prg.start),
  arrow_callbacks (prg.arrow_callbacks)
{
  Microcode_iterate_nodes (prg, node)
    add_node (new MicrocodeNode (*(*node)));
}

Microcode::~Microcode()
{
  Microcode_iterate_nodes (*this, node)
    delete *node;
}

MicrocodeAddress 
Microcode::entry_point ()
{
  return start;
}

void 
Microcode::set_entry_point (MicrocodeAddress addr)
{
  start = addr;
}

MicrocodeNode *
Microcode::get_node (MicrocodeAddress addr) const
  throw (GetNodeNotFoundExc)
{
  node_map_type::const_iterator it = opt_nodes.find (addr);
  if (it == opt_nodes.end ())
    throw GetNodeNotFoundExc ();
  return it->second;
}

bool
Microcode::has_node_at (MicrocodeAddress addr) const
{
  return (opt_nodes.find (addr) != opt_nodes.end ());
}

MicrocodeNode *
Microcode::get_or_create_node (MicrocodeAddress addr) 
{
  MicrocodeNode *node;

  try {
    node = get_node(addr);
  } catch (GetNodeNotFoundExc e) {
    node = new MicrocodeNode(addr);
    add_node(node);
  }

  return node;
}

StmtArrow *
Microcode::add_skip(MicrocodeAddress beg, MicrocodeAddress end, Expr *guard)
{
  MicrocodeNode *b = get_or_create_node(beg);

  if (guard == NULL)
    guard = Constant::True ();

  MicrocodeNode_iterate_successors (*b, succ)
    {
      if ((*succ)->is_dynamic ())
	continue;

      Expr *cond = (*succ)->get_condition ();
      MicrocodeAddress tgt = ((StaticArrow *) *succ)->get_target ();

      if (cond == guard && tgt.equals (end))
	{
	  guard->deref ();
	  return *succ;
	}
    }

  StmtArrow *a = b->add_successor (guard, get_or_create_node(end),
				   new Skip());
  apply_callbacks (a);

  return a;
}

StmtArrow *
Microcode::add_assignment(MicrocodeAddress beg, LValue *lvalue, Expr *expr,
			  MicrocodeAddress end, Expr *guard) 
{
  MicrocodeNode *b = get_or_create_node(beg);

  if (guard == NULL)
    guard = Constant::True ();
  StmtArrow *a = b->add_successor(guard, get_or_create_node(end),
				  new Assignment(lvalue, expr));
  apply_callbacks (a);

  return a;
}

StmtArrow *
Microcode::add_assignment(MicrocodeAddress &beg, LValue *lvalue, Expr *expr,
			  MicrocodeAddress *pend)
{
  MicrocodeAddress end = pend == NULL ? beg + 1 : *pend;

  StmtArrow *a = add_assignment (beg, lvalue, expr, end);
  beg = end;

  return a;
}

StmtArrow *
Microcode::add_jump(MicrocodeAddress beg, Expr *target, Expr *guard) 
{
  MicrocodeNode *b = get_or_create_node(beg);

  if (guard == NULL)
    guard = Constant::True ();
  StmtArrow *a = b->add_successor(guard, target->ref (), new Jump(target));
  apply_callbacks (a);

  return a;
}

/* Should the relation be a Formula instead? Probably. */
void
Microcode::add_external(MicrocodeAddress /* beg */, Expr * /* relation */,
      MicrocodeAddress /* end */) {
  //! \todo Not implemented yet
  cerr << "Microcode::add_external() is not implemented yet." << endl;
}


static void 
s_copy_annotations (Annotable *dst, const Annotable *src, address_t shift)
{
  const Annotable::AnnotationMap *annotations = src->get_annotations ();

  for(Annotable::AnnotationMap::const_iterator i = annotations->begin ();
      i != annotations->end (); i++)
    {
      const NextInstAnnotation *maa = 
	dynamic_cast<const NextInstAnnotation *>(i ->second);
      Annotation *newa;
      if (maa != NULL)
	newa = new NextInstAnnotation (maa->get_value () + shift);
      else 
	newa = (Annotation *) i->second->clone ();
      dst->add_annotation (i->first, newa);
    }
}

void 
Microcode::merge (const Microcode *other, address_t shift)
{
  Microcode_iterate_nodes(*other, in) 
    {
      MicrocodeNode *node = *in;
      MicrocodeAddress loc = node->get_loc ();
      MicrocodeAddress newloc (loc.getGlobal () + shift, loc.getLocal ());
      MicrocodeNode *newsrc = get_or_create_node (newloc);
      
      s_copy_annotations (newsrc, node, shift);
    }

  Microcode_iterate_nodes(*other, in) 
    {
      MicrocodeNode *node = *in;
      MicrocodeAddress loc = node->get_loc ();
      MicrocodeAddress newloc (loc.getGlobal () + shift, loc.getLocal ());
      MicrocodeNode *newsrc = get_node (newloc);
      
      MicrocodeNode_iterate_successors(*node, is) 
	{
	  StmtArrow *a = *is;
	  StmtArrow *na;

	  assert (a->get_src () == node);
	  if (a->is_static ())
	    {
	      StaticArrow *sa = dynamic_cast<StaticArrow *> (a);
	      MicrocodeAddress natgt (sa->get_target ().getGlobal () + shift,
				      sa->get_target ().getLocal ());
	      MicrocodeNode *newtgt = get_node (natgt);

	      na = newsrc->add_successor (sa->get_condition ()->ref (),
					  newtgt, sa->get_stmt ()->clone ());
	    }
	  else
	    {
	      DynamicArrow *da = dynamic_cast<DynamicArrow *> (a);
	      na = newsrc->add_successor (da->get_condition ()->ref (),
					  da->get_target ()->ref (),  
					  da->get_stmt ()->clone ());
	    }
	  s_copy_annotations (na, a, shift);
	}
    }
}

void
Microcode::output_text (ostream & out) const
{
  Microcode::const_node_iterator stmt = begin_nodes ();
  for (; stmt != end_nodes (); stmt++)
    out << (*stmt)->pp() << endl;
}


static bool 
microcode_sort_ordering (MicrocodeNode *e1, MicrocodeNode *e2)
{
  return (*e1) < (*e2);
}

void 
Microcode::sort ()
{
  std::sort (begin_nodes (), end_nodes (), microcode_sort_ordering);
}

/*! \brief Produces a (new) static arrow from the current dynamic arrow
 *  by trying to extract the target with extract_target method. */

static Option<StaticArrow*>
make_static (Microcode *mc, DynamicArrow *da)
{
  Option<MicrocodeAddress> t = da->extract_target();

  if (t.hasValue())
    {
      MicrocodeNode *tgt = NULL;
      if (! mc->has_node_at (t.getValue ()))
	return Option<StaticArrow*>();

      StaticArrow * static_arrow =
	new StaticArrow(da->get_src(),
			tgt,
			da->get_stmt()->clone(),
			da->get_annotations(),
			da->get_condition()->ref());
      return Option<StaticArrow*>(static_arrow);
    }
  else
    return Option<StaticArrow*>();
}

void 
Microcode::simplify_and_clean_targets()
{
  set<MicrocodeNode *> new_nodes; // temporary list to record nodes to be added.

  Microcode_nodes_pass(node) 
  {
    vector<StmtArrow *> * succs = (*node)->get_successors();
    vector<StmtArrow *>::iterator arr = succs->begin();
    
    while (arr != succs->end())
      {
	// For static arrow, one tests that the target well
	// exists, if not, one adds it in the new node list.
	if ((*arr)->is_static()) {
	  StaticArrow * the_arrow = (StaticArrow *) *arr;
	  MicrocodeAddress addr = the_arrow->get_concrete_target();
	  if (! has_node_at (addr))
	    new_nodes.insert(new MicrocodeNode(addr));
	}
	else
	  {
	    // For dynamic arrow, one tests if we can get the
	    // target directly
	    if ((*arr)->is_dynamic() && ((*arr)->extract_target().hasValue()))
	      {
		DynamicArrow *old_arrow = (DynamicArrow *) * arr;
		StaticArrow * static_arrow =
		  make_static (this, old_arrow).getValue();
		delete old_arrow;
		(*succs).erase(arr);
		succs->push_back(static_arrow);
		// \todo: adds the target node if it does not
		// exists (at the moment this is done, but not
		// optimized !!
		arr = succs->begin();   // \todo optimisation...
	      }
	  }
	arr++;
      }
  }

  for (set<MicrocodeNode *>::iterator new_node = new_nodes.begin();
       new_node != new_nodes.end(); new_node++)
    add_node (*new_node );
}

void 
Microcode::regular_form () 
{
  simplify_and_clean_targets ();
  sort ();
}

vector<Expr **> * 
Microcode::expr_list() 
{
  vector<Expr **> * all_expr = new vector<Expr **>;

  Microcode_iterate_nodes(*this, node) 
    {
      vector<Expr **> * exprs = (*node)->expr_list();
      for (vector<Expr **>::iterator e = exprs->begin(); e != exprs->end();
	   e++) 
        all_expr->push_back(*e);
      delete exprs;
    }

  return all_expr;
}

pair<StmtArrow *, MicrocodeNode *> 
Microcode::get_first_successor(MicrocodeNode *n)  const
{
  if (n == NULL || n->get_successors()->size() == 0) 
      return pair<StmtArrow *, MicrocodeNode *>(NULL, NULL);

  StmtArrow *out = n->get_successors()->at(0);
  MicrocodeNode *dst = NULL;
  try { dst = this->get_target(out); }
  catch (GetNodeNotFoundExc &) {}
  return pair<StmtArrow *, MicrocodeNode *>(out, dst);
}

pair<StmtArrow *, MicrocodeNode *> 
Microcode::get_next_successor(MicrocodeNode *n, StmtArrow *e) const
{
  vector<StmtArrow *>::iterator it = n->get_successors()->begin();
  vector<StmtArrow *>::iterator end = n->get_successors()->end();
  StmtArrow *ne = NULL;
  MicrocodeNode *nn = NULL;
  try {
    bool found = false;
    while (it != end && ne == NULL) {
      if (found && !(**it == *e)) {
	ne = *it;
	nn = this->get_target(ne);
      }
      else {
	if (**it == *e)	found = true;
				*it++;
      }
    }
  }
  catch (GetNodeNotFoundExc &) {}
  return pair<StmtArrow *, MicrocodeNode *>(ne, nn);
}

int 
Microcode::get_nb_successors(MicrocodeNode *n) const
{
  return n->get_successors()->size();
}

MicrocodeNode *
Microcode::get_source(StmtArrow *e) const
{
  return get_node (e->get_origin());
}

MicrocodeNode * 
Microcode::get_target(StmtArrow *e) const
{
  Option<MicrocodeAddress> target = e->extract_target();
  try {
    if (target.hasValue())
      return get_node(target.getValue());
  }
  catch (GetNodeNotFoundExc &) {}
  return NULL;
}

MicrocodeNode *
Microcode::get_entry_point ()  const
{
  return get_node (start);
}

std::size_t
Microcode::get_number_of_nodes () const
{
  assert (nodes.size () == opt_nodes.size ());
  return nodes.size ();
}

Microcode::const_node_iterator
Microcode::begin_nodes () const
{
  return nodes.begin ();
}

Microcode::const_node_iterator
Microcode::end_nodes () const
{
  return nodes.end ();
}

Microcode::node_iterator
Microcode::begin_nodes () 
{
  return nodes.begin ();
}

Microcode::node_iterator
Microcode::end_nodes () 
{
  return nodes.end ();
}

void Microcode::add_node (MicrocodeNode *n)
{
  assert (! has_node_at (n->get_loc ()));
  nodes.push_back(n);
  opt_nodes[n->get_loc ()] = n;
}

void
Microcode::add_arrow_creation_callback (ArrowCreationCallback *cb)
{
  arrow_callbacks.push_back (cb);
}

void
Microcode::remove_arrow_creation_callback (ArrowCreationCallback *cb)
{
  arrow_callbacks.erase (find (arrow_callbacks.begin (),
			       arrow_callbacks.end (), cb));
}

void
Microcode::apply_callbacks (StmtArrow *a)
{
  std::vector<ArrowCreationCallback *>::iterator i = arrow_callbacks.begin ();

  for (; i != arrow_callbacks.end (); i++)
    (*i)->add_node (this, a);
}

string Microcode::get_label_node(MicrocodeNode *n) const
{
  ostringstream oss;
  oss << n->get_loc().getGlobal() << "_" << n->get_loc().getLocal();
  return oss.str();
}

/*****************************************************************************/
/* replace_nodes                                                             */
/*****************************************************************************/

void Microcode::replace_nodes(MicrocodeNodeSet &to_replace, MicrocodeNode *nvo, bool delete_nodes = true)
{

  for (node_iterator it = begin_nodes(); it != end_nodes ();)
    {
      MicrocodeNode *elem = *it;
      for (StmtArrow *a = this->get_first_successor(elem).first; a != NULL; a = this->get_next_successor(elem, a).first)
        {
          MicrocodeNode *tgt = this->get_target(a);
          if (tgt != NULL)
            {
              if (to_replace.find(tgt) != to_replace.end())
                {
                  assert(dynamic_cast<StaticArrow *>(a) != NULL);
                  StaticArrow * sa = (StaticArrow *) a;
                  //Redirect arrows targets
                  sa->set_concrete_target(nvo->get_loc());
                }
            }
        }
      //Remove from graph
      if (to_replace.find(elem) != to_replace.end())
        {
          it = nodes.erase(it);
        }
      else
        {
          ++it;
        }
    }
  //Delete old nodes
  for (MicrocodeNodeSet::iterator it = to_replace.begin(); delete_nodes && it != to_replace.end(); it++)
    {
      delete *it;
    }
  //Add new one
  nodes.push_back(nvo);
}

/*****************************************************************************/
/* extract_subgraph                                                          */
/*****************************************************************************/
/*
Microcode *Microcode::extract_subgraph(list<MicrocodeNode *>* subset)
{
  Microcode *res = new Microcode();
  vector<MicrocodeNode *>* old = this->get_nodes();
  vector<MicrocodeNode *>* nvo = res->get_nodes();

  for (vector<MicrocodeNode *>::iterator it = old->begin(); it != old->end();)
    {
      MicrocodeNode *e = *it;
      bool subs = false;
      for (list<MicrocodeNode *>::iterator it2 = subset->begin(); it2 != subset->end() && !subs; it2++)
        {
          if (*e == **it2)
            {
              subs = true;
            }
        }
      if (subs)
        {
          nvo->push_back(e);
          it = old->erase(it);
        }
      else
        {
          ++it;
        }
    }
  return res;
}
*/
/*****************************************************************************/
/* get_subgraph                                                          */
/*****************************************************************************/

/*
Microcode *Microcode::get_subgraph(list<MicrocodeNode *>* subset)
{
  Microcode *res = new Microcode();
  vector<MicrocodeNode *>* old = this->get_nodes();
  vector<MicrocodeNode *>* nvo = res->get_nodes();

  for (vector<MicrocodeNode *>::iterator it = old->begin(); it != old->end();)
    {
      MicrocodeNode *e = *it;
      bool subs = false;
      for (list<MicrocodeNode *>::iterator it2 = subset->begin(); it2 != subset->end() && !subs; it2++)
        {
          if (*e == **it2)
            {
              subs = true;
            }
        }
      if (subs)
        {
          nvo->push_back(e->clone());
          ++it;
        }
      else
        {
          ++it;
        }
    }
  return res;
}
*/

void
Microcode::check () const
{
  for (const_node_iterator it = begin_nodes (); it != end_nodes(); it++)
    {
      const MicrocodeNode *e = *it;
      MicrocodeNode_iterate_successors (*e, succ) {
	StmtArrow *sa = *succ;
	assert (sa->get_src () == e);
      }
    }
}

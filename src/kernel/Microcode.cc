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
#include <decoders/DecoderFactory.hh>
#include <utils/option.hh>
#include <utils/tools.hh>

using namespace std;

Microcode::Microcode() :
  start(MicrocodeAddress::null_addr()),
  optimized(false),
  node_callbacks ()
{
  nodes = new vector<MicrocodeNode *>;
}

Microcode::Microcode(vector<MicrocodeNode *> * nodes) :
  nodes(nodes),
  optimized(false),
  node_callbacks ()
{
	if (nodes->size() > 0) start = (*nodes)[0]->get_loc();
	else start = MicrocodeAddress::null_addr();
}

Microcode::Microcode(vector<MicrocodeNode *> * nodes, MicrocodeAddress start) :
  nodes(nodes),
  start(start),
  optimized(false),
  node_callbacks ()
{}

Microcode::Microcode(const Microcode &prg) :
  MicrocodeStore(prg),
  GraphInterface<MicrocodeNode, StmtArrow>(),
  start(prg.start),
  optimized(false),
  node_callbacks (prg.node_callbacks)
{
  nodes = new vector<MicrocodeNode *>;
  Microcode_iterate_nodes(prg, node)
  nodes->push_back(new MicrocodeNode(*(*node)));

  if (prg.optimized)
    this->optimize();
}

Microcode::~Microcode()
{
  Microcode_iterate_nodes(*this, node)
    delete *node;
  delete nodes;
}

/*****************************************************************************/

MicrocodeAddress Microcode::entry_point()
{
  return start;
}

void Microcode::set_entry_point(MicrocodeAddress addr)
{
  start = addr;
}

/*****************************************************************************/

MicrocodeNode * Microcode::get_node(MicrocodeAddress addr) const
	throw(GetNodeNotFoundExc)
{
  if (optimized) {
    std::tr1::unordered_map<MicrocodeAddress, MicrocodeNode *,
			    std::tr1::hash<MicrocodeAddress>,
		    EqualsFunctor<MicrocodeAddress> >::const_iterator it;
    it = opt_nodes.find(addr);
    if (it != opt_nodes.end())
      return it->second;
  }
  else {
    Microcode_iterate_nodes(*this, node) {
      if ((*node)->get_loc().equals(addr))
	return (*node);
    }
  }
  throw GetNodeNotFoundExc();
}

MicrocodeNode *
Microcode::get_or_create_node(MicrocodeAddress addr) {
  MicrocodeNode *node;

  try {
    node = get_node(addr);
  } catch (GetNodeNotFoundExc e) {
    node = new MicrocodeNode(addr);
    add_node(node);
  }

  return node;
}

/*****************************************************************************/

void
Microcode::add_skip(MicrocodeAddress beg, MicrocodeAddress end,
        Expr *guard) {
  MicrocodeNode *b = get_or_create_node(beg);

  if (guard == NULL)
    guard = Constant::create (1);

  b->add_successor(guard, get_or_create_node(end), new Skip());
}

void
Microcode::add_assignment(MicrocodeAddress beg, LValue *lvalue, Expr *expr,
        MicrocodeAddress end, Expr *guard) {
  MicrocodeNode *b = get_or_create_node(beg);

  if (guard == NULL)
    guard = Constant::create (1);
  b->add_successor(guard, get_or_create_node(end),
       new Assignment(lvalue, expr));
}

void 
Microcode::add_assignment(MicrocodeAddress &beg, LValue *lvalue, Expr *expr,
			  MicrocodeAddress *pend)
{  
  MicrocodeAddress end = pend == NULL ? beg + 1 : *pend;

  add_assignment (beg, lvalue, expr, end);
  beg = end;
}

void
Microcode::add_jump(MicrocodeAddress beg, Expr *target, Expr *guard) {
  MicrocodeNode *b = get_or_create_node(beg);

  if (guard == NULL)
    guard = Constant::create (1);
  b->add_successor(guard, target->ref (), new Jump(target));
}

/* Should the relation be a Formula instead? Probably. */
void
Microcode::add_external(MicrocodeAddress /* beg */, Expr * /* relation */,
      MicrocodeAddress /* end */) {
  //! \todo Not implemented yet
  cerr << "Microcode::add_external() is not implemented yet." << endl;
}

/*****************************************************************************/

void Microcode::optimize()
{
  regular_form();

  opt_nodes.clear();
  Microcode_iterate_nodes(*this, node) {
    opt_nodes[((MicrocodeNode *) *node)->get_loc()] = *node;
    (*node)->set_father(this);
  }

  Microcode_iterate_nodes(*this, node) {
	  MicrocodeNode_iterate_successors((*(*node)), succ) {
		  (*succ)->set_father(this);
		  (*succ)->set_src(*node);
		  if ((*succ)->is_static()) {
			  StaticArrow * sarr = (StaticArrow*) *succ;
			  MicrocodeNode * t = opt_nodes[ sarr->get_concrete_target() ];
              sarr->set_tgt(t);
              t->add_predecessor(sarr);
		  }
	  }
  }

  optimized = true;
}

bool Microcode::is_optimized() {
  return optimized;
}

/*****************************************************************************/

void
Microcode::output_text(ostream & out) const
{
  vector<MicrocodeNode *>::const_iterator stmt = this->get_nodes()->begin();
  for (; stmt != this->get_nodes()->end(); stmt++)
    out << "(" << (*stmt)->get_loc().pp()
        << ", " << (*stmt)->pp() << ")" << endl;
}


/*****************************************************************************/

void Microcode::regroup_nodes() {
  optimized = false;

  vector<MicrocodeNode *>::iterator node = nodes->begin();
  while (node != nodes->end()) {
    bool new_node = true;
    for (vector<MicrocodeNode *>::iterator past_node = nodes->begin();
	 past_node != node; past_node++) {
      if ((*past_node)->get_loc().equals((*node)->get_loc())) {
	MicrocodeNode_iterate_successors(*(*node), succ) {
	  (*past_node)->get_successors()->push_back((*succ)->clone());
	}
	delete *node;
	nodes->erase(node);
	new_node = false;
	break;
      }
    }
    if (new_node) node++;
  }
}

/*****************************************************************************/

bool microcode_sort_ordering(MicrocodeNode *e1, MicrocodeNode *e2)
{
  return (*e1) < (*e2);
}

void Microcode::sort()
{
  std::sort(nodes->begin(), nodes->end(), microcode_sort_ordering);
}

/*****************************************************************************/

void Microcode::simplify_and_clean_targets()
{
  optimized = false;

  set<MicrocodeNode *> new_nodes; // temporary list to record nodes to be added.

  Microcode_nodes_pass(node) {
	  vector<StmtArrow *> * succs = (*node)->get_successors();
	  vector<StmtArrow *>::iterator arr = succs->begin();

	  while (arr != succs->end())
	    {
	      // For static arrow, one tests that the target well
	      // exists, if not, one adds it in the new node list.
	      if ((*arr)->is_static()) {
		StaticArrow * the_arrow = (StaticArrow *) *arr;
		MicrocodeAddress addr = the_arrow->get_concrete_target();
		try {
		  get_node(addr);
		}
		catch (GetNodeNotFoundExc &)
		  {
		    new_nodes.insert(new MicrocodeNode(addr));
		  }
	      }
	      else
		{
		  // For dynamic arrow, one tests if we can get the
		  // target directly
		  if ((*arr)->is_dynamic() && ((*arr)->extract_target().hasValue()))
		    {
		      DynamicArrow *old_arrow = (DynamicArrow *) * arr;
		      StaticArrow * static_arrow =
			old_arrow->make_static().getValue();
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
    nodes->push_back( *new_node );
};


/*****************************************************************************/

void Microcode::regular_form() {
  regroup_nodes();
  simplify_and_clean_targets();
  sort();
}

/*****************************************************************************/

vector<Expr **> * Microcode::expr_list() {
  vector<Expr **> * all_expr = new vector<Expr **>;

  Microcode_iterate_nodes(*this, node) {
    vector<Expr **> * exprs = (*node)->expr_list();
    for (vector<Expr **>::iterator e = exprs->begin();
         e != exprs->end();
         e++) {
        all_expr->push_back(*e);
      }
    delete exprs;
  }

  return all_expr;
}

/*****************************************************************************/
pair<StmtArrow *, MicrocodeNode *> Microcode::get_first_successor(MicrocodeNode *n)  const
{
  if (n == NULL || n->get_successors()->size() == 0) {
      return pair<StmtArrow *, MicrocodeNode *>(NULL, NULL);
  }
  StmtArrow *out = n->get_successors()->at(0);
  MicrocodeNode *dst = NULL;
  try { dst = this->get_target(out); }
  catch (GetNodeNotFoundExc &) {}
  return pair<StmtArrow *, MicrocodeNode *>(out, dst);
}

pair<StmtArrow *, MicrocodeNode *> Microcode::get_next_successor(MicrocodeNode *n, StmtArrow *e) const
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

int Microcode::get_nb_successors(MicrocodeNode *n) const
{
  return n->get_successors()->size();
}

MicrocodeNode *Microcode::get_source(StmtArrow *e) const
{
  return get_node(e->get_origin());
}

MicrocodeNode * Microcode::get_target(StmtArrow *e) const
{
  Option<MicrocodeAddress> target = e->extract_target();
  try {
	  if (target.hasValue())
		  return get_node(target.getValue());
  }
  catch (GetNodeNotFoundExc &) {}
  return NULL;
}

MicrocodeNode * Microcode::get_entry_point()  const
{
  return get_node(start);
}

vector<MicrocodeNode *> * Microcode::get_nodes()   const
{
  return nodes;
}

void Microcode::add_node(MicrocodeNode *n)
{
  // TODO: optimization !
  nodes->push_back(n);
  apply_callbacks (n);
}

void 
Microcode::add_node_creation_callback (NodeCreationCallback *cb)
{
  node_callbacks.push_back (cb);
}

void 
Microcode::remove_node_creation_callback (NodeCreationCallback *cb)
{
  node_callbacks.erase (find (node_callbacks.begin (), 
			      node_callbacks.end (), cb));
}

void 
Microcode::apply_callbacks (MicrocodeNode *node)
{
  std::vector<NodeCreationCallback *>::iterator i = node_callbacks.begin ();
    
  for (; i != node_callbacks.end (); i++)
    (*i)->add_node (this, node);
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

  for (vector<MicrocodeNode *>::iterator it = nodes->begin(); it != nodes->end();)
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
          it = nodes->erase(it);
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
  nodes->push_back(nvo);
  if (optimized)
    this->optimize();
}

/*****************************************************************************/
/* extract_subgraph                                                          */
/*****************************************************************************/

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

/*****************************************************************************/
/* get_subgraph                                                          */
/*****************************************************************************/


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

struct MCNodeCreate : public Microcode::NodeCreationCallback
{
  list<MicrocodeNode *> nodes;

  void add_node (Microcode *, MicrocodeNode *node) {
    nodes.push_back (node);
  }
};

struct CmpConcreteAddress {
  bool operator() (const ConcreteAddress &a1, const ConcreteAddress &a2) {
    return a1.get_address () < a2.get_address ();
  }
};

/* This is disabled until the decoder is imported */
Microcode *
Build_Microcode (MicrocodeArchitecture *mcarch, ConcreteMemory *mem, 
		 const ConcreteAddress &start)
{
  const Architecture *arch = mcarch->get_reference_arch ();
  assert (! mem->is_undefined (start));
  set<ConcreteAddress, CmpConcreteAddress> visited;
  set<ConcreteAddress, CmpConcreteAddress> tovisit;
  Decoder *decoder = DecoderFactory::get_Decoder(mcarch, mem);
  Microcode *mc = new Microcode ();
  MCNodeCreate newnodes;
  mc->add_node_creation_callback (&newnodes);

  mc->set_entry_point (MicrocodeAddress (start.get_address ()));
  tovisit.insert (start);
  try
    {      
      while (! tovisit.empty ())
	{
	  ConcreteAddress addr = *tovisit.begin ();
	  tovisit.erase (addr);
	  visited.insert (addr);

	  ConcreteAddress next = decoder->decode (mc, addr);
	  while (!newnodes.nodes.empty ())
	    {
	      MicrocodeNode *node = newnodes.nodes.front ();
	      if (node->get_loc ().getLocal () == 0)
		{
		  ConcreteAddress ctgt (node->get_loc ().getGlobal ());
			  
		  if ((!mem->is_undefined (ctgt)) && 
		      visited.find (ctgt) == visited.end () && 
		      tovisit.find (ctgt) == tovisit.end ())
		    tovisit.insert (ctgt);
		}

	      newnodes.nodes.pop_front ();

	      std::vector<StmtArrow *> *successors = node->get_successors ();
	      std::vector<StmtArrow *>::iterator s = successors->begin ();

	      for (; s != successors->end (); s++)
		{
		  StmtArrow *arrow = *s;
		  StaticArrow *sa = dynamic_cast<StaticArrow *> (arrow);
		  MicrocodeAddress tgt;
		  bool tgt_is_defined = false;

		  if (sa == NULL)
		    {
		      DynamicArrow *da = dynamic_cast<DynamicArrow *> (*s);
		      MemCell *mc = dynamic_cast<MemCell *> (da->get_target ());

		      if (mc != NULL && mc->get_addr ()->is_Constant ())
			{
			  Constant *cst = 
			    dynamic_cast<Constant *> (mc->get_addr ());
			  ConcreteAddress a (cst->get_val());

			  if (! mem->is_undefined (a))
			    {
			      ConcreteValue val = 
				mem->get (a, arch->address_range, 
					  arch->endianness);
			      tgt = MicrocodeAddress (val.get ());
			      tgt_is_defined = true;
			    }
			}
		    }
		  else
		    {
		      tgt = sa->get_target();
		      tgt_is_defined = true;
		    }

		  if (tgt_is_defined && tgt.getLocal () == 0)
		    {
		      ConcreteAddress ctgt (tgt.getGlobal ());
			  
		      if ((! mem->is_undefined (ctgt)) && 
			  visited.find (ctgt) == visited.end () && 
			  tovisit.find (ctgt) == tovisit.end ())
			tovisit.insert (ctgt);
		    }	
		}
	    }
        }
    }
  catch (std::exception &e)
    {
      delete mc;
      delete decoder;
      throw;
    }

  delete decoder;

  mc->remove_node_creation_callback (&newnodes);

  return mc;
}

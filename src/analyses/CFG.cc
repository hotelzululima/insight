/*-
 * Copyright (C) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
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
#include "CFG.hh"

#include <algorithm>
#include <kernel/annotations/SolvedJmpAnnotation.hh>

using namespace std;

struct CFG_BasicBlockImpl;

struct CFG_EdgeImpl : public CFG_Edge
{
  CFG_EdgeImpl () : src (NULL), tgt (NULL) { }
  virtual ~CFG_EdgeImpl () {}

  bool operator == (const CFG_Edge &e) const;

  string pp () const;
  virtual CFG_BasicBlock *get_src () const;
  virtual CFG_BasicBlock *get_tgt () const;

  CFG_BasicBlockImpl *src;
  CFG_BasicBlockImpl *tgt;
};

struct CFG_BasicBlockImpl : public CFG_BasicBlock
{
  CFG_BasicBlockImpl () : nodes (), in (), out () { }
  virtual ~CFG_BasicBlockImpl () {
    for (list<CFG_EdgeImpl *>::iterator ei = in.begin(); ei != in.end (); ei++)
      delete *ei;
  }

  bool operator == (const CFG_BasicBlock &bb) const;
  string pp () const;
  virtual MicrocodeNode *get_entry () const;
  virtual MicrocodeNode *get_exit () const;

  vector<MicrocodeNode *> nodes;
  list<CFG_EdgeImpl *> in;
  list<CFG_EdgeImpl *> out;
};


static vector<MicrocodeNode *> *
s_build_successors (const Microcode *prog, const MicrocodeNode *node)
{
  vector<MicrocodeNode *> *result = new vector<MicrocodeNode *> ();

  MicrocodeNode_iterate_successors (*node, succ)
    {
      StmtArrow *a = *succ;

      if (a->is_static ())
	{
	  StaticArrow *sa = (StaticArrow *) a;
	  MicrocodeAddress tgt = sa->get_target ();

	  result->push_back (prog->get_node (tgt));
	}
      else if (a->has_annotation (SolvedJmpAnnotation::ID))
	{
	  SolvedJmpAnnotation *sja = (SolvedJmpAnnotation *)
	    a->get_annotation (SolvedJmpAnnotation::ID);

	  for (SolvedJmpAnnotation::const_iterator i = sja->begin ();
	       i != sja->end (); i++)
	    result->push_back (prog->get_node (*i));
	}
    }

  return result;
}

static CFG_BasicBlockImpl *
s_split_basic_block (CFG *cfg, CFG_BasicBlockImpl *bb, MicrocodeNode *new_ep,
		     map<MicrocodeNode *, CFG_BasicBlock *> &done)
{
  vector<MicrocodeNode *>::size_type i;
  CFG_BasicBlockImpl *result = (CFG_BasicBlockImpl *) cfg->new_node (new_ep);

  for (i = 0; i < bb->nodes.size () && bb->nodes.at (i) != new_ep; i++)
    /* nop */;
  int eppos = i;
  for (i++; i < bb->nodes.size (); i++)
    {
      MicrocodeNode *n = bb->nodes.at (i);
      result->nodes.push_back (n);
      done[n] = result;
    }
  assert (eppos > 0);
  bb->nodes.resize (eppos);

  // change src of out edges to point to new bb and add these edges to result's
  // output list
  for (list<CFG_EdgeImpl *>::iterator e = bb->out.begin ();
       e !=  bb->out.end (); e++)
    {
      (*e)->src = result;
      result->out.push_back (*e);
    }

  // create new edge between splitted parts of bb
  bb->out.clear ();
  cfg->add_edge (bb, result);

  return result;
}

static void
s_add_successor (CFG *cfg, CFG_BasicBlockImpl *&bb, MicrocodeNode *s,
		 bool merge,
		 list<CFG_BasicBlockImpl *> &todo,
		 map<MicrocodeNode *, CFG_BasicBlock *> &done)
{
  map<MicrocodeNode *, CFG_BasicBlock *>::iterator sp = done.find (s);
  CFG_BasicBlockImpl *sbb = NULL;

  if (sp == done.end ())
    {
      if (! merge)
	{
	  sbb = (CFG_BasicBlockImpl *) cfg->new_node (s);
	  cfg->add_edge (bb, sbb);
	  todo.push_back (sbb);
	}
      else
	{
	  bb->nodes.push_back (s);
	  done[s] = bb;
	  todo.push_back (bb);
	}
    }
  else
    {
      sbb = (CFG_BasicBlockImpl *) sp->second;

      if (sbb->nodes.at (0) != s)
	{
	  // we point in the middle of a BB; split it.
	  CFG_BasicBlockImpl *nbb = s_split_basic_block (cfg, sbb, s, done);
	  if (find (todo.begin (), todo.end (), sbb) != todo.end ())
	    {
	      todo.remove (sbb);
	      todo.push_back (nbb);
	    }

	  if (sbb == bb)
	    {
	      cfg->add_edge (nbb, nbb);
	      bb = nbb;
	    }
	  else
	    cfg->add_edge (bb, nbb);
	}
      else
	{
	  cfg->add_edge (bb, sbb);
	}
    }
}

CFG::CFG () : GraphInterface<CFG_BasicBlock, CFG_Edge, CFG_NodeStore> (),
	      nodes (), node2bb ()
{
}

CFG::~CFG ()
{
  for (node_iterator i = nodes.begin (); i != nodes.end (); i++)
    delete *i;
}


CFG *
CFG::createFromMicrocode (const Microcode *prog, const MicrocodeAddress &start)
{
  CFG *result = new CFG ();

  MicrocodeNode *ep = prog->get_node (start);
  CFG_BasicBlockImpl *bb = (CFG_BasicBlockImpl *) result->new_node (ep);
  result->entrypoint = bb;
  list<CFG_BasicBlockImpl *> todo;

  result->node2bb[ep] = bb;
  todo.push_back (bb);

  while (! todo.empty())
    {
      bb = *todo.begin ();
      todo.pop_front();

      ep = bb->nodes.at (bb->nodes.size () - 1);
      vector<MicrocodeNode *> *succ = s_build_successors (prog, ep);

      for (vector<MicrocodeNode *>::size_type i = 0; i < succ->size (); i++)
	{
	  MicrocodeNode *s = succ->at (i);
	  s_add_successor (result, bb, s, succ->size () == 1, todo,
			   result->node2bb);
	}

      delete succ;
    }

  return result;
}

CFG::const_node_iterator
CFG::begin_nodes () const
{
  return nodes.begin ();
}

CFG::const_node_iterator
CFG::end_nodes () const
{
  return nodes.end ();
}

CFG::node_iterator
CFG::begin_nodes ()
{
  return nodes.begin ();
}

CFG::node_iterator
CFG::end_nodes ()
{
  return nodes.end ();
}

CFG::node_type *
CFG::get_entry_point () const
{
  return entrypoint;
}

std::string
CFG::get_label_node (CFG::node_type *n) const
{
  ostringstream oss;

  oss << "0x" << std::hex << n;
  return oss.str ();
}

std::pair<CFG::edge_type *, CFG::node_type *>
CFG::get_first_successor (node_type *n) const
{
  std::pair<CFG::edge_type *, CFG::node_type *> result(NULL,NULL);
  CFG_BasicBlockImpl *ni = (CFG_BasicBlockImpl *) n;

  if (! ni->out.empty ())
    {
      result.first = *(ni->out.begin ());
      result.second = (*ni->out.begin ())->tgt;
    }

  return result;
}

std::pair<CFG::edge_type *, CFG::node_type *>
CFG::get_next_successor (CFG::node_type *n, CFG::edge_type *e) const
{
  std::pair<CFG::edge_type *, CFG::node_type *> result (NULL, NULL);
  list<CFG_EdgeImpl *>::iterator i = ((CFG_BasicBlockImpl *) n)->out.begin ();

  for (; i != ((CFG_BasicBlockImpl *) n)->out.end (); i++)
    if (e == *i)
      {
	i++;
	break;
      }
  if (i != ((CFG_BasicBlockImpl *) n)->out.end ())
    {
      result.first = *i;
      result.second = (*i)->tgt;
    }

  return result;
}

CFG::node_type *
CFG::get_source (CFG::edge_type *e) const
{
  return ((CFG_EdgeImpl *) e)->src;
}

CFG::node_type *
CFG::get_target (CFG::edge_type *e) const
{
  return ((CFG_EdgeImpl *) e)->tgt;
}

void
CFG::output_text(std::ostream & out) const
{
  for (const_node_iterator i = nodes.begin (); i != nodes.end (); i++)
    out << (*i)->pp () << endl;
}

CFG::node_type *
CFG::new_node (MicrocodeNode *entry)
{
  CFG_BasicBlockImpl *result = new CFG_BasicBlockImpl ();

  result->nodes.push_back (entry);
  nodes.push_back (result);
  node2bb[entry] = result;

  return result;
}

void
CFG::add_edge (node_type *src, node_type *tgt)
{
  CFG_EdgeImpl *e = new CFG_EdgeImpl ();
  e->src = dynamic_cast<CFG_BasicBlockImpl *> (src);
  e->tgt = dynamic_cast<CFG_BasicBlockImpl *> (tgt);
  e->src->out.push_back (e);
  e->tgt->in.push_back (e);
}

bool
CFG_EdgeImpl::operator == (const CFG_Edge &e) const
{
  return this == &e;
}

static void
s_output_jmp_arrow (ostream &out, StmtArrow *a)
{
  if (!(a->get_stmt ()->is_Skip () || a->get_stmt ()->is_Jump ()))
    return;

  out << "(";
  if (a->get_condition () == NULL ||
      a->get_condition ()->is_TrueFormula ())
    out << "1";
  else
    a->get_condition ()->output_text (out);
  out << ",";
  if (a->get_stmt () != NULL)
    out << " " << a->get_stmt ()->pp ();
  out << ")";
}

string
CFG_EdgeImpl::pp () const
{
  ostringstream oss;

  MicrocodeNode *srcnode = src->get_exit ();

  if (srcnode->get_successors ()->size () == 1)
    {
      StmtArrow *a = srcnode->get_successors ()->at (0);
      s_output_jmp_arrow (oss, a);
    }
  else
    {
      MicrocodeNode_iterate_successors (*srcnode, succ)
	{
	  StaticArrow *sa = dynamic_cast<StaticArrow *> (*succ);
	  if (sa == NULL ||
	      sa->get_target ().equals(tgt->get_entry ()->get_loc ()))
	    s_output_jmp_arrow (oss, *succ);
	}
    }

  return oss.str ();
}

CFG_BasicBlock *
CFG_EdgeImpl::get_src () const
{
  return src;
}

CFG_BasicBlock *
CFG_EdgeImpl::get_tgt () const
{
  return tgt;
}

bool
CFG_BasicBlockImpl::operator == (const CFG_BasicBlock &bb) const
{
  return this == &bb;
}

string
CFG_BasicBlockImpl::pp () const
{
  ostringstream oss;
  oss << "BB_" << std::hex << this << " : "
      << nodes.at(0)->get_loc () << " ... "
      << nodes.at(nodes.size () - 1)->get_loc ()
      << endl << endl;
  for (vector<MicrocodeNode *>::size_type i = 0; i < nodes.size (); i++)
    {
      MicrocodeNode *node = nodes.at(i);

      if (node->get_successors ()->size () == 1)
	{
	  StmtArrow *a = node->get_successors ()->at (0);
	  if (a->is_static ())
	    {
	      StaticArrow *sa = (StaticArrow *) a;
	      if (a->get_stmt()->is_Skip ())
		oss << a->get_stmt ()->pp () << " " << sa->get_target ();
	      else
		oss << a->get_stmt ()->pp ();
	    }
	  else
	    {
	      DynamicArrow *da = (DynamicArrow *) a;
	      oss << a->get_stmt () << " ";
	      da->get_target ()->output_text (oss);
	    }
	  oss << endl;
	}
      else
	{
	  oss << "  " << node->pp () << endl;
	}
    }
  return oss.str ();
}

MicrocodeNode *
CFG_BasicBlockImpl::get_entry () const
{
  assert (! nodes.empty ());
  return nodes.at (0);
}

MicrocodeNode *
CFG_BasicBlockImpl::get_exit () const
{
  assert (! nodes.empty ());
  return nodes.at (nodes.size () - 1);
}

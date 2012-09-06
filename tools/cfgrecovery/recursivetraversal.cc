/*-
 * Copyright (C) 2012, Centre National de la Recherche Scientifique,
 *                     Institut Polytechnique de Bordeaux,
 *                     Universite Bordeaux 1.
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

#include "recursivetraversal.hh"

#include <stdlib.h>
#include <utils/logs.hh>
#include <kernel/annotations/CallRetAnnotation.hh>
#include <analyses/slicing/Slicing.hh>
#include <tr1/unordered_map>

#include "FloodTraversal.hh"

using namespace std;
using namespace std::tr1;

class RecursiveTraversal : public FloodTraversal
{
  struct CA_Hash { 
    size_t operator()(const ConcreteAddress &F) const {
      return F.get_address ();
    }
    bool operator()(const ConcreteAddress &F1, 
		    const ConcreteAddress &F2) const {
      return F1 == F2;
    }
  };

  list<ConcreteAddress> stack;

  unordered_map<ConcreteAddress, pair<MicrocodeNode *, Expr *>,
		CA_Hash, CA_Hash > call_ret_store;



public :
  RecursiveTraversal (const ConcreteMemory *memory, Decoder *decoder) 
    : FloodTraversal (false, memory, decoder), stack ()
  {
  }
      
  ~RecursiveTraversal ()
  {
  }

protected:
  void treat_new_arrow (Microcode *mc, 
			const MicrocodeNode *entry, const StmtArrow *arrow, 
			const ConcreteAddress &next)
  {    
    FloodTraversal::treat_new_arrow (mc, entry, arrow, next);

    MicrocodeNode *src = arrow->get_src ();

    if (! src->has_annotation (CallRetAnnotation::ID))
      return;

    CallRetAnnotation *an = (CallRetAnnotation *) 
      src->get_annotation (CallRetAnnotation::ID);
    if (an->is_call ())
      {
	const Expr *tgt = an->get_target ();
	ConcreteAddress ctgt;
	bool ctgt_is_defined = false;
	if (tgt->is_Constant ())
	  {
	    const Constant *c = dynamic_cast<const Constant *> (tgt);
	    ctgt = ConcreteAddress (c->get_val ());
	    ctgt_is_defined = true;
	  }
	else if (tgt->is_MemCell ())
	  {
	    const MemCell *mc = dynamic_cast<const MemCell *> (tgt);
      
	    if (mc != NULL && mc->get_addr ()->is_Constant ())
	      {
		Constant *cst = dynamic_cast<Constant *> (mc->get_addr ());
		ConcreteAddress a (cst->get_val());
	  
		if (mem->is_defined(a))
		  {
		    const Architecture *arch = 
		      decoder->get_arch ()->get_reference_arch ();
		    ConcreteValue val = 
		      mem->get (a, arch->get_address_size (), 
				arch->get_endian ());
		    ctgt = ConcreteAddress (val.get ());
		    ctgt_is_defined = true;
		  }
	      }
	  }
  
	if (ctgt_is_defined && mem->is_defined (ctgt))
	  {
	    if (already_visited (ctgt))
	      {		    
		address_t na = next.get_address ();
		assert (! (call_ret_store.find (ctgt) == 
			   call_ret_store.end ()));
		pair<MicrocodeNode *, Expr *> retnode = call_ret_store[ctgt];
		Expr *rettgt = retnode.second;
		Expr *cond =
		  Expr::createEquality (rettgt->ref (),
					Constant::create (na, 0, 
							  rettgt->get_bv_size ()));
		MicrocodeAddress nma (na);
		MicrocodeNode *tgt = mc->get_or_create_node (nma);
		StmtArrow *a =
		  retnode.first->add_successor (cond, tgt, new Skip ());
		FloodTraversal::treat_new_arrow (mc, entry, a, next);
	      }
	    else
	      {
		ConcreteAddress call (entry->get_loc ().getGlobal ());
		assert (call_ret_store.find (next) == call_ret_store.end ());
		stack.push_front (ctgt);
		stack.push_front (next);
	      }
	  }
      }
    else if (! stack.empty ())
      {
	ConcreteAddress ret(stack.front ());
	stack.pop_front ();
	ConcreteAddress call(stack.front ());
	stack.pop_front ();
	if (can_visit (ret))
	  {
	    const DynamicArrow *da = dynamic_cast<const DynamicArrow *> (arrow);

	    if (da != NULL)
	      {
		Expr *target = da->get_target ();
		int targetsz = target->get_bv_size ();
		call_ret_store[call].first = arrow->get_src ();
		call_ret_store[call].second = target;
		address_t na = ret.get_address ();
		Expr *cond =
		  Expr::createEquality (target->ref (),
					Constant::create (na, 0, targetsz));
		MicrocodeAddress nma (na);
		MicrocodeNode *tgt = mc->get_or_create_node (nma);
		StmtArrow *a =
		  arrow->get_src ()->add_successor (cond, tgt, new Skip ());
		FloodTraversal::treat_new_arrow (mc, entry, a, next);
	      }
	    else
	      {
		add_to_todo_list (ret);
	      }
	  }
      }
    else
      {
	logs::error << src->get_loc ()
		   << ": error: ret without matching call" << endl;
      }
  }
};

/* Recursive traversal disassembly method */
Microcode *
recursivetraversal (const ConcreteAddress * entrypoint,
		    ConcreteMemory * memory,
		    Decoder * decoder)
{
  Microcode * mc = new Microcode();
  RecursiveTraversal rt (memory, decoder);

  rt.compute (mc, *entrypoint);

  return mc;
}

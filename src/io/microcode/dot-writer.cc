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
#include <set>
#include <kernel/microcode/MicrocodeNode.hh>
#include <kernel/annotations/AsmAnnotation.hh>
#include "dot-writer.hh"

using namespace std;

static void
s_successor_instructions_rec (const Microcode *mc, const MicrocodeNode *node, 
			      set<MicrocodeNode *> &done,
			      vector<MicrocodeNode *> &res)
{
  MicrocodeNode_iterate_successors (*node, succ)
    {
      if (! (*succ)->is_static ())
	continue;

      MicrocodeAddress tgt = ((StaticArrow *) *succ)->get_target ();
      MicrocodeNode *n = mc->get_node (tgt);
            
      if (tgt.getLocal () == 0)
	res.push_back (n);
      else if (done.find (n) == done.end ())
	{
	  done.insert (n);
	  s_successor_instructions_rec (mc, n, done, res);
	}
    }
}


static vector<MicrocodeNode *>
s_successor_instructions (const Microcode *mc, const MicrocodeNode *node)
{
  set<MicrocodeNode *> done;
  vector<MicrocodeNode *> result;
  
  s_successor_instructions_rec (mc, node, done, result);

  return result;
}


void 
dot_writer (std::ostream &out, const Microcode *mc, bool asm_only)
{
  if (! asm_only)
    {
      mc->toDot (out);
      return;
    }

  out << "digraph G { \n";
  std::vector<MicrocodeNode *>* ns = mc->get_nodes();
  for (typename std::vector<MicrocodeNode *>::iterator it = ns->begin(); 
       it != ns->end(); ++it)
    {
      MicrocodeNode *n = *it;
      std::string pp;

      MicrocodeAddress ma = n->get_loc ();
      if (ma.getLocal () != 0)
	continue;

      out << "cfg_" << ma.getGlobal () << "_" << ma.getLocal ()
	  << "[shape=box,style=filled,color=oldlace,label=\"";

      if (n->has_annotation (AsmAnnotation::ID))
	out << setw(8) << hex << ma.getGlobal () << ": " 
	    << *n->get_annotation (AsmAnnotation::ID);
      else
	out << n->pp ();

      out << "\"];\n";
      vector<MicrocodeNode *> succs = s_successor_instructions (mc, n);

      for (vector<MicrocodeNode *>::const_iterator s = succs.begin (); 
	   s != succs.end (); s++)
	{
	  MicrocodeAddress tgt = (*s)->get_loc ();
	  assert (tgt.getLocal () == 0);

	  out << "cfg_" << ma.getGlobal () << "_" << ma.getLocal () 
	      << " -> "
	      << "cfg_" << tgt.getGlobal () << "_" << tgt.getLocal () 
	      << "; " << endl;
	}

    }

  out << "}; " << std::endl;
  out.flush (); 
}

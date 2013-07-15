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
#include <list>
#include <kernel/microcode/MicrocodeNode.hh>
#include <kernel/annotations/AsmAnnotation.hh>
#include <kernel/annotations/SolvedJmpAnnotation.hh>
#include <cstdlib>
#include "dot-writer.hh"

using namespace std;

static void
s_successor_instructions_rec (const Microcode *mc, const MicrocodeNode *node, 
			      set<MicrocodeNode *> &done,
			      vector<MicrocodeNode *> &res)
{
  MicrocodeNode_iterate_successors (*node, succ)
    {
      list<MicrocodeAddress> addresses;

      if ((*succ)->is_static ())
	addresses.push_back (((StaticArrow *) *succ)->get_target ());
      else if ((*succ)-> has_annotation (SolvedJmpAnnotation::ID))
	{
	  SolvedJmpAnnotation *sja = (SolvedJmpAnnotation *)
	    (*succ)->get_annotation (SolvedJmpAnnotation::ID);
	  addresses = sja->get_value ();
	}

      for (list<MicrocodeAddress>::const_iterator i = addresses.begin ();
	   i != addresses.end (); i++)
	{
	  MicrocodeAddress tgt = *i;
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
dot_writer (std::ostream &out, const Microcode *mc, bool asm_only,
	    const std::string &graphlabel, 
	    ConcreteAddress *entrypoint, BinaryLoader *loader)
{
  if (! asm_only)
    {
      mc->toDot (out);
      return;
    }

  static int primes[] = { 5483, 10967, 21933, 43867,  87731, 175459, 350919, 
			  701833, 1403667, 2807333 , 5614667, 11229331, 
			  16777253 };
  static int nb_primes = sizeof (primes) / sizeof (primes[0]);

  map<string,int> symbols;
  int rgb = 0xfdf5e6;

  out << "digraph G { " << endl
      << " splines=ortho; " << endl;

  if (! graphlabel.empty ())
    out << " label=\"" << graphlabel << "\"; " << endl;

  for (Microcode::node_iterator it = mc->begin_nodes (); 
       it != mc->end_nodes(); ++it)
    {
      std::string pp;

      MicrocodeAddress ma = n->get_loc ();
      if (ma.getLocal () != 0)
	continue;

      if (loader )
	{
	  Option<string> fun = loader->get_symbol_name (ma.getGlobal ());

	  if (fun.hasValue ())
	    {
	      string s = fun.getValue ();
	      rgb = 0;
	      int k = 0;
	      for (string::size_type i = 0; i < s.length (); i++)
		{
		  rgb = primes[k] * s[i] + (rgb << 3);
		  k = (k+1) % nb_primes;
		}
	      int b = rgb & 0xFF000000;
	      rgb ^= (b >> 8)|(b>> 16)|(b>>24);
	      rgb &= 0x00FFFFFF;
	      symbols[s] = rgb;
	    }
	}

      out << "cfg_" << std::hex << ma.getGlobal () << "_" << ma.getLocal ()
	  << "[shape=box,style=filled,fillcolor=\"#" 
	  << hex << rgb << "\",label=\"";
      
      if (n->has_annotation (AsmAnnotation::ID))
	out << setw(8) << hex << ma.getGlobal () << ": " 
	    << *n->get_annotation (AsmAnnotation::ID);
      else
	out << n->pp ();

      out << "\"";

      if (entrypoint && ma.getGlobal() == entrypoint->get_address ())
	out << ",color=red,peripheries=2";
      else
	out << ",color=\"#" << hex << rgb << "\"";
      out << "];\n";

      vector<MicrocodeNode *> succs = s_successor_instructions (mc, n);

      set<MicrocodeAddress,LessThanFunctor<MicrocodeAddress> > targets;

      for (vector<MicrocodeNode *>::const_iterator s = succs.begin (); 
	   s != succs.end (); s++)
	{
	  MicrocodeAddress tgt = (*s)->get_loc ();

	  if (targets.find (tgt) != targets.end ())
	    continue;

	  assert (tgt.getLocal () == 0);
	  targets.insert (tgt);

	  out << "cfg_" << std::hex << ma.getGlobal () << "_" << ma.getLocal () 
	      << " -> "
	      << "cfg_" << std::hex << tgt.getGlobal () << "_" 
	      << tgt.getLocal () 
	      << "; " << endl;
	}
    }

  out << " subgraph cluster_legend { " << endl
      << "  label=\"Symbols\"; " << endl;
  int k = 0;
  for (map<string,int>::const_iterator i = symbols.begin (); 
       i != symbols.end (); i++, k++)
    {      
      out << " sym_" << k << "[label=\"" << i->first << "\","
	  << "shape=box,style=filled,color=\"#" << std::hex << i->second 
	  << "\"]; " << endl;
    }
  out << " }; " << endl;
  k = 0;
  for (map<string,int>::const_iterator i = symbols.begin (); 
       i != symbols.end (); i++, k++)
    {
      out << "sym_" << k << " -> cfg_" << std::hex 
	  << loader->get_symbol_value (i->first).getValue ().get_address () 
	  << "_0; " << endl;
    }
  out << "} " << std::endl;
  out.flush (); 
}

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
#include <vector>
#include <list>
#include <kernel/microcode/MicrocodeNode.hh>
#include <kernel/annotations/AsmAnnotation.hh>
#include <kernel/annotations/SolvedJmpAnnotation.hh>
#include <cstdlib>
#include "asm-writer.hh"
#include "dot-writer.hh"

using namespace std;

#define NODE_PREFIX "BB_0x"

struct basic_block_t 
{
  int ident;
  int in_degree;
  vector<MicrocodeNode *> *nodes;
  vector<MicrocodeNode *> *succs;
};

static bool 
s_sort_microcode (MicrocodeNode *e1, MicrocodeNode *e2)
{
  return (*e1) < (*e2);
}

static void 
s_init_basic_block (const Microcode *mc, MicrocodeNode *n, basic_block_t &bb,
		    int ident)
{  
  bb.ident = ident;
  bb.in_degree = 0;
  bb.nodes = new vector<MicrocodeNode *> ();
  bb.nodes->push_back (n);
  bb.succs = asm_get_successor_instructions (mc, n);
}

static void 
s_clear_basic_block (basic_block_t &bb)
{
  delete bb.nodes;
  delete bb.succs;
}

static vector<MicrocodeNode *> *
s_compute_asm_nodes (const Microcode *mc, 
		     std::map<MicrocodeNode *, basic_block_t> &anodes)
{
  const vector<MicrocodeNode *> *nodes = mc->get_nodes ();
  vector<MicrocodeNode *> *result = new vector<MicrocodeNode *> ();

  for (size_t i = 0; i < nodes->size (); i++) 
    {
      MicrocodeNode *n = nodes->at (i);

      assert (! n->has_annotation (AsmAnnotation::ID) || 
	      n->get_loc ().getLocal() == 0);
      if (! n->has_annotation (AsmAnnotation::ID))
	continue;

      if (anodes.find (n) == anodes.end ())
	s_init_basic_block (mc, n, anodes[n], anodes.size ());
      result->push_back (n);
      
      basic_block_t &an = anodes[n];
      for (size_t s = 0; s < an.succs->size (); s++)
	{
	  MicrocodeNode *sn = an.succs->at (s);
	  if (anodes.find (sn) == anodes.end ())
	    s_init_basic_block (mc, sn, anodes[sn], anodes.size ());
	  anodes[sn].in_degree++;
	}
    }
  std::sort (result->begin (), result->end (), s_sort_microcode);

  return result;
}

static void
s_merge_bb_from (basic_block_t *entry, 
		 std::map<MicrocodeNode *, basic_block_t> &anodes,
		 MicrocodeNode *entrypoint, const SymbolTable *symboltable)
{
  while (entry->succs->size () == 1)
    {
      Option<address_t> nextaddr =
	next_instruction_addr (entry->nodes->at (entry->nodes->size () - 1));

      MicrocodeNode *succ = entry->succs->at (0);
      assert (anodes.find (succ) != anodes.end ());
      basic_block_t &bbsucc = anodes[succ];
      if (bbsucc.in_degree > 1 || succ == entrypoint ||
	  symboltable->has (succ->get_loc ().getGlobal ()) ||
	  ! s_sort_microcode (entry->nodes->at (entry->nodes->size () - 1),
			      succ) ||
	  (nextaddr.hasValue () && nextaddr.getValue () != 
	   succ->get_loc ().getGlobal ()))
	return;
  
      for (size_t i = 0; i < bbsucc.nodes->size (); i++)
	entry->nodes->push_back (bbsucc.nodes->at (i));

      entry->succs->clear ();
      for (size_t i = 0; i < bbsucc.succs->size (); i++)
	entry->succs->push_back (bbsucc.succs->at (i));

      s_clear_basic_block (bbsucc);
      anodes.erase (anodes.find (succ));
    }
}

static void
s_merge_basic_blocks (vector<MicrocodeNode *> *nodes, 
		      std::map<MicrocodeNode *, basic_block_t> &anodes,
		      MicrocodeNode *entrypoint, const SymbolTable *symboltable)
{
  size_t nb_nodes = nodes->size ();

  for (size_t i = 0; i < nb_nodes; i++)
    {
      MicrocodeNode *n = nodes->at (i);

      if (anodes.find (n) == anodes.end ())
	continue;

      s_merge_bb_from (&anodes[n], anodes, entrypoint, symboltable);
    }
}

void 
dot_writer (std::ostream &out, const Microcode *mc, bool asm_only,
	    const std::string &graphlabel, 
	    ConcreteAddress *entrypoint, const SymbolTable *symboltable)
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

  std::map<MicrocodeNode *, basic_block_t> anodes;
  vector<MicrocodeNode *> *nodes = s_compute_asm_nodes (mc, anodes);
  MicrocodeNode *entrynode;
  if (entrypoint)
    entrynode = mc->get_node (entrypoint->get_address ());
  else
    entrynode = NULL;
 
  if (entrynode || symboltable)
    s_merge_basic_blocks (nodes, anodes, entrynode, symboltable);
 
  for (vector<MicrocodeNode *>::const_iterator i = nodes->begin (); 
       i != nodes->end (); i++)
    {
      MicrocodeNode *n = *i;
      if (anodes.find (n) == anodes.end ())
	continue;

      basic_block_t &bb = anodes[n];
      if (bb.nodes->size () == 1 && bb.succs->size () == 0)
	continue;

      MicrocodeAddress ma = n->get_loc ();
      assert (ma.getLocal () == 0);
      
      if (symboltable && symboltable->has (ma.getGlobal ()))
	{	  
	  string s = *symboltable->get (ma.getGlobal ()).begin ();
	  if (symbols.find (s) == symbols.end ())
	    {
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
	  else
	    {
	      rgb = symbols[s];
	    }
	}
      else
	{
	  rgb += ma.getGlobal () *3;
	  rgb &= 0x00FFFFFF;
	}
      
      if ((rgb & 0xFF0000) >> 16 < 0x7F)
	rgb += 0x7F0000;
      if ((rgb & 0xFF00) >> 8 < 0x7F)
	rgb += 0x7F00;
      if ((rgb & 0xFF) < 0x7F)
	rgb += 0x7F;

      out << NODE_PREFIX << std::hex << ma.getGlobal () 
	  << "[shape=box,style=filled,fillcolor=\"#" << std::hex << rgb 
	  << "\",justify=left,label=\"";
      for (size_t inst = 0; inst < bb.nodes->size (); inst++)
	{
	  MicrocodeNode *instn = bb.nodes->at (inst);
	  if (instn->has_annotation (AsmAnnotation::ID))
	    out << setw(8) << hex << instn->get_loc ().getGlobal () << " : " 
		<< *(instn->get_annotation (AsmAnnotation::ID)) << "\\l";
	  else
	    out << instn->pp();
	}
      out << "\"";
      if (n == entrynode)
	out << ",color=red,peripheries=2";
      else
	out << ",color=\"#" << hex << rgb << "\"";
      out << "];\n";

      set<MicrocodeAddress,LessThanFunctor<MicrocodeAddress> > targets;

      for (vector<MicrocodeNode *>::const_iterator s = bb.succs->begin (); 
	   s != bb.succs->end (); s++)
	{
	  MicrocodeAddress tgt = (*s)->get_loc ();

	  if (targets.find (tgt) != targets.end ())
	    continue;

	  assert (tgt.getLocal () == 0);
	  targets.insert (tgt);

	  out << NODE_PREFIX << std::hex << ma.getGlobal () 
	      << " -> "
	      << NODE_PREFIX << std::hex << tgt.getGlobal () 
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
  assert (symbols.size () == 0 || symboltable != NULL);
  for (map<string,int>::const_iterator i = symbols.begin (); 
       i != symbols.end (); i++, k++)
    {
      out << "sym_" << k << " -> " << NODE_PREFIX << std::hex 
	  << symboltable->get (i->first)
	  << endl;
    }
  out << "} " << std::endl;
  out.flush (); 
}

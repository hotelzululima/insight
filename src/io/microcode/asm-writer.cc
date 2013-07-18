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
#include <sstream>
#include <cassert>
#include <cstring>
#include <cstdio>
#include <list>
#include <tr1/unordered_map>
#include <kernel/annotations/NextInstAnnotation.hh>
#include <kernel/annotations/AsmAnnotation.hh>
#include <kernel/annotations/SolvedJmpAnnotation.hh>
#include "asm-writer.hh"

using namespace std;

static string 
s_instruction_bytes (const BinaryLoader *loader, const ConcreteAddress &start,
		     const ConcreteAddress &next)
{
  ostringstream result;
  ConcreteMemory *m = loader->get_memory ();

  for (ConcreteAddress a = start; ! a.equals (next); a++)
    result << hex << setfill('0') << setw (2) 
	   << m->get (a, 1, Architecture::LittleEndian).get () << ' ';
  return result.str ();
}

typedef tr1::unordered_map<address_t,string> SymbolTable;

static Option<address_t>
s_next_instruction_addr (const MicrocodeNode *node)
{
  Option<address_t> next;
  if (node->has_annotation (NextInstAnnotation::ID))
    {
      NextInstAnnotation *nia = (NextInstAnnotation *)
	node->get_annotation (NextInstAnnotation::ID);
      next = nia->get_value ().getGlobal ();
    }  

  return next;
}

static bool
s_is_next_instruction_addr (const MicrocodeNode *node, address_t a)
{
  Option<address_t> next = s_next_instruction_addr (node);

  return next.hasValue () && next.getValue () == a;
}

static SymbolTable *
s_build_symbol_table (const Microcode *mc, const BinaryLoader *loader)
{
  const char *label_prefix = "L";
  char *tmpbuf = new char[::strlen (label_prefix) + 10];
  int label_index = 0;
  list<address_t> addrtable;
  SymbolTable *result = new SymbolTable ();
  
  for (Microcode::node_iterator pN = mc->begin_nodes (); pN != mc->end_nodes ();
       pN++)
    {
      MicrocodeNode *N = *pN;
      MicrocodeAddress Nma = N->get_loc ();

      if (Nma.getLocal () != 0)
	continue;

      vector<MicrocodeNode *> *succinsts = 
	asm_get_successor_instructions (mc, N);
      int nb_succ = succinsts->size ();
      if (Nma.getLocal () == 0)
	{	  
	  address_t a = Nma.getGlobal ();
	  Option<string> symb = loader->get_symbol_name (a);
	  if (symb.hasValue ())
	    (*result)[a] = symb.getValue ();
	}

      for (int i = 0; i <nb_succ; i++)
	{
	  MicrocodeNode *succ = succinsts->at (i);
	  assert (succ->get_loc ().getLocal () == 0);

	  address_t a = succ->get_loc ().getGlobal ();
	  if (result->find (a) == result->end () &&
	      ! s_is_next_instruction_addr (N, a))
	    addrtable.push_back (a);	      
	}
      delete succinsts;
    }

  for (list<address_t>::iterator i = addrtable.begin (); i != addrtable.end ();
       i++)
    {
      if (result->find (*i) != result->end ())
	continue;

      do
	{
	  sprintf (tmpbuf, "%s_%x", label_prefix, label_index);
	  label_index++;
	}
      while (loader->get_symbol_value (tmpbuf).hasValue ());
      assert (result->find (*i) == result->end ());
      (*result)[*i] = tmpbuf;
    }

  return result;
}

void 
asm_writer (ostream &out, const Microcode *mc, const BinaryLoader *loader,
	    bool with_bytes)
{
  int i;
  vector<MicrocodeNode *> *nodes = mc->get_nodes ();
  int nb_nodes = nodes->size ();
  SymbolTable *symbtable = s_build_symbol_table (mc, loader);

  for (i = 0; i < nb_nodes; i++)
    {
      MicrocodeNode *node = nodes->at(i);

      if (! node->has_annotation (AsmAnnotation::ID))
	continue;
      MicrocodeAddress ma (node->get_loc ());

      if (ma.getLocal () == 0)
	{
	  SymbolTable::iterator j = symbtable->find (ma.getGlobal ());
	  if (j != symbtable->end ())
	    {
	      out << right << hex << setfill ('0') 
		  << setw (8) 
		  << ma.getGlobal () 
		  << setw (0) 
		  << " <" << j->second << ">: " << endl;
	    }
	}
      AsmAnnotation *a = (AsmAnnotation *) 
	node->get_annotation (AsmAnnotation::ID);
      Option<address_t> next = s_next_instruction_addr (node);
      out << right << hex << setw (8) << setfill (' ')
	  << node->get_loc ().getGlobal () << ":\t";
      if (with_bytes)
	{
	  string bytes;

	  if (next.hasValue ())
	    bytes = 
	      s_instruction_bytes (loader, ma.getGlobal (), next.getValue ());
	  else
	    bytes = "(unknown)";
	  out << left << setw (24) << setfill (' ') << bytes << "\t";
	}
      out << a->get_value ();      
      vector<MicrocodeNode *> *succ = asm_get_successor_instructions (mc, node);
      int nb_succ = succ->size ();
      bool first = true;
      for (int s = 0; s < nb_succ; s++)
	{
	  MicrocodeNode *instr = succ->at (s);
	  address_t saddr = instr->get_loc ().getGlobal ();
	  if (next.hasValue () && next.getValue () == saddr)
	    continue;

	  SymbolTable::iterator sname = symbtable->find (saddr);
	  assert (sname != symbtable->end ());
	    {
	      if (first) { out << " # jump to : " ; first = false; }
	      else { out << ", "; }
	      out << sname->second;
	    }
	}
      delete succ;
      out << endl;
    }

  delete symbtable;
}


static void
s_successor_instructions_rec (const Microcode *mc, const MicrocodeNode *node, 
			      set<MicrocodeNode *> &done,
			      vector<MicrocodeNode *> *res)
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
	    res->push_back (n);
	  else if (done.find (n) == done.end ())
	    {
	      done.insert (n);
	      s_successor_instructions_rec (mc, n, done, res);
	    }
	}
    }
}

vector<MicrocodeNode *> *
asm_get_successor_instructions (const Microcode *mc, const MicrocodeNode *node)
{
  set<MicrocodeNode *> done;
  vector<MicrocodeNode *> *result = new vector<MicrocodeNode *> ();
  
  s_successor_instructions_rec (mc, node, done, result);

  return result;
}

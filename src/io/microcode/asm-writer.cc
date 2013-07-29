/*
 * Copyright (c) 2010-2013, Centre National de la Recherche Scientifique,
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
s_instruction_bytes (const ConcreteMemory *memory, const ConcreteAddress &start,
		     const ConcreteAddress &next)
{
  ostringstream result;

  for (ConcreteAddress a = start; ! a.equals (next); a++)
    result << hex << setfill('0') << setw (2) 
	   << memory->get (a, 1, Architecture::LittleEndian).get () << ' ';
  return result.str ();
}

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
s_build_symbol_table (const Microcode *mc, const SymbolTable *symboltable,
		      bool with_labels)
{
  const char *label_prefix = "L";
  int label_index = 0;
  list<address_t> addrtable;
  SymbolTable *result = symboltable->clone ();
  
  if (! with_labels)
    return result;

  for (Microcode::node_iterator pN = mc->begin_nodes (); 
       pN != mc->end_nodes (); pN++)
    {
      MicrocodeNode *N = *pN;
      MicrocodeAddress Nma = N->get_loc ();
      
      if (Nma.getLocal () != 0)
	continue;

      vector<MicrocodeNode *> *succinsts = 
	asm_get_successor_instructions (mc, N);
      int nb_succ = succinsts->size ();

      for (int i = 0; i <nb_succ; i++)
	{
	  MicrocodeNode *succ = succinsts->at (i);
	  assert (succ->get_loc ().getLocal () == 0);

	  address_t a = succ->get_loc ().getGlobal ();
	  if (! result->has (a) && ! s_is_next_instruction_addr (N, a))
	    addrtable.push_back (a);	      
	}
      delete succinsts;
    }

  char *tmpbuf = new char[::strlen (label_prefix) + 10];
  for (list<address_t>::iterator i = addrtable.begin (); i != addrtable.end ();
       i++)
    {
      if (result->has (*i))
	continue;

      do
	{
	  sprintf (tmpbuf, "%s_%x", label_prefix, label_index);
	  label_index++;
	}
      while (result->has (tmpbuf));
      result->add_symbol (tmpbuf, *i);
    }
  delete[] tmpbuf;

  return result;
}

static void
s_dump_memory_between (ostream &out, const ConcreteMemory *M, 
		       const ConcreteAddress &start, 
		       const ConcreteAddress &end)
{  
  if (start.get_address () >= end.get_address ())
    return;

  ConcreteAddress a = start;

  while (a.get_address () <= end.get_address ())
    {
      address_t p = a.get_address () % 16;

      out << right << hex << setw (8) << setfill (' ') 
	  << a.get_address () << ":\t";
      out << right << setw (3 * p) << setfill (' ') << "";
      while (p < 16 && a.get_address () <= end.get_address ())
	{
	  if (M->is_defined (a))
	    {
	      ConcreteValue val = M->get (a, 1, Architecture::LittleEndian);
	      out << hex << setw(2) << setfill ('0') << val.get () << " ";
	    }
	  else
	    {
	      out << "   ";
	    }
	  a++;
	  p++;
	}
      out << endl;
    }
}

void 
asm_writer (ostream &out, const Microcode *mc, 
	    const ConcreteMemory *memory, const SymbolTable *symboltable,
	    bool with_bytes, bool with_holes, bool with_labels)
{
  vector<MicrocodeNode *> *nodes = mc->get_nodes ();
  int nb_nodes = nodes->size ();
  SymbolTable *symbtable = s_build_symbol_table (mc, symboltable, with_labels);
  int i = 0;
  MicrocodeNode *lastnode = NULL;

  while (i < nb_nodes && ! nodes->at (i)->has_annotation (AsmAnnotation::ID))
    i++;
  MicrocodeAddress prev;
  if (i < nb_nodes)
    prev = nodes->at (i)->get_loc ();
  for (; i < nb_nodes; i++)
    {
      MicrocodeNode *node = nodes->at (i);

      if (! node->has_annotation (AsmAnnotation::ID))
	continue;
      lastnode = node;
      MicrocodeAddress ma (node->get_loc ());

      assert (ma.getLocal () == 0);

      if (with_holes)
	s_dump_memory_between (out, memory, prev.getGlobal (), 
			       ma.getGlobal () - 1);

      if (symbtable->has (ma.getGlobal ()))
	{
	  const std::list<std::string> &symbols = 
	    symbtable->get (ma.getGlobal ());
	  for (std::list<std::string>::const_iterator s = symbols.begin ();
	       s != symbols.end (); s++)
	    out << right << hex << setfill ('0') 
		<< setw (8) 
		<< ma.getGlobal () 
		<< setw (0)
		<< " <" << *s << ">: " << endl;
	}
      AsmAnnotation *a = (AsmAnnotation *) 
	node->get_annotation (AsmAnnotation::ID);
      Option<address_t> next = s_next_instruction_addr (node);
      if (next.hasValue ())
	prev = next.getValue ();
      out << right << hex << setw (8) << setfill (' ')
	  << node->get_loc ().getGlobal () << ":\t";
      if (with_bytes)
	{
	  string bytes;

	  if (next.hasValue ())
	    bytes = 
	      s_instruction_bytes (memory, ma.getGlobal (), next.getValue ());
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

	  if (symbtable->has (saddr))
	    {
	      const std::list<std::string> &symbols = symbtable->get (saddr);
		
	      for (std::list<std::string>::const_iterator s = symbols.begin (); 
		   s != symbols.end (); s++)
		{
		  if (first) { out << " # jump to : " ; first = false; }
		  else { out << ", "; }
		  out << *s;
		}
	    }
	}
      delete succ;
      out << endl;
    }

  if (lastnode != NULL)
    {
      Option<address_t> next = s_next_instruction_addr (lastnode);
      if (next.hasValue ())
	out << right << hex << setw (8) << setfill (' ')
	    << next.getValue () << ":" << endl;
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

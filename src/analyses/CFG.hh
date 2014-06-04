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
#ifndef ANALYSES_CFG_HH
# define ANALYSES_CFG_HH

# include <map>
# include <string>
# include <utils/graph.hh>
# include <kernel/Microcode.hh>

class CFG_BasicBlock
{
public:
  virtual ~CFG_BasicBlock () {}
  virtual bool operator == (const CFG_BasicBlock &e) const = 0;
  virtual std::string pp () const = 0;
  virtual MicrocodeNode *get_entry () const = 0;
  virtual MicrocodeNode *get_exit () const = 0;
};

class CFG_Edge
{
public:
  virtual ~CFG_Edge () {}
  virtual bool operator == (const CFG_Edge &e) const = 0;
  virtual std::string pp () const = 0;
  virtual CFG_BasicBlock *get_src () const = 0;
  virtual CFG_BasicBlock *get_tgt () const = 0;
};

struct CFG_NodeStore
{
  typedef std::vector<CFG_BasicBlock *> store_type;
  typedef store_type::iterator node_iterator;
  typedef store_type::const_iterator const_node_iterator;
};

class CFG : public GraphInterface<CFG_BasicBlock, CFG_Edge, CFG_NodeStore>
{
protected:
  CFG ();

public:
  virtual ~CFG();

  static CFG *createFromMicrocode (const Microcode *prog,
				   const MicrocodeAddress &start);

  typedef CFG_BasicBlock node_type;
  typedef CFG_Edge edge_type;

  virtual const_node_iterator begin_nodes () const;
  virtual const_node_iterator end_nodes () const;
  virtual node_iterator begin_nodes ();
  virtual node_iterator end_nodes ();

  virtual node_type *get_entry_point () const;
  virtual std::string get_label_node (node_type *n) const;
  virtual std::pair<edge_type *, node_type *>
  get_first_successor (node_type *n) const;
  virtual std::pair<edge_type *, node_type *>
  get_next_successor (node_type *n, edge_type *e) const;
  virtual node_type *get_source (edge_type *e) const;
  virtual node_type *get_target (edge_type *e) const;
  virtual void output_text(std::ostream & out) const;

  virtual node_type *new_node (MicrocodeNode *entry);
  virtual void add_edge (node_type *src, node_type *tgt);

private:
  store_type nodes;
  std::map<MicrocodeNode *, CFG_BasicBlock *> node2bb;
  node_type *entrypoint;
};

#endif /* ! ANALYSES_CFG_HH */

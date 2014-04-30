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

#ifndef KERNEL_MICROCODE_HH
#define KERNEL_MICROCODE_HH

#include <domains/concrete/ConcreteMemory.hh>
#include <kernel/microcode/MicrocodeNode.hh>
#include <kernel/microcode/MicrocodeStore.hh>
#include <utils/graph.hh>
#include <utils/map-helpers.hh>
#include <utils/path.hh>
#include <utils/tools.hh>

class MCPath;
class Expr;

/*****************************************************************************/
/*! \brief This class defines the concept of Microcode Program.
 *  This is a list of nodes, each node containing its successors.
 *****************************************************************************/
struct NodeStore 
{
  typedef std::vector<MicrocodeNode *> store_type;
  typedef store_type::iterator node_iterator;
  typedef store_type::const_iterator const_node_iterator;
};

class Microcode
  : public MicrocodeStore, 
    public GraphInterface<MicrocodeNode, StmtArrow, NodeStore> {

public:
  struct ArrowCreationCallback {
    virtual void add_node (Microcode *mc, StmtArrow *e) = 0;
  };

private:
  
  /*! \brief A microcode program is simply defined as a collection of
   * nodes. */
  store_type nodes;
  typedef std::unordered_map<MicrocodeAddress, MicrocodeNode *,
			     std::hash<MicrocodeAddress>,
			     EqualsFunctor<MicrocodeAddress> > node_map_type;
  node_map_type opt_nodes;

  /*! \brief the entry point of the program */
  MicrocodeAddress start;

  void apply_callbacks (StmtArrow *e);
  std::vector<ArrowCreationCallback *> arrow_callbacks;

/*****************************************************************************/
public:
  Microcode();
  Microcode(const Microcode &prg);
  virtual ~Microcode();

  MicrocodeAddress entry_point() const;
  void set_entry_point(MicrocodeAddress addr);

  /*! \brief try to retrieve the node at address addr, throw
    GetNodeNotFoundExc if there is no node at this address. */
  MicrocodeNode * get_node(MicrocodeAddress addr) const
    throw(GetNodeNotFoundExc);
  bool has_node_at (MicrocodeAddress addr) const;
  MicrocodeNode * get_or_create_node(MicrocodeAddress addr);
  void add_node(MicrocodeNode *n);

  const_node_iterator begin_nodes () const;
  const_node_iterator end_nodes () const;
  node_iterator begin_nodes ();
  node_iterator end_nodes ();
  std::size_t get_number_of_nodes () const;

  void add_arrow_creation_callback (ArrowCreationCallback *cb);
  void remove_arrow_creation_callback (ArrowCreationCallback *cb);

/*****************************************************************************/

  /* Here is the simplified API */
  StmtArrow *
  add_skip(MicrocodeAddress beg, MicrocodeAddress end, Expr *guard = 0);
  StmtArrow *
  add_assignment(MicrocodeAddress beg, LValue *lvalue, Expr *expr,
		 MicrocodeAddress end, Expr *guard = 0);

  StmtArrow *
  add_assignment(MicrocodeAddress &beg, LValue *lvalue, Expr *expr,
		 MicrocodeAddress *pend = NULL);
  StmtArrow *
  add_jump(MicrocodeAddress beg, Expr *target, Expr *guard = 0);

  void add_external(MicrocodeAddress beg, Expr *relation, MicrocodeAddress end);

  void merge (const Microcode *other, address_t shift, bool fold = false);

/*****************************************************************************/

  /* GraphInterface interface for navigation in the microcode.
   * (see graph.hh for doc.)  */
  MicrocodeNode * get_entry_point()  const;
  MicrocodeNode * get_source(StmtArrow *e) const;
  MicrocodeNode * get_target(StmtArrow *e) const;
  std::pair<StmtArrow *, MicrocodeNode *> get_first_successor(MicrocodeNode *n) const;
  std::pair<StmtArrow *, MicrocodeNode *> get_next_successor(MicrocodeNode *n, StmtArrow *e) const;
  int get_nb_successors(MicrocodeNode *n) const;
  virtual std::string get_label_node(MicrocodeNode *n) const;

  /***************************************************************************/

  /*! \brief Replace a set of MicrocodeNodes with another
   *  MicrocodeNode. StaticArrows are redirected, while dynamic
   *  ones are not modified, so be careful. The element nvo will not
   *  be modified, i.e no arrow will be added with it as source.
   *  Replaced MicrocodeNodes are deleted.
   *  \param to_replace set of nodes to replace
   *  \param nvo new MicrocodeNode
   *  \param delete_nodes true if replaced nodes must be deleted
   *
   *  \todo: a bit particular maybe to be move anywhere else */
  void replace_nodes(MicrocodeNodeSet & to_replace, MicrocodeNode *nvo, bool delete_nodes);

  /*! \brief Compute the set of direct paths (without repetition) going
   *  to a set of nodes to another set of node. */
  std::set<MCPath> compute_static_paths(MicrocodeNodeSet origin, MicrocodeNodeSet target);

  /***************************************************************************/
  // Simplification
  /***************************************************************************/

  /*! \brief Sort the nodes of the program regarding locations */
  void sort();

  /*! \brief Makes a pass on all the arrows.
   * - Transform dynamic targets into static ones when it is given by
   *   a constant expression. This is a good filter to lighten previous
   *   step of construction of Microcode.
   * - Adds missing node (i.e. the one pointed by static arrow) */
  void simplify_and_clean_targets();

  /*! Put the program into basic regular form:
   *  - regroup_nodes (cf. above)
   *  - simplify_and_clean_target (cf. above)
   *  - and sort. */
  void regular_form();

  /***************************************************************************/

  /*!\brief construct the list of all the expressions present in the
   * microcode, this includes expressions used in all the nodes and
   * arrows.
   * \return a vector containing pointers on pointers to
   * expressions. This allows to modify the expressions. (same as
   * MicrocodeNode.expr_list and MicrocodeNode.expr_list */
  std::vector<Expr **> * expr_list();

  /*! \todo microcode : parse stream */
  bool parse_stream(std::istream &in);

  /***************************************************************************/
  void output_text(std::ostream &out) const;

  void check () const;
};
/***************************************************************************/

/*! \brief Iterator syntaxic sugar */
#define Microcode_iterate_nodes(prg, node)				\
  for (Microcode::const_node_iterator node = (prg).begin_nodes (); \
       node != (prg).end_nodes ();				\
       node++)

/*! \brief Iterator syntaxic sugar */
#define Microcode_nodes_pass(node)			     \
  for (Microcode::const_node_iterator node = begin_nodes ();       \
       node != end_nodes ();				     \
       node++)

/*****************************************************************************/
/*! \brief A path in a MC Program. This is a list of Microcode
  Nodes. The choice of lists makes it easier to do operation on
  path (concatenation, insersion, etc. */
class MCPath : 
  public ConcreteEdgePath<MicrocodeNode, StmtArrow, NodeStore> {
public:
  MCPath(Microcode *prog) : ConcreteEdgePath<MicrocodeNode, StmtArrow, NodeStore>(prog) {};
  MCPath(const MCPath &o) : ConcreteEdgePath<MicrocodeNode, StmtArrow, NodeStore>(o) {};
};

#define MCPath_iterator std::list<StmtArrow*>::iterator
#define MCPath_reverse_iterator std::list<StmtArrow*>::reverse_iterator


#endif /* KERNEL_MICROCODE_HH */

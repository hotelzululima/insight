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
#ifndef UTILS_GRAPH_HH
#define UTILS_GRAPH_HH

#include <vector>
#include <set>
#include <list>
#include <utility>
#include <string>

template<typename Node, typename Edge, typename NodeStore>
class GraphPath;

class GetNodeNotFoundExc {};

/* ***************************************************/
/**
 * \brief  A visitor of a graph
 */
/* ***************************************************/
template<typename Node, typename Edge>
class GraphVisitor
{
public:
  std::set<Edge *> visited;      // The set of already visited arrows
  std::list< std::vector<Edge *> > * current_path;        // The current position (with the path going to it)


  /*! \brief Base constructor */
  GraphVisitor() {};

  /*! \brief Destructor */
  virtual ~GraphVisitor() {};

  /*! \brief the processing of the current arrow. Note that there is
   *  no real need of the node itself, which is referenced by the
   *  arrow. */
  virtual void process(Node *n, Edge *e) = 0;

  /*! \brief tells whether the visitor wants to continue exploration
   *  further or not. */
  virtual bool go_further(Node *n, Edge *e) = 0;

  /*! \brief inform the visitor that a back step has been performed
   *  because there is no more arrow. */
  virtual void back_step_impasse() = 0;

  /*! \brief inform the visitor that a back step has been performed
   *  because it found a loop */
  virtual void back_step_loop(Edge *e) = 0;

  /*! \brief ask the visitor whether he want to continue the run or
   *  not */
  virtual bool continue_run() = 0;

  /*! \brief tells the visitor the traversal is over */
  virtual void traversal_over() = 0;
};

/* ***************************************************/
/**
 * \brief  A graph object. This is an abstract class.
 * Lots of functions implementations are let to the class
 * concrete child, like successors and predcessors access.
 * It is because it would consume too much time to refactor
 * the Microcode class.
 * \todo This interface should be reworked in the future
 * and should contain a full graph default implementation.
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class GraphInterface
{
public:
  typedef typename NodeStore::store_type store_type;
  typedef typename NodeStore::node_iterator node_iterator;
  typedef typename NodeStore::const_node_iterator const_node_iterator;

  /* ***************************************************/
  /**
   * \brief  return graph nodes
   */
  /* ***************************************************/
  virtual const_node_iterator begin_nodes () const = 0;
  virtual const_node_iterator end_nodes () const = 0;
  virtual node_iterator begin_nodes () = 0;
  virtual node_iterator end_nodes () = 0;

  /* ***************************************************/
  /**
   * \brief  return graph entry point
   * \returns the graph entry point
   */
  /* ***************************************************/
  virtual Node *get_entry_point() const = 0;

  /* ***************************************************/
  /**
   * \brief add graph node
   * \param n node to add
   */
  /* ***************************************************/
  //  virtual void add_node(Node *n) = 0;


  /* ***************************************************/
  /**
   * \brief  returns a (short) label for a given node
   * \param  n the node
   * \returns the label
   */
  /* ***************************************************/
  virtual std::string get_label_node(Node *n) const = 0;

  /* ***************************************************/
  /**
   * \brief  returns a (short) label for a given edge.
   * Default: get_label(source)->get_label(target)
   * \param  n the edge
   * \returns the label
   */
  /* ***************************************************/
  virtual std::string get_label_edge(Edge *n) const;

  /* ***************************************************/
  /**
   * \brief  return the first successor of a node
   * \param  n the node
   * \returns  first successor (edge) or NULL if none
   */
  /* ***************************************************/
  virtual std::pair<Edge *, Node *> get_first_successor(Node *n) const = 0;

  /* ***************************************************/
  /**
   * \brief  return another successor of a node n
   * \param  n the node
   * \param  e last enumerated edge
   * \returns another successor (edge) or NULL if no more
   * edge
   */
  /* ***************************************************/
  virtual std::pair<Edge *, Node *> get_next_successor(Node *n, Edge *e) const = 0;

  /* ***************************************************/
  /**
   * \brief  get source of the arrow (or NULL if none)
   * \param  e the arrow
   * \returns  source node
   */
  /* ***************************************************/
  virtual Node *get_source(Edge *e) const = 0;


  /* ***************************************************/
  /**
   * \brief  get target of the arrow (or NULL if none)
   * \param  e the arrow
   * \returns  target node
   */
  /* ***************************************************/
  virtual Node *get_target(Edge *e) const = 0;









  /* ***************************************************/
  /**
   * \brief  return true if n is in graph
   * \param  n the node
   * \note operator== must be defined for Node
   */
  /* ***************************************************/
  virtual bool contains(Node *n) const;


  /* ***************************************************/
  /**
   * \brief  return the first predecessor of a node
   * \param  n the node
   * \returns  first predecessor (edge) or NULL if none
   */
  /* ***************************************************/
  virtual std::pair<Edge *, Node *> get_first_predecessor(Node *n) const;

  /* ***************************************************/
  /**
   * \brief  return another predecessor of a node n
   * \param  n the node
   * \param  e last enumerated edge
   * \returns another predecessor (edge) or NULL if no more
   * edge
   */
  /* ***************************************************/
  virtual std::pair<Edge *, Node *> get_next_predecessor(Node *n, Edge *e) const ;


  /* ***************************************************/
  /**
   * \brief  return the number of successors of a node
   * \param  n the node
   * \returns number of successors of n
   */
  /* ***************************************************/
  virtual int get_nb_successors(Node *n) const;

  /* ***************************************************/
  /**
   * \brief  return the number of predecessors of a node
   * \param  n the node
   * \returns number of predecessors of n
   */
  /* ***************************************************/
  virtual int get_nb_predecessors(Node *n) const;

  /* ***************************************************/
  /**
   * \brief Performs a depth-first run on the microcode graph
   * starting from node start.
   * The run collects all the accessible arrows, in a depth
   * first algorithm, which run path without node repetition.
   * \note An edge may be visited more than once
   * \todo was it wanted ? ask Olivier
   * \param  start first node to start run from
   * \param  visitor callback class
   */
  /* ***************************************************/
  virtual void depth_first_run(Node *start, 
			       GraphVisitor<Node, Edge>& visitor) const;


  /* ***************************************************/
  /**
   * \brief Performs a  run on the microcode graph
   * that respects the depth-first order of the graph if possible.
   * \note An edge will be visited only once
   * \param  start first node to start run from
   * \param  visitor callback class
   */
  /* ***************************************************/
  virtual void depth_first_traversal(Node *start, GraphVisitor<Node, Edge>& visitor) const;


  /* ***************************************************/
  /**
   * \brief Performs a  run on the microcode graph
   * that respects the topological order of the graph if possible.
   * The topological order is only guaranteed if the graph is a DAG.
   * \note An edge will be visited only once
   * \param  start first node to start run from
   * \param  visitor callback class
   */
  /* ***************************************************/
  virtual void topological_traversal(Node *start, GraphVisitor<Node, Edge>& visitor) const;

  /* ***************************************************/
  /**
   * \brief Performs a bread-first run on the microcode graph
   * starting from node start.
   * The run collects all the accessible arrows, in a bread
   * first algorithm, which run path without node repetition.
   * \todo: not implemented
   * \note An edge will be visited only once
   * \param  start first node to start run from
   * \param  visitor callback class
   */
  /* ***************************************************/
  virtual void bread_first_traversal(Node *start, 
				     GraphVisitor<Node, Edge>& visitor) const;


  /* ***************************************************/
  /**
   * \brief  Perform a test DFR, printing out all visited
   * edges
   */
  /* ***************************************************/
  virtual void depth_first_test();

  /* ***************************************************/
  /**
   * \brief computes the regular path over-approximating
   * the paths of the graph, without considering the graph
   * semantic.
   * \returns a regular path
   */
  /* ***************************************************/
  virtual GraphPath<Node, Edge, NodeStore>* get_regular_node_paths();

  /* ***************************************************/
  /**
   * \brief  Get all nodes located on a path starting from
   * \code start  and ending in \code end.
   * The caller must delete himself the resulting list
   * \param  start starting node of path
   * \param  end ending node of path
   * \returns  nodes n s.t start <= n <= end
   */
  /* ***************************************************/
  virtual std::list<Node *>* get_nodes_between(Node *start, std::list<Node *> &end);
  virtual std::list<Node *>* get_nodes_between(Node *start, Node *end);


  /* ***************************************************/
  /**
   * \brief  pretty printing
   */
  /* ***************************************************/
  virtual std::string pp() const;
  virtual void output_text(std::ostream & out) const = 0;
  /* ***************************************************/
  /**
   * \brief  Export the current graph to dot format
   * \param  filename the file the dot code will be
   * written in
   */
  /* ***************************************************/
  virtual void toDot(std::string filename) const;
  virtual void toDot(std::ostream &out) const;
};

#include "graph.ii"

#endif /* UTILS_GRAPH_HH */

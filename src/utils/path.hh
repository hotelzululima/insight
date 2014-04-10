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
#ifndef UTILS_PATH_HH
#define UTILS_PATH_HH

#include <kernel/Expressions.hh>

#include <utils/graph.hh>

template<typename Node, typename Edge, typename NodeStore>
class EmptyPath;
template<typename Node, typename Edge, typename NodeStore>
class ConcreteEdgePath;
template<typename Node, typename Edge, typename NodeStore>
class ConcreteNodePath;
template<typename Node, typename Edge, typename NodeStore>
class UnionPath;
template<typename Node, typename Edge, typename NodeStore>
class ConcatenationPath;
template<typename Node, typename Edge, typename NodeStore>
class StarPath;
template<typename Node, typename Edge, typename NodeStore>
class VariablePath;

/* ***************************************************/
/**
 * \brief  Abstract class for graph paths
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class GraphPath
{

private:
  const GraphInterface<Node, Edge, NodeStore>* graph;

public:
  /*! \brief Constructor */
  GraphPath(const GraphInterface<Node, Edge, NodeStore>* graph): graph(graph) {};
  /*! \brief Copy constructor */
  GraphPath(const GraphPath<Node, Edge, NodeStore>& o): graph(o.graph) {};
  /*! Destructor */
  virtual ~GraphPath() {};

  /*! \brief Clone */
  virtual GraphPath<Node, Edge, NodeStore>* clone() const = 0;

  /*! \brief accessor */
  const GraphInterface<Node, Edge, NodeStore>* get_graph()
  {
    return graph;
  };


  /* ***************************************************/
  /**
   * \brief  Replace variable in place
   * (by using bottom_up_apply_in_place function).
   * \param  v_id the variable id
   * \param  value the value to replace with
   * \returns the new address of the term after replacement.
   * Note that this address may be the same as the current instance.
   */
  /* ***************************************************/
  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value) = 0;

  /* ***************************************************/
  /**
   * \brief  simplify a path
   * \returns  the new path after simplification
   * Note that this address may be the same as the current instance.
   */
  /* ***************************************************/
  virtual GraphPath<Node, Edge, NodeStore>* simplify() = 0;

  /* ***************************************************/
  /**
   * \brief  put a path in disjonctive form
   * \returns  the new path after simplification
   * Note that this address may be the same as the current instance.
   */
  /* ***************************************************/
  virtual GraphPath<Node, Edge, NodeStore>* distribute() = 0;

  /* ***************************************************/
  /**
   * \brief  put a path in normal form, a polynom of variables
   * \returns  the new path after normalization
   * Note that:
   * - this address may be the same as the current instance.
   * - path must be in disjonctive form.
   * - variables must be either at leftmost or rightmost parts of ConcatenationPath
   * - path must be of first degree
   *
   */
  /* ***************************************************/
  virtual GraphPath<Node, Edge, NodeStore>* normalize() = 0;

  /* ***************************************************/
  /**
   * \brief  factorize a path
   * \returns  the new path after factorization
   * Note that this address may be the same as the current instance.
   */
  /* ***************************************************/
  virtual GraphPath<Node, Edge, NodeStore>* factorize() = 0;


  /* ***************************************************/
  /**
   * \brief  tells if it is an empty path
   * \returns  true if empty
   */
  /* ***************************************************/
  virtual bool is_empty()
  {
    return dynamic_cast<EmptyPath<Node, Edge, NodeStore>*>(this) != NULL;
  };

  /* ***************************************************/
  /**
   * \brief  tells if it is a concrete  edge path
   * \returns  true if concrete
   */
  /* ***************************************************/
  virtual bool is_concrete_edge()
  {
    return dynamic_cast<ConcreteEdgePath<Node, Edge, NodeStore>*>(this) != NULL;
  };

  /* ***************************************************/
  /**
   * \brief  tells if it is a concrete  node path
   * \returns  true if concrete
   */
  /* ***************************************************/
  virtual bool is_concrete_node()
  {
    return dynamic_cast<ConcreteNodePath<Node, Edge, NodeStore>*>(this) != NULL;
  };

  /* ***************************************************/
  /**
   * \brief  tells if it is a union of paths
   * \returns  true if union
   */
  /* ***************************************************/
  virtual bool is_union()
  {
    return dynamic_cast<UnionPath<Node, Edge, NodeStore>*>(this) != NULL;
  };

  /* ***************************************************/
  /**
   * \brief  tells if it is a concatenation of path
   * \returns  true if concatenation
  */
  /* ***************************************************/
  virtual bool is_concatenation()
  {
    return dynamic_cast<ConcatenationPath<Node, Edge, NodeStore>*>(this) != NULL;
  };

  /* ***************************************************/
  /**
   * \brief  tells if it is a repetition of a path
   * \returns  true if repetition
   */
  /* ***************************************************/
  virtual bool is_star()
  {
    return dynamic_cast<StarPath<Node, Edge, NodeStore>*>(this) != NULL;
  };

  /* ***************************************************/
  /**
   * \brief  tells if it is a symbolic path
   * \returns  true if symbolic
   */
  /* ***************************************************/
  virtual bool is_variable()
  {
    return dynamic_cast<VariablePath<Node, Edge, NodeStore>*>(this) != NULL;
  };

  /* ***************************************************/
  /**
   * \brief  tells if path contains a variable
   * \returns  true if contains a variable
   */
  /* ***************************************************/
  virtual bool contains_variable(std::string v_id = "") = 0;

  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars) = 0;

  /*! \brief Pretty Printing */
  virtual std::string pp() const = 0;

  /*! \brief Syntaxic equality */
  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const = 0;
};


/* ***************************************************/
/**
 * \brief a concrete edge path of a graph: a sequence of edges
 * The choice of lists makes it easier to do operation on
 path (concatenation, insersion, etc.
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class ConcreteEdgePath : public std::list<Edge *>, 
			 public GraphPath<Node, Edge, NodeStore>
{

public:
  /*! \brief Constructor */
  ConcreteEdgePath(const GraphInterface<Node, Edge, NodeStore>* graph) : std::list<Edge *>(), GraphPath<Node, Edge, NodeStore>(graph) {};
  /*! \brief Copy constructor */
  ConcreteEdgePath(const ConcreteEdgePath<Node, Edge, NodeStore>& o) : std::list<Edge *>(o), GraphPath<Node, Edge, NodeStore>(o) {};
  /*! Destructor : do not delete the Edges !*/
  virtual ~ConcreteEdgePath() { };

  /*! \brief Clone */
  virtual ConcreteEdgePath<Node, Edge, NodeStore>* clone() const
  {
    return new ConcreteEdgePath<Node, Edge, NodeStore>(*this);
  };

  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value);

  virtual GraphPath<Node, Edge, NodeStore>* simplify();
  virtual GraphPath<Node, Edge, NodeStore>* distribute();
  virtual GraphPath<Node, Edge, NodeStore>* factorize();
  virtual GraphPath<Node, Edge, NodeStore>* normalize();
  virtual bool contains_variable(std::string v_id = "");
  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars);

  /*! \brief Pretty Printing */
  std::string pp() const;
  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const;
};

/* ***************************************************/
/**
 * \brief a concrete node path of a graph: a sequence of edges
 * The choice of lists makes it easier to do operation on
 path (concatenation, insersion, etc.
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class ConcreteNodePath : public std::list<Node *>, public GraphPath<Node, Edge, NodeStore>
{

public:
  /*! \brief Constructor */
  ConcreteNodePath(const GraphInterface<Node, Edge, NodeStore>* graph): std::list<Node *>(), GraphPath<Node, Edge, NodeStore>(graph) {};
  /*! \brief Copy constructor */
  ConcreteNodePath(const ConcreteEdgePath<Node, Edge, NodeStore>& o): std::list<Node *>(o), GraphPath<Node, Edge, NodeStore>(o) {};
  /*! Destructor : do not delete the Edges !*/
  virtual ~ConcreteNodePath() { };

  /*! \brief Clone */
  virtual ConcreteNodePath<Node, Edge, NodeStore>* clone() const
  {
    return new ConcreteNodePath<Node, Edge, NodeStore>(*this);
  };

  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value);

  virtual GraphPath<Node, Edge, NodeStore>* simplify();
  virtual GraphPath<Node, Edge, NodeStore>* distribute();
  virtual GraphPath<Node, Edge, NodeStore>* factorize();
  virtual GraphPath<Node, Edge, NodeStore>* normalize();
  virtual bool contains_variable(std::string v_id = "");
  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars);

  /*! \brief Pretty Printing */
  std::string pp() const;
  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const;
};


/* ***************************************************/
/**
 * \brief empty path
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class EmptyPath :  public GraphPath<Node, Edge, NodeStore>
{

public:
  /*! \brief Constructor */
  EmptyPath(const GraphInterface<Node, Edge, NodeStore>* graph): GraphPath<Node, Edge, NodeStore>(graph) {};
  /*! \brief Copy constructor */
  EmptyPath(const EmptyPath<Node, Edge, NodeStore>& o): GraphPath<Node, Edge, NodeStore>(o) {};
  /*! Destructor */
  virtual ~EmptyPath() { };

  /*! \brief Clone */
  virtual EmptyPath<Node, Edge, NodeStore>* clone() const
  {
    return new EmptyPath<Node, Edge, NodeStore>(*this);
  };

  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value);

  virtual GraphPath<Node, Edge, NodeStore>* simplify();
  virtual GraphPath<Node, Edge, NodeStore>* distribute();
  virtual GraphPath<Node, Edge, NodeStore>* factorize();
  virtual GraphPath<Node, Edge, NodeStore>* normalize();
  virtual bool contains_variable(std::string v_id = "");
  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars);

  /*! \brief Pretty Printing */
  std::string pp() const;
  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const;
};


/* ***************************************************/
/**
 * \brief  concatenation of several paths
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class ConcatenationPath : public std::list<GraphPath<Node, Edge, NodeStore>*>, public GraphPath<Node, Edge, NodeStore>
{
public:
  /*! \brief basic constructor */
  ConcatenationPath(const GraphInterface<Node, Edge, NodeStore>* p): GraphPath<Node, Edge, NodeStore>(p) {};
  /*! \brief Constructor */
  ConcatenationPath(GraphPath<Node, Edge, NodeStore>* u1, GraphPath<Node, Edge, NodeStore>* u2) : std::list<GraphPath<Node, Edge, NodeStore>*>(), GraphPath<Node, Edge, NodeStore>(u1->get_graph())
  {
    this->push_back(u1);
    this->push_back(u2);
  };
  /*! \brief Copy constructor */
  ConcatenationPath(const ConcatenationPath<Node, Edge, NodeStore>& o) : std::list<GraphPath<Node, Edge, NodeStore>*>(), GraphPath<Node, Edge, NodeStore>(o)
  {
    for (typename std::list<GraphPath<Node, Edge, NodeStore>*>::const_iterator it = o.begin(); it != o.end(); ++it)
      this->push_back((*it)->clone());
  };
  /*! Destructor */
  virtual ~ConcatenationPath()
  {
    for (typename std::list<GraphPath<Node, Edge, NodeStore>*>::iterator it = this->begin(); it != this->end(); ++it) delete(*it);
  };

  /*! \brief Clone */
  virtual ConcatenationPath<Node, Edge, NodeStore>* clone() const
  {
    return new ConcatenationPath<Node, Edge, NodeStore>(*this);
  };

  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value);

  virtual GraphPath<Node, Edge, NodeStore>* simplify();
  virtual GraphPath<Node, Edge, NodeStore>* distribute();
  virtual GraphPath<Node, Edge, NodeStore>* factorize();
  virtual GraphPath<Node, Edge, NodeStore>* normalize();
  virtual bool contains_variable(std::string v_id = "");
  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars);

  /*! \brief Pretty Printing */
  std::string pp() const;
  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const;

};

/* ***************************************************/
/**
 * \brief  Union of several paths
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class UnionPath : public std::list<GraphPath<Node, Edge, NodeStore>*>, public GraphPath<Node, Edge, NodeStore>
{
public:
  /*! \brief basic constructor */
  UnionPath(const GraphInterface<Node, Edge, NodeStore>* p): GraphPath<Node, Edge, NodeStore>(p) {};
  /*! \brief Constructor */
  UnionPath(GraphPath<Node, Edge, NodeStore>* u1, GraphPath<Node, Edge, NodeStore>* u2) : std::list<GraphPath<Node, Edge, NodeStore>*>(), GraphPath<Node, Edge, NodeStore>(u1->get_graph())
  {
    this->push_back(u1);
    this->push_back(u2);
  };
  /*! \brief Copy constructor */
  UnionPath(const UnionPath<Node, Edge, NodeStore>& o) : std::list<GraphPath<Node, Edge, NodeStore>*>(), GraphPath<Node, Edge, NodeStore>(o)
  {
    for (typename std::list<GraphPath<Node, Edge, NodeStore>*>::const_iterator it = o.begin(); it != o.end(); ++it)
      this->push_back((*it)->clone());
  };
  /*! Destructor */
  virtual ~UnionPath()
  {
    for (typename std::list<GraphPath<Node, Edge, NodeStore>*>::iterator it = this->begin(); it != this->end(); ++it) delete(*it);
  };

  /*! \brief Clone */
  virtual UnionPath<Node, Edge, NodeStore>* clone() const
  {
    return new UnionPath<Node, Edge, NodeStore>(*this);
  };

  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value);

  virtual GraphPath<Node, Edge, NodeStore>* simplify();
  virtual GraphPath<Node, Edge, NodeStore>* distribute();
  virtual GraphPath<Node, Edge, NodeStore>* factorize();
  virtual GraphPath<Node, Edge, NodeStore>* normalize();
  virtual bool contains_variable(std::string v_id = "");
  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars);

  /*! \brief Pretty Printing */
  std::string pp() const;
  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const;
};

/* ***************************************************/
/**
 * \brief Repetition of a path
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class StarPath : public GraphPath<Node, Edge, NodeStore>
{
public:
  GraphPath<Node, Edge, NodeStore>* path;

public:
  /*! \brief Constructor */
  StarPath(GraphPath<Node, Edge, NodeStore>* p): GraphPath<Node, Edge, NodeStore>(p->get_graph()), path(p) {};
  /*! \brief Copy constructor */
  StarPath(const StarPath<Node, Edge, NodeStore>& o): GraphPath<Node, Edge, NodeStore>(o), path(o.path->clone()) {};
  /*! Destructor */
  virtual ~StarPath()
  {
    delete path;
  };

  /*! \brief Clone */
  virtual StarPath<Node, Edge, NodeStore>* clone() const
  {
    return new StarPath<Node, Edge, NodeStore>(*this);
  };

  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value);

  virtual GraphPath<Node, Edge, NodeStore>* simplify();
  virtual GraphPath<Node, Edge, NodeStore>* distribute();
  virtual GraphPath<Node, Edge, NodeStore>* factorize();
  virtual GraphPath<Node, Edge, NodeStore>* normalize();
  virtual bool contains_variable(std::string v_id = "");
  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars);

  /*! \brief Pretty Printing */
  std::string pp() const;

  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const;
};

/* ***************************************************/
/**
 * \brief  a symbolic path
 */
/* ***************************************************/
template<typename Node, typename Edge, typename NodeStore>
class VariablePath : public GraphPath<Node, Edge, NodeStore>
{
private:
  const std::string id;

public:
  /*! \brief Constructor */
  VariablePath(const GraphInterface<Node, Edge, NodeStore>* p, const std::string id): GraphPath<Node, Edge, NodeStore>(p), id(id) {};
  /*! \brief Copy constructor */
  VariablePath(const VariablePath<Node, Edge, NodeStore>& o): GraphPath<Node, Edge, NodeStore>(o), id(o.id) {};

  /*! \brief Clone */
  virtual VariablePath<Node, Edge, NodeStore>* clone() const
  {
    return new VariablePath<Node, Edge, NodeStore>(*this);
  };

  virtual GraphPath<Node, Edge, NodeStore>* replace_variable_in_place(std::string v_id, GraphPath<Node, Edge, NodeStore>* value);

  const std::string get_id() const
  {
    return id;
  };

  virtual GraphPath<Node, Edge, NodeStore>* simplify();
  virtual GraphPath<Node, Edge, NodeStore>* distribute();
  virtual GraphPath<Node, Edge, NodeStore>* factorize();
  virtual GraphPath<Node, Edge, NodeStore>* normalize();
  virtual bool contains_variable(std::string v_id = "");
  virtual void gather_variables(std::list<VariablePath<Node, Edge, NodeStore>*>* vars);

  std::string pp() const;
  virtual bool operator==(const GraphPath<Node, Edge, NodeStore> & e) const;
};

#include "path.ii"

#endif /* UTILS_PATH_HH */

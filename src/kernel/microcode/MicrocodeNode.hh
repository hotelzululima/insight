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
#ifndef KERNEL_MICROCODE_MICROCODE_NODE_HH
#define KERNEL_MICROCODE_MICROCODE_NODE_HH

#include <vector>
#include <set>

#include <domains/concrete/ConcreteAddress.hh>
#include <kernel/Architecture.hh>
#include <kernel/Annotable.hh>
#include <kernel/Expressions.hh>
#include <kernel/microcode/MicrocodeAddress.hh>
#include <kernel/microcode/MicrocodeStatements.hh>

/***********************************************************************/
/* Summary                                                             */
/***********************************************************************/
class MicrocodeNode;
class StmtArrow;
class StaticArrow;
class DynamicArrow;

/* reference */
class Microcode;

/***********************************************************************/
/*! \brief A node is a minimal code entity where to put a statement.
 *  Nodes are connected by arrows (StmtArrow).
 *
 * \remark Nodes which carry a skip statement are here to encode jumps
 * and conditional jumps, keeping consistency with code address.
 ***********************************************************************/
class MicrocodeNode: public Annotable {

private:
  /* Note that an assembly instruction may give raise to several
   * microcode node. That is why the loc object contains
   * the real object code address, but also a secondary address to
   * distinguish microcode instructions sharing the same object code
   * address. */
  MicrocodeAddress loc;
  std::vector<StmtArrow *> * successors;
  /* computed during the optimization step */
  std::vector<StmtArrow *> * predecessors;

  // TODO *** TODO *** TODO *** TODO ***
  // OPTIMIZATION : set-up the father at initialization !

public:
  MicrocodeNode(MicrocodeAddress loc);
  MicrocodeNode(MicrocodeAddress loc, std::vector<StmtArrow *> * successors);
  MicrocodeNode(MicrocodeAddress loc, StmtArrow * unique_succ);
  MicrocodeNode(MicrocodeAddress loc, StmtArrow * succ1, StmtArrow * succ2);
  MicrocodeNode(const MicrocodeNode &);
  ~MicrocodeNode();
  MicrocodeNode * clone() const;

  void add_predecessor(StmtArrow * arr);

  const MicrocodeAddress &get_loc() const;
  std::vector<StmtArrow *> * get_successors() const;
  std::vector<StmtArrow *> * get_predecessors() const;
  std::vector<MicrocodeNode *> get_global_parents () const;

  /* equality of location only (not successors) */
  bool operator==(const MicrocodeNode &) const;
  bool operator<(const MicrocodeNode &e) const;

  StmtArrow *
  add_successor(Expr *condition, Expr *target, Statement *stmt);
  StmtArrow *
  add_successor(Expr *condition, MicrocodeNode *tgt, Statement *stmt);

  /*!\brief construct the list of all the expressions present in the
   * statement, this includes expressions used in arrows.
   * \return a vector containing pointers on pointers to expression.
   * This allows to modify the expressions. (same as
   * MicrocodeNode.expr_list) */
  std::vector<Expr **> * expr_list();
  std::string pp() const ;

  struct lt_node {
    bool operator()(MicrocodeNode *n1, MicrocodeNode *n2) const {
      return n1->get_loc().lessThan(n2->get_loc());
    }
  };
};

/***********************************************************************/

/*! \brief Iterator syntactic sugar */
#define MicrocodeNode_iterate_successors(node, succ)                              \
  for (std::vector<StmtArrow*>::iterator succ = (node).get_successors()->begin(); \
       succ != (node).get_successors()->end();                                    \
       succ++)

/***********************************************************************/
/*! \brief Arrows defines the successors of microcode nodes.
 * The class is abstract, it is specialized into two types:
 * - static arrows for which concrete targets are known
 * - dynamic arrows for which targets are defined by expressions.
 ***********************************************************************/
class StmtArrow: public Annotable {

protected:

  /*! points on the origin of the arrow if it is different to NULL (for optimization) */

  /* Pointer to the node which has us as a successor */
  MicrocodeNode *src;

  /*! \brief Each arrow carries a statement (which can actually be Skip). */
  Statement * stmt;

  /*! \brief The guard of the arrow, defined by an expression
   *  interpreted as a boolean (0 for false, true for any other value). */
  Expr * condition;

public:
  StmtArrow(MicrocodeNode * origin,
            Statement *stmt,
            const AnnotationMap * annotations = 0,
            Expr * condition = 0);

  StmtArrow(const StmtArrow & arr);
  virtual ~StmtArrow();
  virtual StmtArrow *clone() = 0;

  void set_src(MicrocodeNode * n);

  MicrocodeAddress get_origin() const;
  MicrocodeNode *get_src() const;
  Statement * get_stmt() const;
  Expr * get_condition() const;

  /*! \brief (full) equality of origins and targets, of conditions and of statements. */
  bool operator==(const StmtArrow &other);
  bool is_dynamic() const;
  bool is_static() const;

  /*! \brief Try to retrieve the target. If the function
   * return None, this implies that the arrow is a dynamic arrow, and
   * there is no trival computation. */
  virtual Option<MicrocodeAddress> extract_target() const = 0;

  /*! \brief the function expr_list must access the address of the
   *  condition attribute. */
  friend std::vector<Expr **> * MicrocodeNode::expr_list();
  virtual std::string pp() const = 0;

  struct lt_arrow {
    bool operator()(StmtArrow *n1, StmtArrow *n2) const {
      return ((long) n1) < ((long) n2) ;
    }
  };
};

/***********************************************************************/
/*! \brief Static arrows specialize arrows with a concrete target,
 *  i.e. the target is defined as microcode address.
 ***********************************************************************/
class StaticArrow : public StmtArrow {
private:
  /*! \brief The target of the arrow. Here it is defined as a concrete
   *  microcode address. Note that a microcode address cannot be encoded
   *  into an expression, because of its two components. */
  MicrocodeAddress target; // \todo deprecated

  MicrocodeNode *tgt;

public:
  StaticArrow(MicrocodeNode *src,
              MicrocodeNode *tgt,
              Statement *stmt,
              const AnnotationMap *annotations = 0,
              Expr *condition = 0);

  StaticArrow(const StaticArrow &other);
  StmtArrow * clone();
  virtual ~StaticArrow();

  void set_tgt(MicrocodeNode *);

  MicrocodeAddress get_concrete_target() const;
  void set_concrete_target(MicrocodeAddress);

  /*! \brief Always returns the target */
  Option<MicrocodeAddress> extract_target() const;
  MicrocodeAddress get_target() const;

  /*! \brief the function expr_list must access the address of the
   *  target attribute. */
  friend std::vector<Expr **>* MicrocodeNode::expr_list();
  std::string pp() const;
};

/***********************************************************************/
/*! \brief Dynamic arrows specialize arrow with a dynamic target,
 *  i.e. the target is defined as an expression which computes the target.
 ***********************************************************************/
class DynamicArrow : public StmtArrow
{
private:
  /*! \brief The target is dynamic: it is defined by an expression */
  Expr * target;

public:
  DynamicArrow(MicrocodeNode *origin,
               Expr *target,
               Statement *stmt,
               const AnnotationMap *annotations = 0,
               Expr *condition = 0);

  DynamicArrow(const DynamicArrow &other);

  StmtArrow *clone();
  virtual ~DynamicArrow();
  Expr * get_target() const;

  /* \brief may return nothing if there is no trivial simplification. */
  Option<MicrocodeAddress> extract_target() const;

  /*! \brief the function expr_list must access the address of the
    target attribute. */
  friend std::vector<Expr **>* MicrocodeNode::expr_list();
  std::string pp() const;

  void add_solved_jump (MicrocodeAddress tgt);
};

/* MicrocodeAddress Hash function */
namespace std {
#ifdef USE_TR1_NAMESPACE
  namespace tr1 {
#endif
    template<>
    struct hash<MicrocodeAddress> {
      size_t operator()(const MicrocodeAddress &a) const {
	return a.getGlobal();
      }
    };
#ifdef USE_TR1_NAMESPACE
  }
#endif
}

/*****************************************************************************/
/* Nodes and arrows sets                                                     */
/*****************************************************************************/
typedef std::set<MicrocodeNode *, MicrocodeNode::lt_node> MicrocodeNodeSet;
typedef std::set<StmtArrow *, StmtArrow::lt_arrow> MicrocodeArrowSet;

#endif /* KERNEL_MICROCODE_MICROCODE_NODE_HH */


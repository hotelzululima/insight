/*-
 * Copyright (C) 2010-2012, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
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

#ifndef MICROCODE_EXEC_HH
#define MICROCODE_EXEC_HH

#include <map>
#include <list>
#include <string>
#include <utils/map-helpers.hh>
#include <utils/option.hh>
#include <kernel/Memory.hh>
#include <kernel/microcode/MicrocodeStore.hh>
#include <interpreters/ExprSemantics.hh>
#include <interpreters/concrete/ConcreteAddress.hh>

#define TEMPLATE \
  template <typename Address,       \
  typename Value,         \
  typename Semantics,     \
  typename Memory,        \
  typename ProgramPoint>  \
   
#define TEMPLATE_ARGS Address,Value,Semantics,Memory,ProgramPoint

/*****************************************************************************/

//template <class ProgramPoint> class AbstractProgramPoint;

/*****************************************************************************/
/*! \brief The abstract context class is the data structure to be
 *  stored at each program point. It carries all information needed to
 *  interpret statement.
 *****************************************************************************/
TEMPLATE
class AbstractContext    /* Abstract */
{

public: /*! \todo private */
  typedef Memory ContextMemory;

  Memory *memory;

  /***************************************************************************/
  /* Expression Evaluation                                                   */
  /***************************************************************************/

  /*! \remark The semantics of expressions is defined by the
   *  implementation of the ExprSemantics class. See
   *  concrete/ConcreteExprSemantics.* for example. */

private:

  /*! \brief Evaluation of a unary expression. */
  Value eval_unary_expr(UnaryApp *ua);

  /*! \brief Evaluation of a binary expression. */
  Value eval_binary_expr(BinaryApp *ba);

  /*! \brief Evaluation of a ternary expression. */
  Value eval_ternary_expr(TernaryApp *ta);

public:
  virtual ~AbstractContext() { }

  /*! \brief The general expression evaluation function */
  virtual Value eval(const Expr *e);


  /***************************************************************************/
  /* Statement interpretation                                                */
  /***************************************************************************/

  /*! \brief Interpretation of a statement from the current context.
   *  \param st The statement to be interpreted
   *  \return The new context after the effect of the statement. */
  AbstractContext *exec(Statement *st);

  /*! \brief Merge an other context to the current one (defined by the
   *  current object instance). Caution, this operation is not
   *  commutative : for instance the context "other" may replace the
   *  current context in the case of the simulator.
   *
   *  \return a bool value indicating whether the context must be
   *  interpreted after the merge operation. In particular, if there
   *  is no change, then it should return false and then the
   *  interpreter stop his walk here. But note that in any case the merge
   *  operation is done.
   */
  virtual bool merge(AbstractContext *other) = 0;

  /*! \brief Split a context according to a given condition. Returns a
   *  pair of contexts (ctxt1, ctxt2). ctxt1 (resp. ctxt2) is an upper
   *  set enclosing the values making the condition true
   *  (resp. false). If the condition is always true (resp. false)
   *  then one returns None for the false context (resp. true).
   *  User is responsible for result destruction. */
  virtual
  std::pair< Option<AbstractContext *>, Option<AbstractContext *> >
  split_context(Expr *condition);

  /***************************************************************************/
  /* Utils                                                                   */
  /***************************************************************************/

  /*! \brief Produce the empty context. */
  static AbstractContext *empty_context();

  /*! \brief Construct a clone of the current object. Note that this
   *  class being abstract, it cannot be instanciated and do not
   *  have constructor. */
  virtual AbstractContext *clone() = 0;

  /*! \brief Pretty printing */
  virtual std::string pp();

};

/*****************************************************************************/
/*! \brief The concept of program point generalizes the program counter
 *  value. The central data structure of an analysis is a map
 *  associating contexts to program points. A program point may be a
 *  program counter value (MicrocodeAddress), but may be more general
 *  than that, for instance a trace. The set of program point maps on
 *  to the cfg, via the method to_address() below.
 *
 * \remark Here we use concrete addresses. One supposes that abstract
 * addresses are not used to access executable code.
 *****************************************************************************/
template <typename ProgramPoint>
class AbstractProgramPoint   /* abstract */
{

public:
  virtual ~AbstractProgramPoint() { }

  /*! \brief Define the canonical program point associated to an
    address at initialisation of the execution. Note that the address
    is a concrete address because it is intended to be used with the
    concrete starting address of the microcode program. */
  static ProgramPoint *init_program_point(MicrocodeAddress addr);

  /*! \brief Each program point corresponds to a unique program
     counter address via this function. It is used to get the
     corresponding instruction of the microcode program. Again we use
     concrete addresses. */
  virtual MicrocodeAddress to_address() = 0;

  /*! \brief Determine the next program point, when one follows an
      edge of the microcode with target addr. Again we use concrete
      addresses. This is the base program point constructor.  \todo
      next should know the edge and also the context if we want rich
      program points */
  virtual ProgramPoint next(MicrocodeAddress addr) = 0;

  /*! \brief Checks equality of two ProgramPoint's */
  virtual bool equals(const ProgramPoint &) const = 0;

  /*! \brief Needed to store ProgramPoints in a map */
  virtual bool lessThan(const ProgramPoint &) const = 0;

  /*! \brief Pretty printing */
  virtual std::string pp() const = 0 ;

private:
  /*! \brief deprecated, aborts */
  virtual bool operator== (const ProgramPoint &) const = 0;

  /*! \brief deprecated, aborts */
  virtual bool operator< (const ProgramPoint &) const = 0;
};

/*****************************************************************************/
/*! \brief A pending arrow may have several status.
 *  \todo instead of categorizing each pending arrow with its status,
 *        store each kind of pending arrows in its own bag
 *****************************************************************************/
typedef enum
{
  PAS_PENDING,                  //! The arrow has not been explored yet
  PAS_UNABLE_TO_EVAL_CONDITION, //! The arrow has already been explored
  //  but condition could not be evaluated.
  PAS_UNABLE_TO_EVAL_TARGET,    //! The arrow has already been explored the
  // condition was true but target could
  // not be evaluated.
} PendingArrowStatus;


/*****************************************************************************/
/*! \brief The enclosing class for pending arrows
 *         Pending arrows are the elements of the "work list" of the analysis
 *****************************************************************************/
TEMPLATE
class PendingArrow
{

public:

  /*! \brief The status of the pending arrow, see PendingArrowStatus
      for documentation */
  PendingArrowStatus status;

  /*! \brief The origin of the pending arrow */
  ProgramPoint pp;

  /*! \brief The pending arrow */
  StmtArrow *arr;

  /*! \brief Constructor */
  PendingArrow(ProgramPoint pp, StmtArrow *arr, PendingArrowStatus st) :
    status(st), pp(pp), arr(arr) 
  {
  }

  /*! \brief Copy constructor */
  PendingArrow(const PendingArrow &pa) :
    status(pa.status), pp(pa.pp), arr(pa.arr) 
  {
  }

};

/*****************************************************************************/
/*! \brief Report result for the AbstractExecContext::step method */
typedef enum
{
  SR_OK,                             //! Transition is ok
  SR_CONDITION_FALSE,                //! The condition is not fulfilled
  SR_UNABLE_TO_EVALUATE_CONDITION,   //! The condition could not be evaluated
  SR_UNABLE_TO_EVALUATE_TARGET,      //! The target could not be evaluated
  SR_TARGET_NOT_FOUND                //! No target! \todo may throw an exception
} StepResult;

/*****************************************************************************/
/*! \brief Here is the interpreter global data structure. It maintains
 *   - the access to microcode instructions
 *   - the table associating program point to contexts.
 *  This should be the main entry point for the interpreter.
 * \todo rename as Interpreter?
 *****************************************************************************/
TEMPLATE
class AbstractExecContext
{
public:
  typedef PendingArrow<TEMPLATE_ARGS> Arrow;
  typedef AbstractContext<TEMPLATE_ARGS> Context;

protected:

  /*! \brief The pointer to the program. This is via this that we
   * access to microcode instruction.
   * \todo should be replaced by a traversable view by Renaud. */
  MicrocodeStore *program;

  /***************************************************************************/

public:  /*! \todo : should be private */

  /*! \brief The map associating a context to program points. This map
      is filled step by step during the interpretation. */
  typedef typename   
  std::map<ProgramPoint, AbstractContext<TEMPLATE_ARGS> *, 
	   LessThanFunctor<ProgramPoint> > ExecMap;
  ExecMap exec_map;

  /*! \brief One maintains the list of pending arrows. These are the
      arrow which remains to be interpreted. When a new context is
      added or merged (returning true) at a given program point, then
      one adds to this list the outgoing arrows. A pending arrow may
      have several status (see PendingArrow class for documentation) */
  typedef typename   
  std::list< PendingArrow<TEMPLATE_ARGS> > PendingArrows;

  PendingArrows pending_arrows;

  /***************************************************************************/
public:

  virtual ~AbstractExecContext();

  /*! \brief Initialize the global table (program point x
      context). First it retrieves the entry point of the microcode
      program, then it construct the initial program point from it and
      it insert ctxt at this program point, adding the outgoing edges
      to the pending arrow list.*/
  virtual void init(AbstractContext<TEMPLATE_ARGS> *ctxt);

  /*! \brief Choose a pending arrow (the first) and interpret
      it. After that the pending arrow is deleted from the list.
      \remark One could parametrize this function by a choosing
      strategy.
      \return false if there was no pending arrow any more. */
  virtual bool generic_step();

  /*! \brief The entry point for stepping function, may be overloaded
      by the user if additional operations must be performed. For
      instance, in the simulator, any context without pending edge can
      be forgotten.
      \return false if there was no pending arrow any more. */
  virtual bool step()
  {
    return generic_step();
  };

  /***************************************************************************/

  /*! \brief Interpret a particular edge (supposed to come from the
    pending arrow list). See StepResult type for result documentation */
  virtual StepResult step(Arrow pa);

  /*! \brief Insert a new pair (program point x context) in the global
      table and set it as fresh, i.e., all outgoing arrows are set to
      be pending. */
  virtual void set_context_and_request_update(ProgramPoint &pp,
					AbstractContext<TEMPLATE_ARGS> *ctxt);

  /*! \brief Add all outgoing edges of the microcode node
      corresponding to pp to the pending arrows list. This method is
      used for instance when a context must be updated.  */
  /*! \todo change the name of the method */
  virtual void request_update(ProgramPoint &pp);

  /***************************************************************************/

  /*! \brief Delete a pending arrow from the list no matter of its status. */
  virtual void delete_pending_arrow(ProgramPoint &pp, StmtArrow *arr);

  /*! \brief Delete a pending arrow from the list */
  virtual void delete_pending_arrow(PendingArrow<TEMPLATE_ARGS> pa);

  /*! \brief Modifies the status of a pending arrow in the list */
  virtual void pending_arrow_set_status(ProgramPoint &pp,
                                        StmtArrow *arr,
                                        PendingArrowStatus st);

  /*! \brief Add a pending arrow to the list */
  virtual void add_pending_arrow(ProgramPoint pp,
                                 StmtArrow *arr,
                                 PendingArrowStatus st);

  /***************************************************************************/

  /*! \brief Retrieves a particular node of the microcode graph from a
      program point. */
  virtual MicrocodeNode *get_node(ProgramPoint &pp);

  /*! \brief Retrieves the context at a given program point if it is
      defined. */
  virtual Option<AbstractContext<TEMPLATE_ARGS> *>
	get_current_context(ProgramPoint &pp);

  /*! \brief Retrieves the context at a given program point if it is
      defined. */
  virtual Option<AbstractContext<TEMPLATE_ARGS> *>
  get_current_context ();

  virtual ProgramPoint
  get_current_program_point ();

  /***************************************************************************/

  /*! \brief Pretty printing */
  virtual std::string pp();

};

#include "microcode_exec.ii"

#undef TEMPLATE
#undef TEMPLATE_ARGS

#endif /* MICROCODE_EXEC_HH */

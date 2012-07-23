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

#ifndef INTERPRETERS_SETS_SETS_CONTEXT_HH
#define INTERPRETERS_SETS_SETS_CONTEXT_HH

#include <analyses/microcode_exec.hh>
#include <domains/common/ConcreteProgramPoint.hh>
#include <domains/sets/SetsAddress.hh>
#include <domains/sets/SetsExprSemantics.hh>
#include <domains/sets/SetsMemory.hh>
#include <domains/sets/SetsValue.hh>
#include <kernel/Architecture.hh>
#include <utils/option.hh>

#include <list>
#include <map>

#define SETS_CLASSES          \
  SetsAddress,                \
  SetsValue,                  \
  SetsExprSemantics,          \
  SetsMemory,                 \
  ConcreteProgramPoint

class SetsContext : public AbstractContext<SETS_CLASSES>
{
public:
  /*! \brief basic constructor */
  SetsContext(SetsMemory *mem);

  /*! \brief \tSetsodo destructor */
  virtual ~SetsContext();

  /*! \brief clone the context. */
  virtual SetsContext *clone();

  /*! \brief the merging of two contexts consists in the union of sets
      l-value by l-value */
  virtual bool merge(AbstractContext<SETS_CLASSES> * other);

  /*! \brief construct a context with an empty memory. */
  static SetsContext *empty_context();

  /*! \brief One specializes the evaluation function. It is use to
      optimize the computations, by avoiding brute cartesian products
      all the time. */
  SetsValue eval(const Expr *e);

  /*! \brief Split a context according to a given condition. Returns a
   *  pair of contexts (ctxt1, ctxt2). ctxt1 (resp. ctxt2) is an upper
   *  set enclosing the values making the condition true
   *  (resp. false). If the condition is always true (resp. false)
   *  then one returns None for the false context (resp. true). */
  std::pair< Option<AbstractContext<SETS_CLASSES>*>, Option<AbstractContext<SETS_CLASSES>*> >
  split_context(Expr *condition);

};

/*****************************************************************************/
/* Non Deterministic Evaluation                                              */
/*****************************************************************************/

class SpecializedContextNotSpecialized {};

// OPTIM : chain the specialized context with each other to save space.
class SpecializedContext
{

public:
  SpecializedContext(SetsContext *ctxt);
  SpecializedContext(const SetsContext &other);
  ~SpecializedContext();

  /*! \brief The underlying context is the whole memory. */
  SetsContext *underlying_context;

  /*! \brief The list of all the specialized cells. Caution, values
      must be compatible to the underlying context. None in the right
      member of the pair encodes the TOP values i.e. ANY value is
      possible. */
  std::list < std::pair < ConcreteAddress, Option<ConcreteValue> > > specialised_mem_cells;

  /*! \brief The list of all the registers. Caution, values
      must be compatible to the underlying context. None in the right
      member of the pair encodes the TOP values i.e. ANY value is
      possible. */
  std::list < std::pair < const RegisterDesc *, Option<ConcreteValue> > > specialised_registers;

  /*********************************/

  /*! \brief specialize a memory cell. Launch an internal error if the value
   is not in the underlying context. */
  void specialize(ConcreteAddress addr, Option<ConcreteValue> v);

  /*! \brief specialize a register. Launch an internal error if the value
   is not in the underlying context. */
  void specialize(const RegisterDesc *reg, Option<ConcreteValue> v);

  /*! \brief gets the specialized value corresponding to a given address. Launch
   *   an internal error if the address has not been specialized.
   * \raise SpecializedContextNotSpecialized if the addr is not specialized */
  Option<ConcreteValue> get_specialized(ConcreteAddress addr);

  /*! \brief gets the specialized value corresponding to a given register. Launch
   *  an internal error if the address has not been specialized.
   * \raise SpecializedContextNotSpecialized if the addr is not specialized */
  Option<ConcreteValue> get_specialized(const RegisterDesc *reg);

  /*! \brief once contexts have been specialized and selected
    depending on the targetted value, one reconstructs a new
    context. Caution, all the contexts of s_ctxts must have the same
    underlying set_context. Returns None if the list is empty. */
  static Option<AbstractContext<SETS_CLASSES>*>
  merge_contexts(std::list< SpecializedContext *> s_ctxts);

};

/*! \brief The base result of the expression evaluation function. This
  return a disjunctive list of result associated to specialised
  contexts. Note that during the evaluation of the expression any
  accessed l-value becomes specialized */
#define ND_eval_result std::list< std::pair< Option<ConcreteValue>, SpecializedContext *> >

/*! \brief The recursive evaluation of expression.  Compute all
 *  possible values, each of them associated to a specialized
 *  context. The specialized context record all the choices of value
 *  in any l-value set (even if there is only one choice!)
 *
 *  TODO: differencier les comportements sur TOP, ici, tout calcul sur TOP retourne TOP,
 *  a l'exception du produit par 0. Pour ce faire, le mieux est d'implementer SetsExprSemantic
 */
ND_eval_result ND_eval(SpecializedContext *s_ctxt, const Expr *e);


class SetsExecContext : public AbstractExecContext<SETS_CLASSES>
{

public:
  SetsExecContext(MicrocodeStore *prg)
  {
    program = prg;
  }
  virtual ~SetsExecContext() {}

};

#endif /* INTERPRETERS_SETS_SETS_CONTEXT_HH */

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

#ifndef SLICING_H
#define SLICING_H

#include <list>
#include <map>
#include <domains/common/ConcreteProgramPoint.hh>
#include <kernel/Architecture.hh>
#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>
#include <kernel/expressions/Formula.hh>
#include <kernel/microcode/MicrocodeNode.hh>
#include <utils/option.hh>
#include <utils/map-helpers.hh>


class DataDependency;
class DataDependencyLocalContext;
class LocatedLValue;

/*! Compute the list of l-values on which the expression e depends on.
 *  Caution, we do not consider nested l-values. This means that if
 *  e depends on some lvalue like [%12 + 2], then %12 will not be listed
 *  into the dependencies. Indeed collecting [%12 + 2], and not %12 indicates
 *  the real dependency, and is actually more precise. */
std::list<const LValue *> dependencies(Expr *e);

/* same as before but with nested dependencies */
std::list<const LValue *> nested_dependencies(Expr * e);

/*! An instance of this class will be associated to each program point, here is
 * the kernel of the slicing algorithm, i.e. the back step along arrows. */
class DataDependencyLocalContext {

  /* the global structure of the fixpoint */
  DataDependency * fixpoint_structure;

  /* Here are the lvalue to watch. This is a set encoded by a logical
   * formula (see ConditionalSet.h) */
  Expr * the_lvalues;

public:
  DataDependencyLocalContext(DataDependency * fixpoint_structure);
  DataDependencyLocalContext(const DataDependencyLocalContext &other);
  ~DataDependencyLocalContext();
  DataDependency * get_global_context() { return fixpoint_structure; };
  Expr ** get_watched_lvalues() { return & the_lvalues; };

public:

  /* back interpret a static arrow and produce a new context from
   * the current one. Precisely, the current context (this) has a list
   * of lvalues to watch (the dependencies). Then this method runs
   * backward an arrow and computes the new list of lvalue to watch
   * and put it into a new context.
   *
   * TODO: the method could tell whether the watched lvalue are
   * independant of the statement of the arrow or not. */
  DataDependencyLocalContext * run_backward(StaticArrow *);

  /* Returns true if and only if the previous arrow must be inspected,
   * i.e. if the current list of watched lvalue changed with the merging
   * or not. */
  bool merge(DataDependencyLocalContext *other);
};

class LocatedLValue {
private:
  ConcreteProgramPoint pp;
  LValue *lv;
public:
  LocatedLValue(const LocatedLValue &other);
  LocatedLValue (MicrocodeAddress addr, const LValue *lv);
  ~LocatedLValue ();

  const ConcreteProgramPoint &get_ProgramPoint () const;
  const LValue *get_LValue () const;
};

class DataDependency {

private:
  Microcode * the_program;
  std::map<ConcreteProgramPoint, DataDependencyLocalContext *, 
	   LessThanFunctor<ConcreteProgramPoint> > the_fixpoint;
  std::list<StaticArrow *> pending_arrows;
  bool fixpoint_reached;

  /*! Realise an inverse step:
   * - pick an arrow in the pending arrow list
   * - interpret the arrow (run_backward) on the context of the target of
   *   the arrow (must be a static arrow).
   * - at the origin of the arrow, merge the new context with the
   *   existing one: the union of the lvalues sets.
   * - update the pending arrow list if this last context has been modified.
   * returns true if and only if the fixpoint has been reached. */
  bool InverseStep();

  DataDependencyLocalContext *get_local_context (ConcreteProgramPoint pp);

  /*! push the arrows pointing on pp into the pending arrow list */
  void update_from_program_point(ConcreteProgramPoint pp);

  /* algorithm parameters*/
  static bool consider_jump_cond_flag;
  static bool only_simple_sets_flag;

public:

  /*! Initializes the fixpoint calculus:
   * - puts the seeds into the fixpoint map
   * - puts the inverse arrows into the pending arrow list. */
  DataDependency(Microcode *prg, std::list<LocatedLValue> seeds);
  ~DataDependency();
  /* Iterates InverseStep until reaching the fixpoint (or max step nb reached). */
  void ComputeFixpoint(int max_step_nb);

  /*! Get the result at program point pp from the current state of the fixpoint.
   *  If the fixpoint has not been reached already, then
   *  one does at most max_step_nb more step before returning the result. */
  Expr * get_dependencies(ConcreteProgramPoint pp, int max_step_nb);

  /*! Get the result at program point pp from the current state of the fixpoint.
   *  This simplified version gives all the possibilities.
   *  If the fixpoint has not been reached already, then
   *  one does at most max_step_nb more step before returning the result. */
  std::vector<Expr*> get_simple_dependencies(ConcreteProgramPoint pp, int max_step_nb);

  /*! In the computation of the slicing, consider or not conditions on arrows.
   * considering them (ConsiderJumpCondMode(true)) means adding them in the conditional set. */
  static void ConsiderJumpCondMode(bool set);
  static bool ConsiderJumpCond();
  /*! Here we only consider flat sets, without any conditions */
  static void OnlySimpleSetsMode(bool set);
  static bool OnlySimpleSets();

  /* Returns an upper set of the set of arrow that may influence the value of the seed.
   * A seed is a located lvalue, ie. a particular lvalue at a particular program point. */
  static std::vector<StmtArrow*> slice_it(Microcode * prg, std::list<LocatedLValue> seeds);
  static std::vector<StmtArrow*> slice_it(Microcode * prg, MicrocodeAddress seed_loc, const Expr *seed);

  /* Tells whether a statement is used or not in a piece of microcode.
   * Note that when a not resolved dynamic jump is found, or a missing node,
   * one supposes that anything can occur. */
  static bool statement_used(Microcode * prg, StmtArrow* arr);

  /* Tags the useless arrows in a piece of microcode. Note that when a not resolved dynamic
   * jump is found, or a missing node, one supposes that anything can occur. */
  static std::vector<StmtArrow*> useless_statements(Microcode * prg);

};

#endif /* SLICING_H */

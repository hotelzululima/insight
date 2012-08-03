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
#ifndef KERNEL_EXPRESSIONS_FORMULA_HH
#define KERNEL_EXPRESSIONS_FORMULA_HH

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <utils/Object.hh>
#include <utils/option.hh>

#include <iostream>
#include <string>
#include <vector>
#include <tr1/unordered_set>

/*****************************************************************************/
/* ATTENTION CHANTIER -- ATTENTION CHANTIER -- ATTENTION CHANTIER            */
/*****************************************************************************/

/* TODO:
 - export vers smt solver et/ou alt-ergo solver.
 - integration avec Microcode::sequencialize() function to get Filliatre stuff.
 */

/*****************************************************************************/

// \todo peut etre changer de nom : Formula <- Expr et Expr <- MicrocodeExpr

class Formula;
class FormulaVisitor;
class ConstFormulaVisitor;

class Expr;       // (Abstract)
class Constant;   // --> Expr
class Variable;   // --> Expr
class UnaryApp;   // --> Expr
class BinaryApp;  // --> Expr
class LValue;     // --> Expr (Abstract)
class MemCell;    // --> LValue
class RegisterExpr;   // --> LValue

class Statement;
class StmtArrow;

class MCPath;

/*****************************************************************************/
/*! \brief This is the base class for encoding Logical formulae.
 *  Formulae are defined as terms like expression.
 *
 *  Instances of the class Expr are themselves considered as atomic
 *  formula (whose validity is non equality to 0).*/
class Formula 
{
  /*****************************************************************************/
protected:
  Formula();

  virtual ~Formula() ;

public:
  static void init ();
  static void terminate ();
  
  virtual void acceptVisitor (FormulaVisitor &visitor);
  virtual void acceptVisitor (ConstFormulaVisitor &visitor) const;
  virtual void acceptVisitor (FormulaVisitor *visitor) = 0;
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const = 0;

  virtual std::string to_string() { return pp(); }
  /*****************************************************************************/
  /* TODO TODO TODO TODO                                                       */
  /*****************************************************************************/

  /*! \brief call external tool to try to evaluate the formula.
   *  At the moment, the function try to decide the formula with
   *  Simplify tool. */
  Option<bool> eval_with_external();

  /*****************************************************************************/
  /* Formula Construction                                                      */
  /*****************************************************************************/

  /*! \brief construct the formula A ==> B.
   *  Caution A and B are not copied */
  static Formula * implies(Formula *A, Formula *B);

  /*! \brief construct the formula (cond /\ A) \/ ((Not cont) /\ B).
   *  Caution A and B are not copied */
  static Formula * IfThenElse(Formula *cond, Formula *A, Formula *B);

  /*! \brief construct the formula, actually the expression (EQ A B).
   *  Caution A and B are not copied */
  static Formula * Equality(Expr *A, Expr *B);

  /*****************************************************************************/
  /* Simplification System                                                     */
  /*****************************************************************************/

  /*****************************************************************************/

  virtual bool has_type_of (const Formula *) const { return false; };


  /*! \brief pretty printing */
  virtual std::string pp(std::string prefix = "") const = 0;
  virtual std::string to_string() const;

  /*! operations needed for unordered_set storage */
  virtual size_t hash () const;
  virtual bool equal (const Formula *F) const = 0;

  struct Hash { 
    size_t operator()(const Formula *const &F) const; 
  };

  struct Equal { 
    bool operator()(const Formula *const &F1, const Formula * const &F2) const; 
  };

  Formula *ref () const;

  void deref ();

protected:
  static Formula *find_or_add_formula (Formula *F);

  template<typename C>
  static C *find_or_add (C *F) { 
    Formula *res = find_or_add_formula (F);
    return dynamic_cast<C *> (res);
  }
  
private:
  typedef std::tr1::unordered_set<Formula *, Formula::Hash, Formula::Equal> FormulaStore;  

  static FormulaStore *formula_store;
  static void dumpStore ();
  mutable int refcount;
};

#endif /* KERNEL_EXPRESSIONS_FORMULA_HH */

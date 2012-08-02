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

#include <kernel/Annotation.hh>
#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/expressions/FormulaRewritingRule.hh>
#include <utils/Object.hh>
#include <utils/option.hh>
#include <utils/infrastructure.hh>

#include <cassert>
#include <iostream>
#include <list>
#include <string>
#include <tr1/unordered_set>
#include <tr1/unordered_map>
#include <vector>

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

class AtomicFormula; // (abstract) --> Formula
class NaryBooleanFormula;  // --> Formula
class ConjunctiveFormula;  // --> NaryBooleanFormula
class DisjunctiveFormula;  // --> NaryBooleanFormula
class NegationFormula;     // --> NaryBooleanFormula
class QuantifiedFormula;     // --> NaryBooleanFormula

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

  /*! \brief add a new conjunctive clause to the current formula,
   *  Caution c is not copied
   *  Note that this is a "functional version" with initial copy of 'this' */
  Formula * add_conjunctive_clause(Formula *c) const;

  /*! \brief add a new conjunctive clause to the current formula in place.
   *  Caution c is not copied */
  static void add_conjunctive_clause(Formula **phi, Formula *c);

  /*! \brief add a new disjunctive clause to the current formula,
   *  Caution c is not copied
   *  Note that this is a "functional version" with initial copy of 'this' */
  Formula * add_disjunctive_clause(Formula *c) const;

  /*! \brief add a new disjunctive clause to the current formula in place.
   *  Caution c is not copied */
  static void add_disjunctive_clause(Formula **phi, Formula *c);

  /*! \brief construct the formula (cond /\ A) \/ ((Not cont) /\ B).
   *  Caution A and B are not copied */
  static Formula * IfThenElse(Formula *cond, Formula *A, Formula *B);

  /*! \brief construct the formula, actually the expression (EQ A B).
   *  Caution A and B are not copied */
  static Formula * Equality(Expr *A, Expr *B);

  /*****************************************************************************/
  /* Simplification System                                                     */
  /*****************************************************************************/

  /*! \brief simplification of lower level:
   *  - simplify syntactic equality
   *  - compute expression when possible (\todo: not complete, at the moment: just NOT operator)
   *  - delete trivial clauses in conjunction and disjunction.
   */
  /*! \brief simple syntaxic evaluation: try to transform a true
      formula into a bool. */
  Option<bool> try_eval_level0() const;

  /*! \brief return true iff the formula can be reduce to true. */
  bool eval_level0() const;

  /*****************************************************************************/

  bool is_Expr() const;
  bool is_AtomicFormula() const;
  bool is_ConjunctiveFormula() const;
  bool is_DisjunctiveFormula() const;
  bool is_NegationFormula() const;

  bool is_QuantifiedFormula() const;
  bool is_ExistentialFormula() const;
  bool is_UniversalFormula() const;
  bool is_BooleanConstantFormula() const;
  bool is_TrueFormula() const;
  bool is_FalseFormula() const;

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

  static Formula *parse (MicrocodeArchitecture *arch, 
			 const std::string &input);

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

/*****************************************************************************/
/*! \brief Here are defined atomic formula. At the moment, the only atomic
 *  formula are expressions, evaluated to be true iff it is
 *  equal to 1. However, this intermediate class (between Formula and
 *  Expr) should be usefull for future extension of the logical language. */
class AtomicFormula : public Formula   /* Abstract */
{
  /*****************************************************************************/

protected:
  /* \brief base constructor */
  AtomicFormula() : Formula() {};

  virtual ~AtomicFormula() {}

public:


  /*! \brief virtual destructor definition for abstract class */

  /*****************************************************************************/

  /*! \brief pretty printing */
  virtual std::string pp(std::string prefix = "") const = 0;

};

class BooleanConstantFormula : public AtomicFormula
{
private:
  BooleanConstantFormula (bool value); 
  
  bool value;

  virtual ~BooleanConstantFormula();

public:

  static BooleanConstantFormula *create (bool value);

  virtual bool get_value () const;

  virtual bool has_type_of (const Formula *F) const;

  virtual std::string pp(std::string prefix = "") const;

  virtual size_t hash () const;

  virtual bool equal (const Formula *F) const;

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};


class NaryBooleanFormula : public Formula
{
public:
  typedef std::vector<Formula *> Operands;
  typedef Operands::iterator OperandsIterator;
  typedef Operands::const_iterator OperandsConstIterator;



  virtual Operands get_operands_copy () const;

  virtual const Operands &get_operands () const;
  virtual OperandsConstIterator const_operands_begin () const {
    return get_operands().begin ();
  }
  virtual  OperandsConstIterator const_operands_end () const {
    return get_operands().end ();
  }

  virtual std::string pp (std::string prefix = "") const = 0;

  virtual size_t hash () const;

  virtual bool equal (const Formula *F) const;

  virtual NaryBooleanFormula *
  create_from_operands (const Operands &ops) const = 0;

protected:
  NaryBooleanFormula (Formula *op);
  NaryBooleanFormula (Formula *op1, Formula *op2);
  NaryBooleanFormula (const Operands &args);
  virtual ~NaryBooleanFormula ();

private:  
  Operands ops;
};

class ConjunctiveFormula : public NaryBooleanFormula
{
public:

  static ConjunctiveFormula *create (Formula *A, Formula *B);

  static ConjunctiveFormula *create (const Operands &args);

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;

  virtual std::string pp (std::string prefix = "") const;

  virtual bool has_type_of (const Formula *F) const;

  virtual std::vector<Formula *> get_clauses_copy() const;

  virtual const std::vector<Formula *> &get_clauses() const;

  virtual NaryBooleanFormula *create_from_operands (const Operands &ops) const;

private:
  ConjunctiveFormula (Formula *op1, Formula *op2);

  ConjunctiveFormula (const Operands &args);
  virtual ~ConjunctiveFormula ();
};

/*****************************************************************************/

class DisjunctiveFormula : public NaryBooleanFormula
{
public:

  static DisjunctiveFormula *create (Formula *A, Formula *B);

  static DisjunctiveFormula *create (const Operands &args);

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;

  virtual std::string pp(std::string prefix = "") const;

  virtual bool has_type_of (const Formula *F) const;

  virtual std::vector<Formula *> get_clauses_copy() const;

  virtual const std::vector<Formula *> &get_clauses() const;

  virtual NaryBooleanFormula *create_from_operands (const Operands &ops) const;

private:
  DisjunctiveFormula (Formula *op1, Formula *op2);

  DisjunctiveFormula (const Operands &args);

  virtual ~DisjunctiveFormula();
};

/*****************************************************************************/

class NegationFormula : public NaryBooleanFormula
{
public:

  static NegationFormula *create (Formula *phi);

  const Formula *get_neg() const;

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;

  virtual std::string pp(std::string prefix = "") const;

  virtual bool has_type_of (const Formula *F) const;

  virtual NaryBooleanFormula *create_from_operands (const Operands &ops) const;

private:
  NegationFormula (Formula *phi);

  virtual ~NegationFormula();
};

/*****************************************************************************/
class QuantifiedFormula : public NaryBooleanFormula
{

public:

  static QuantifiedFormula *create (bool exist, Variable *var, Formula *phi);
  static QuantifiedFormula *createE (Variable *var, Formula *phi);
  static QuantifiedFormula *createA (Variable *var, Formula *phi);

  bool is_exist () const;

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;

  const Variable *get_variable() const;

  const Formula *get_body() const;

  virtual std::string pp(std::string prefix = "") const;

  virtual size_t hash () const;

  virtual bool equal (const Formula *F) const;

  virtual bool has_type_of (const Formula *F) const;

  virtual NaryBooleanFormula *create_from_operands (const Operands &ops) const;
  
private:
  QuantifiedFormula (bool exist, Variable *var, Formula *phi);

protected:
  virtual ~QuantifiedFormula ();

  bool exist;
};

#endif /* KERNEL_EXPRESSIONS_FORMULA_HH */

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
#ifndef KERNEL_EXPRESSIONS_HH
#define KERNEL_EXPRESSIONS_HH

#include <map>
#include <list>
#include <string>
#include <vector>

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/expressions/Formula.hh>
#include <kernel/expressions/Operators.hh>

/*****************************************************************************/
/* Summary                                                                   */
/*****************************************************************************/
class Expr;       // (Abstract)
class Constant;   // --> Expr
class Variable;   // --> Expr
// class BitIntExpr; // --> Expr  (template)
class UnaryApp;   // --> Expr
class BinaryApp;  // --> Expr
class TernaryApp;  // --> Expr
class LValue;     // --> Expr (Abstract)
class MemCell;    // --> LValue
class RegisterExpr;   // --> LValue
// class BitIntLVal; // --> LValue (template)
/*****************************************************************************/
class TermReplacingRule;
class TermReplacingRuleNd;
class BottomUpInfo;
class TopBottomInfo;
/*****************************************************************************/

// \todo : sub-expression sharing

/*****************************************************************************/
/*! \brief
 *  The class Expr (for Expression) is the main entry point for defining
 *  microcode expressions.
 *
 * Expression syntax is defined by
 *   - Expression (right values) (class Expr)
 *     -# Variables (class Variable)
 *     -# Constants (class Constant)
 *     -# Unary Applications (class UnaryApp)
 *     -# Binary Applications (class BinaryApp)
 *     -# Bit interval extraction (class BitIntBase<Expr>)
 *   - L-values   (left values) (class LValue)
 *     -# Memory Cell (class MemCell)
 *     -# Registers (class RegisterExpr)
 *     -# Bit interval extraction (class BitIntBase<LValue>)
 *
 *  The Expr class is abstract, and LValue also, they are used for type
 *  organisation.
 *****************************************************************************/
class Expr : public AtomicFormula /* Abstract */ {
private:

  /*! \brief The value of each expression is restricted to a
    particular bit vector. This is an interval of bits the index of
    the first one being bv_offset. */
  int bv_offset;

  /*! \brief The size in bit of the interval of bits. */
  int bv_size;

  /*****************************************************************************/


protected:
  /*! \brief Default constructor. Caution, this is an abstract class,
      it is called by inherited constructor explicitely */
  Expr(int bv_offset, int bv_size);

  virtual ~Expr();

public:

  virtual size_t hash () const;
  virtual Expr *ref () const { return (Expr *) Formula::ref (); }

  /*****************************************************************************/

  /*! \brief the size of the bit vector. */
  int get_bv_size() const;
  /*! \brief define the index of the first bit position of the bit vector */

  /*! \brief the index of the first bit of the bit vector. */
  int get_bv_offset() const;
  /*! \brief define the index of the first bit position of the bit vector */

protected:
  virtual Expr *
  change_bit_vector (int new_bv_offset, int new_bv_size) const = 0;

public:
  virtual Expr *
  extract_bit_vector (int new_bv_offset, int new_bv_size) const;

  virtual Expr *
  extract_with_bit_vector_of (const Expr *e) const;

  virtual Expr *
  extract_with_bit_vector_size_of (const Expr *e) const;

  static void 
  extract_bit_vector (Expr *&e,int new_bv_offset, int new_bv_size);

  static void 
  extract_with_bit_vector_of (Expr *&e, const Expr *other);

  static void
  extract_with_bit_vector_size_of (Expr *&e, const Expr *other);

  /*****************************************************************************/
  // Type checking
  /*****************************************************************************/

  bool is_Variable() const;
  bool is_Constant() const;
  bool is_UnaryApp() const;
  bool is_BinaryApp() const;
  bool is_TernaryApp() const;
  bool is_LValue() const;
  bool is_MemCell() const;
  bool is_RegisterExpr() const;

  virtual bool has_type_of (const Formula *F) const = 0;

  /*****************************************************************************/
  // Rewriting operations
  /*****************************************************************************/

  /*! \brief bottom-up application of term transformation rule. The
   *  rule is applied recursively from bottom leaves to top.
   *
   *  \param r contains a rule of term transformation (see
   *  TermReplacingRule class). Note that during implementation of
   *  the rule, the function f may raise NotApplicable exception if
   *  the rule is not applicable. The mechanism allows to know whether
   *  a rule has indeed been applied or not.
   *
   *  \param bottom_up_info belongs to the mechanism of transmitting
   *  information from bottom to up. More precisely, a pass may want to
   *  transmit information from operations done
   *  at bottom to operation done at upper levels. bottom_up_info is used
   *  for that. When f is applied at some point, it can put some information in
   *  the bottom_up_info object (and before, read information coming from
   *  previous f applications), this information is then kept and transmitted
   *  to next operations. If you do not need such a mechanism, just put NULL
   *  in it and it shall be ignored. The information is read and modified
   *  in the action function of the rule to be applied (TermReplacingRule::f).
   *  To use it, the user must derive its own class form BottomUpInfo.
   *
   *  \param top_bottom_info this enforces a mechanism to transmit information
   *  collected during the descent to a node of the term. This means that
   *  when the processing arrives to a given term, then top_bottom_info
   *  has seen and processed all the terms enclosing this term from the top (the
   *  root) to the considered term. To use it, the user must derive
   *  its own class from TopBottomInfo.
   *
   *  \return the new address of the term after replacement. Note that
   *  this address may be the same as the current instance.
   *
   *  \remark The function does the replacement in place. This means
   *  that the current instance of expression is a priori
   *  modified. However, the function returns the new address of the
   *  term, because, if the type of the root of the term (the top)
   *  change, a new allocation must be done. This behavior is
   *  designed for efficiency, saving memory re-allocations as much as
   *  possible.
   *
   *  \todo a non destructive bottom_up_apply function with duplication.
   *  raise a NotApplicable exception if there is no change */
  virtual Expr * bottom_up_apply (TermReplacingRule *r,
				  TopBottomInfo *top_bottom_info = NULL,
				  BottomUpInfo **bottom_up_info = NULL) const = 0;

  /*! The parameter e points to the location where is the expression. Caution
   *  The function may modify the location of the resulting expression.
   *  Returns true iff there has been indeed some application of the rule. */
  static bool bottom_up_apply_in_place(Expr ** e,
                                       TermReplacingRule * r,
                                       TopBottomInfo * top_bottom_info = NULL,
                                       BottomUpInfo ** bottom_up_info = NULL);

  /*! Applies rules until no one can be applied.
   *  Return true iff at least one rule has been applied and modified the term.
   *  If max_pass_nb = -1 then there is no loop guard. */
  static bool bottom_up_apply_in_place_closure(Expr ** e,
					       std::vector<TermReplacingRule *> rules,
					       int max_pass_nb = -1);

  /*! \brief bottum up application of non-deterministic term replacement rule.
   *  This transformation is NOT performed IN-PLACE !
   *  \param  r the rule to apply
   *  \returns  a list of clone of this expr, where replacement has been done */
  virtual std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const = 0;

  /*****************************************************************************/

  /*! \brief apply the replacing to the current expression as an
   *  atomic formula. This is the implementation of
   *  Formula::bottom_up_apply_in_place.
   *
   *  Caution, the case where an expression should be replaced by a
   *  formula works only when the expression is directly belonging
   *  to a formula. \todo extend that */
  virtual Formula *bottom_up_apply (FormulaReplacingRule *r) const
    throw (NotApplicable);

  /*****************************************************************************/
  // Pattern matching mechanism.
  /*****************************************************************************/

  /*! Replace variable in place (by using bottom_up_apply_in_place function).
   *  \param v The variable to be replaced.
   *  \param value The value to be put in place of v.
   *  \return the new address of the term after replacement. Note that
   *  this address may be the same as the current instance. */
  Expr *replace_variable (const Variable *v, const Expr *value) const;
  static bool replace_variable_in_place(Expr **e, const Variable *v, 
					const Expr *value);

  /*! Replace variable in place (by using bottom_up_apply_in_place function).
   *  \param v The variable to be replaced defined by its identifier.
   *  \param value The value to be put in place of v.
   *  \return the new address of the term after replacement. Note that
   *  this address may be the same as the current instance. */
  Expr *replace_variable (std::string v_id, const Expr *value) const;

  // \todo move all this somewhere else (?)
  // \todo Group all the rewrittings in a separate file with all the
  // rewrite patterns for the formula also, in order to have
  // everything at the same place.

  /*****************************************************************************/
  /*****************************************************************************/

  /*! \brief expression simplification. Returns true iff there has been some
   *  simplification. Result is put in place. */
  static bool simplify (Expr ** e);

  /*****************************************************************************/
  // Basic Queries
  /*****************************************************************************/

  /*! \brief true if o is a sub-expression of this expression */
  virtual bool contains(Expr *o) const = 0;

  /*! \brief return the depth of the expression as a tree (or a term) */
  virtual unsigned int get_depth() const = 0;

  /*****************************************************************************/
  // Pretty printing
  /*****************************************************************************/

  /*! \brief Pretty printing. */
  virtual std::string pp(std::string prefix = "") const = 0;

  /*! \brief Print the bit vector if it is not default */
  std::string bv_pp() const;

  static Expr *parse (MicrocodeArchitecture *arch, 
		      const std::string &input);
};

/*****************************************************************************/
/*! \brief
 *  General use Symbols
 *
 *  They are not element of the microcode language.
 *  Variables are used for term operations. A variable is just
 *  a leaf defined by an identifier (a string). They can be used to define
 *  parameters of some piece of code for instance, or of a logical formula.
 *****************************************************************************/
class Variable : public Expr {
private:
  /*! A Variable is defined by a string identifier */
  std::string id;

  Variable(const std::string &id, int bv_offset, int bv_size);

  virtual ~Variable();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static Variable *create (const std::string &id, int bv_offset = 0, 
			   int bv_size = BV_DEFAULT_SIZE);

  std::string get_id() const;


  /*! \brief syntactic equality of variables */
  virtual bool equal (const Formula *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Formula *F) const;
  
  bool operator<(const Variable &other) const;  /* needed for using variables as key of maps */
  virtual unsigned int get_depth() const;
  bool contains(Expr *o) const;

  /* See Expr class for documentation */
  Expr *bottom_up_apply (TermReplacingRule *r, TopBottomInfo *top_bottom_info = NULL, BottomUpInfo **bottom_up_info = NULL) const;
  std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const;

  std::string pp(std::string prefix = "") const;

  virtual PatternMatching *
  pattern_matching(const Formula *e, 
		   const std::list<const Variable *> &free_variables) const;
  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};

/*****************************************************************************/
/*! \brief
 *  Encoding of concret word values.
 *****************************************************************************/
class Constant : public Expr {
private:
  constant_t val;

  Constant(constant_t v, int bv_offset, int bv_size);
  virtual ~Constant();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:

  static inline Constant *zero (int size = BV_DEFAULT_SIZE) { 
    return create (0, 0, size); 
  }
  static inline Constant *one (int size = BV_DEFAULT_SIZE) { 
    return create (1, 0, size); 
  }
  /* compute 2^{n-1}-1 */
  static inline Constant *max_signed (unsigned int n) { 
    constant_t val = 1;
    val <<= n - 1;
    val--;
    return create (val);
  }
  static inline Constant *max_unsigned (unsigned int n) { 
    constant_t val = 1;
    val <<= n;
    val--;
    return create (val);
  }

  static Constant *create (constant_t v, int bv_offset = 0, 
			   int bv_size = BV_DEFAULT_SIZE);

  constant_t get_val() const;

  /* See Expr class for documentation */
  Expr *bottom_up_apply (TermReplacingRule *r, TopBottomInfo *top_bottom_info = NULL, BottomUpInfo **bottom_up_info = NULL) const;
  std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const;


  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Formula *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Formula *F) const;

  bool contains(Expr *o) const;
  virtual unsigned int get_depth() const;

  std::string pp(std::string prefix = "") const;
  virtual PatternMatching *
  pattern_matching(const Formula *e, 
		   const std::list<const Variable *> &free_variables) const;
  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};

/*****************************************************************************/
/*! \brief
 *  Application of a unary operator to an expression.
 *  Operators are defined in kernel/expressions/Operators.hh
 *****************************************************************************/
class UnaryApp : public Expr {
private:
  /*! \brief The operator */
  UnaryOp op;

  /*! \brief The expression on which the operator is applied
   *  \caution arg1 belongs to the instance and in particular
   *  is deleted when the instance is deleted. arg1 should not
   *  be used by any other term, for this, it must be duplicated. */
  Expr *arg1;

  UnaryApp(UnaryOp op, Expr *arg1, int bv_offset, int bv_size);
  virtual ~UnaryApp();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static UnaryApp *create (UnaryOp op, Expr *arg1);
  static UnaryApp *create (UnaryOp op, Expr *arg1, int bv_offset, 
			   int bv_size = BV_DEFAULT_SIZE);

  UnaryOp get_op() const;
  Expr *get_arg1() const;

  /* See Expr class for documentation */
  std::string pp(std::string prefix = "") const;
  Expr *bottom_up_apply (TermReplacingRule *r, TopBottomInfo *top_bottom_info = NULL, BottomUpInfo **bottom_up_info = NULL) const;
  std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const;

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Formula *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Formula *F) const;

  bool contains(Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual PatternMatching *
  pattern_matching(const Formula *e, 
		   const std::list<const Variable *> &free_variables) const;
  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};

/*****************************************************************************/
/*! \brief
 *  Application of a binary operator to an expression.
 *  Operators are defined in kernel/expressions/Operators.hh
 *****************************************************************************/
class BinaryApp : public Expr {
private:
  /*! \brief The applied operator */
  BinaryOp op;

  /*! \brief The expressions on which the operator is applied
   *  \caution arg1 and arg2 belongs to the instance and in particular
   *  is deleted when the instance is deleted. arg1 and arg2 should not
   *  be used by any other term, for this, it must be duplicated. */
  Expr *arg1, *arg2;

  BinaryApp(BinaryOp op, Expr *arg1, Expr *arg2, int bv_offset, 
	    int bv_size);

  virtual ~BinaryApp();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static BinaryApp *create (BinaryOp op, Expr *arg1, Expr *arg2);
  static BinaryApp *create (BinaryOp op, Expr *arg1, int arg2);

  static BinaryApp *create (BinaryOp op, Expr *arg1, Expr *arg2, 
			    int bv_offset, int bv_size = BV_DEFAULT_SIZE);

  
  static BinaryApp *create (BinaryOp op, Expr *arg1, int arg2,
			    int bv_offset, int bv_size = BV_DEFAULT_SIZE);

  BinaryOp get_op() const;
  Expr *get_arg1() const;
  Expr *get_arg2() const;

  /* See Expr class for documentation */
  Expr *bottom_up_apply (TermReplacingRule *r, TopBottomInfo *top_bottom_info = NULL, BottomUpInfo **bottom_up_info = NULL) const;
  std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const;

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Formula *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Formula *F) const;

  bool contains(Expr *o) const;
  virtual unsigned int get_depth() const;
  std::string pp(std::string prefix = "") const;

  virtual PatternMatching *
  pattern_matching(const Formula *e, 
		   const std::list<const Variable *> &free_variables) const;
  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};



/******************************************************************************/
class TernaryApp: public Expr {

private:
  TernaryOp op;
  Expr *arg1, *arg2, *arg3;

  TernaryApp(TernaryOp op, Expr *arg1, Expr *arg2, Expr *arg3, int bv_offset,
      int bv_size);

  virtual ~TernaryApp();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static TernaryApp *create(TernaryOp op, Expr *arg1, Expr *arg2, Expr *arg3);

  static TernaryApp *create(TernaryOp op, Expr *arg1, Expr *arg2, Expr *arg3,
      int bv_offset, int bv_size = BV_DEFAULT_SIZE);
  Expr *get_arg1() const;
  Expr *get_arg2() const;
  Expr *get_arg3() const;
  TernaryOp get_op() const;

  virtual bool equal(const Formula *F) const;
  virtual size_t hash() const;
  virtual bool has_type_of(const Formula *F) const;

  bool contains(Expr *o) const;
  virtual unsigned int get_depth() const;
  std::string pp(std::string prefix = "") const;

  virtual PatternMatching *
  pattern_matching(const Formula *e,
      const std::list<const Variable *> &free_variables) const;

  /* See Expr class for documentation */
  Expr *bottom_up_apply(TermReplacingRule *r, TopBottomInfo *top_bottom_info =
      NULL, BottomUpInfo **bottom_up_info = NULL) const;
  std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const;

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};


/*****************************************************************************/
/*! \brief
 *  Left-values: define the modifiable expressions of the microcode language:
 *  memory cells and registers.
 *
 *  Note that like Expr class, the class LValue is abstract and thus can not be
 *  instanciated directly.
 *****************************************************************************/
class LValue : public Expr   /* Abstract class */ {
public:
  LValue(int bv_offset, int bv_size);
};

/*! \brief The tag identifies different address spaces */
typedef std::string Tag;
#define DEFAULT_TAG ""

/*****************************************************************************/
/*! \brief
 *  A memory cell is defined by a term indicating the address of the
 *  cell.
 *****************************************************************************/
class MemCell : public LValue {
private:
  /*!\brief The address of the cell. Note that the The effective
   *  transformation of the expression into a real address is in charge
   *  of the MicrocodeAddress class. */
  Expr *addr;

  /*! \brief The address space */
  Tag tag;

  MemCell(Expr *addr, Tag tag, int bv_offset, int bv_size);
  virtual ~MemCell();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static MemCell *create (Expr *addr, Tag tag, int bv_offset = 0, 
			  int bv_size = BV_DEFAULT_SIZE);
  static MemCell *create (Expr *addr, int bv_offset = 0, 
			  int bv_size = BV_DEFAULT_SIZE);

  /*! \brief The tag define the address space in which is defined the
      memory cell. */
  Tag get_tag() const;

  /*! \brief The address of the memory cell in the address space
      tag. */
  Expr *get_addr() const ;

  /* See Expr class for documentation */
  std::string pp(std::string prefix = "") const;
  Expr *bottom_up_apply (TermReplacingRule *r, TopBottomInfo *top_bottom_info = NULL, BottomUpInfo **bottom_up_info = NULL) const;
  std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const;

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Formula *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Formula *F) const;

  bool contains(Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual PatternMatching *
  pattern_matching(const Formula *e, 
		   const std::list<const Variable *> &free_variables) const;

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};

/*****************************************************************************/

/*****************************************************************************/
/*! \brief
 *  A register is uniquely defined by an integer index. It is supposed
 *  to contain a word.
 *
 * \todo replacer RegisterExpr par variable et variable par symbole.
 *****************************************************************************/
class RegisterExpr : public LValue {
private:
  const RegisterDesc *regdesc;

  RegisterExpr (const RegisterDesc *reg, int bv_offset, int bv_size);

  virtual ~RegisterExpr ();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:

  static RegisterExpr *create (const RegisterDesc *reg);
  static RegisterExpr *create (const RegisterDesc *reg, int bv_offset,
			       int bv_size);

  const RegisterDesc *get_descriptor () const;
  const std::string &get_name() const;

  /* See Expr class for documentation */
  Expr *bottom_up_apply (TermReplacingRule *r, TopBottomInfo *top_bottom_info = NULL, BottomUpInfo **bottom_up_info = NULL) const;
  std::list<Expr *> bottom_up_apply_nd(TermReplacingRuleNd *r) const;

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Formula *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Formula *F) const;

  bool contains(Expr *o) const;
  virtual unsigned int get_depth() const;

  std::string pp(std::string prefix = "") const;

  virtual PatternMatching *
  pattern_matching(const Formula *e, 
		   const std::list<const Variable *> &free_variables) const;

  virtual void acceptVisitor (FormulaVisitor *visitor);
  virtual void acceptVisitor (ConstFormulaVisitor *visitor) const;
};

/*****************************************************************************/
/*****************************************************************************/
/*! \brief
 *  This class encloses term transformation rules to be used
 *  with bottom_up_apply_in_place method.
 *  To be used, this class must be implemented. For example, look at
 *  ReplaceVariableRule class.
 *****************************************************************************/
class TermReplacingRule   /* abstract */ {
public:

  /*! \brief virtual destructor definition for abstract class */
  virtual ~TermReplacingRule() {};

  /*! \brief The replacement function. This is the crucial point to be
   *   implemented.
   *   f is supposed to receive the bottom-up information via the
   *   double pointer, and use it to transmit this information, modified as
   *   user want to next applications of f.
   *   Note that it is in charge to delete useless information.
   *   One should put NULL in the pointer to say that it is not used.
   *   This behaviour should be taken into account be the developer.
   *   TopBottomInfo carry some user information coming from the root
   *   of the term. Before calling f to a given node, the TopBottomInfo
   *   object has been run over all the expression from root by applying
   *   its push operation on it. */
  virtual Expr *f(const Expr *, TopBottomInfo *, BottomUpInfo **) = 0;
};
/*****************************************************************************/
/*! \brief
 *  This class encloses non-deterministic term transformation rules to be
 *  used with the method bottom_up_apply_nd.
 *  To be used, this class must be implemented. For example, look at
 *  ReplaceVariableRule class.
 *****************************************************************************/
class TermReplacingRuleNd /* abstract */ {
public:

  /*! \brief virtual destructor definition for abstract class */
  virtual ~TermReplacingRuleNd() {};

  /*! \brief The replacement function. This is the crucial point to be
   *   implemented. */
  virtual std::list<Expr *> f(const Expr *) = 0;
};

/*****************************************************************************/
/*! see bottom_up_apply_in_place above for documentation. */
class BottomUpInfo /* abstract */ {
public:
  virtual ~BottomUpInfo() {};

  /* make a new bottom up info by grouping the left and right information.
   * 'this' is supposed to be the left information. After execution, the
   * resulting info must be in 'this'.
   * Note that this is the charge of the user to reuse or to delete *right.
   * Note that the asymmetry of the implementation is the easiest way
   *      to design the mechanism in order to use inheritance instead of
   *      template. */
  virtual void group(BottomUpInfo *right) = 0;
};
/*****************************************************************************/
/*! see bottom_up_apply_in_place above for documentation. */
class TopBottomInfo /* abstract */ {
public:
  virtual ~TopBottomInfo() {};
  virtual TopBottomInfo *clone() const = 0;
  virtual void push(const Expr *) = 0;
};

std::ostream &operator<< (std::ostream &o, Expr &e);

#endif /* KERNEL_EXPRESSIONS_HH */

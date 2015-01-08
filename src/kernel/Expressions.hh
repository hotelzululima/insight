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
#ifndef KERNEL_EXPRESSIONS_HH
#define KERNEL_EXPRESSIONS_HH

#include <string>

#include <kernel/microcode/MicrocodeArchitecture.hh>
#include <kernel/expressions/Operators.hh>
#include <utils/Option.hh>
#include <utils/ConfigTable.hh>
#include <utils/unordered11.hh>

class ExprVisitor;
class ConstExprVisitor;

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
class QuantifiedExpr;   // --> LValue
// class BitIntLVal; // --> LValue (template)
/*****************************************************************************/

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
class Expr : public Object {
private:

  /*! \brief The value of each expression is restricted to a
    particular bit vector. This is an interval of bits the index of
    the first one being bv_offset. */
  int bv_offset;

  /*! \brief The size in bit of the interval of bits. */
  int bv_size;

  /*! \brief The default size in bits of a vector (default is 32). */
  static int bv_default_size;

  /*****************************************************************************/


protected:
  /*! \brief Default constructor. Caution, this is an abstract class,
   *  it is called by inherited constructor explicitely */
  Expr(int bv_offset, int bv_size);

  virtual ~Expr();

public:
  static const std::string NON_EMPTY_STORE_ABORT_PROP;

  static void init (const ConfigTable &cfg);
  static void terminate ();

  virtual void acceptVisitor (ExprVisitor &visitor);
  virtual void acceptVisitor (ConstExprVisitor &visitor) const;
  virtual void acceptVisitor (ExprVisitor *visitor) = 0;
  virtual void acceptVisitor (ConstExprVisitor *visitor) const = 0;

  virtual size_t hash () const;
  virtual bool equal (const Expr *F) const = 0;

  static Expr *createLNot (Expr *arg);

  static Expr *createLAnd (Expr *arg1, Expr *arg2);

  static Expr *createLOr (Expr *arg1, Expr *arg2);

  /*! \brief construct the expr A ==> B.
   *  Caution A and B are not copied */
  static Expr *createImplies (Expr *A, Expr *B);

  /*! \brief construct the expr (cond /\ A) \/ ((Not cont) /\ B).
   *  Caution A and B are not copied */
  static Expr *createIfThenElse (Expr *cond, Expr *A, Expr *B);

  /*! \brief construct the expr, actually the expression (EQ A B).
   *  Caution A and B are not copied */
  static Expr *createEquality (Expr *A, Expr *B);
  static Expr *createDisequality (Expr *A, Expr *B);

  static Expr *createExtend (BinaryOp op, Expr *A, int newsize);
  static Expr *createExtract (Expr *A, int offset, int size);
  static Expr *createConcat (Expr *A, Expr *B);

  /*! \brief Set the default size of the bitvectors for an expression. */
  static void set_bv_default_size(int);

  /*! \brief Get the default size for an expression. */
  static int get_bv_default_size();

  /*! \brief The size of the bit vector. */
  int get_bv_size() const;

  /*! \brief The index of the first bit of the bit vector. */
  int get_bv_offset() const;

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

  /*! \brief simple syntaxic evaluation: try to transform a true
   *   expr into a bool. */
  Option<bool> try_eval_level0() const;

  /*! \brief return true iff the expr can be reduce to true. */
  bool eval_level0() const;

  /***************************************************************************/
  // Type checking
  /***************************************************************************/

  bool is_Variable() const;
  bool is_Constant() const;
  bool is_RandomValue() const;
  bool is_UnaryApp() const;
  bool is_BinaryApp() const;
  bool is_TernaryApp() const;
  bool is_LValue() const;
  bool is_MemCell() const;
  bool is_RegisterExpr() const;

  bool is_DisjunctiveFormula () const;
  bool is_ConjunctiveFormula () const;
  bool is_NegationFormula () const;
  bool is_QuantifiedFormula () const;
  bool is_ExistentialFormula () const;
  bool is_UniversalFormula () const;
  bool is_TrueFormula () const;
  bool is_FalseFormula () const;


  virtual bool has_type_of (const Expr *F) const = 0;

  /***************************************************************************/
  // Basic Queries
  /***************************************************************************/

  /*! \brief true if o is a sub-expression of this expression */
  virtual bool contains(const Expr *o) const = 0;

  /*! \brief return the depth of the expression as a tree (or a term) */
  virtual unsigned int get_depth() const = 0;

  /***************************************************************************/
  // Pretty printing
  /***************************************************************************/

  virtual void output_text (std::ostream &out) const;

  struct Hash {
    size_t operator()(const Expr *const &F) const;
  };

  struct Equal {
    bool operator()(const Expr *const &F1, const Expr * const &F2) const;
  };

  Expr *ref () const;

  void deref ();


protected:

  static Expr *find_or_add_expr (Expr *F);

  template<typename C>
  static C *find_or_add (C *F) {
    Expr *res = find_or_add_expr (F);
    return dynamic_cast<C *> (res);
  }

private:
  typedef std::unordered_set<Expr *, Expr::Hash, Expr::Equal> ExprStore;

  static ExprStore *expr_store;
  static bool non_empty_store_abort;
  static void dumpStore ();
  mutable int refcount;
};

/***************************************************************************/
/*! \brief
 *  General use Symbols
 *
 *  They are not element of the microcode language.
 *  Variables are used for term operations. A variable is just
 *  a leaf defined by an identifier (a string). They can be used to define
 *  parameters of some piece of code for instance, or of a logical expr.
 ***************************************************************************/
class Variable : public Expr {
private:
  /*! A Variable is defined by a string identifier */
  std::string id;
  size_in_bits_t size;

  Variable(const std::string &id, size_in_bits_t size,
	   int bv_offset, int bv_size);

  virtual ~Variable();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static Variable *create (const std::string &id, size_in_bits_t size);

  size_in_bits_t get_size () const;
  std::string get_id() const;


  /*! \brief syntactic equality of variables */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool operator<(const Variable &other) const;  /* needed for using variables as key of maps */
  virtual unsigned int get_depth() const;
  bool contains(const Expr *o) const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

/***************************************************************************/
/*! \brief
 *  Encoding of concrete word values.
 ***************************************************************************/
class Constant : public Expr {
private:
  constant_t val;

  Constant(constant_t v, int bv_offset, int bv_size);
  virtual ~Constant();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:

  static inline Constant *True () { return one (1); }
  static inline Constant *False () { return zero (1); }

  static inline Constant *zero (int size) { return create (0, 0, size); }
  static inline Constant *one (int size) { return create (1, 0, size); }

  static Constant *create (constant_t v, int bv_offset, int bv_size);

  constant_t get_val() const;
  constant_t get_not_truncated_value() const;

  /*! \brief syntactic equality of registers */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

class RandomValue : public Expr {
private:
  RandomValue (int bv_size);
  virtual ~RandomValue();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static RandomValue *create (int bv_size);

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

/***************************************************************************/
/*! \brief
 *  Application of a unary operator to an expression.
 *  Operators are defined in kernel/expressions/Operators.hh
 ***************************************************************************/
class UnaryApp : public Expr {
private:
  /*! \brief The operator */
  UnaryOp op;

  /*! \brief The expression on which the operator is applied
   *
   *  \warning arg1 belongs to the instance and in particular
   *  is deleted when the instance is deleted. arg1 should not
   *  be used by any other term, for this, it must be duplicated. */
  Expr *arg1;

  UnaryApp(UnaryOp op, Expr *arg1, int bv_offset, int bv_size);
  virtual ~UnaryApp();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static UnaryApp *create (UnaryOp op, Expr *arg1);
  static UnaryApp *create (UnaryOp op, Expr *arg1,
			   int bv_offset, int bv_size);

  UnaryOp get_op() const;
  Expr *get_arg1() const;

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

/***************************************************************************/
/*! \brief
 *  Application of a binary operator to an expression.
 *  Operators are defined in kernel/expressions/Operators.hh
 ***************************************************************************/
class BinaryApp : public Expr {
private:
  /*! \brief The applied operator */
  BinaryOp op;

  /*! \brief The expressions on which the operator is applied
   *
   *  \warning arg1 and arg2 belongs to the instance and in particular
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
			    int bv_offset, int bv_size);
  static BinaryApp *create (BinaryOp op, Expr *arg1, int arg2,
			    int bv_offset, int bv_size);

  BinaryOp get_op() const;
  Expr *get_arg1() const;
  Expr *get_arg2() const;


  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

/****************************************************************************/
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
  static TernaryApp *create(TernaryOp op,
			    Expr *arg1, Expr *arg2, Expr *arg3);

  static TernaryApp *create(TernaryOp op,
			    Expr *arg1, Expr *arg2, Expr *arg3,
			    int bv_offset, int bv_size);
  Expr *get_arg1() const;
  Expr *get_arg2() const;
  Expr *get_arg3() const;
  TernaryOp get_op() const;

  virtual bool equal(const Expr *F) const;
  virtual size_t hash() const;
  virtual bool has_type_of(const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

class QuantifiedExpr : public Expr {
private:
  bool exists;
  Variable *var;
  Expr *body;

  QuantifiedExpr (bool exist, Variable *var, Expr *body);

  virtual ~QuantifiedExpr();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:
  static QuantifiedExpr *create (bool exist, Variable *var, Expr *body);
  static QuantifiedExpr *createExists (Variable *var, Expr *body);
  static QuantifiedExpr *createForall (Variable *var, Expr *body);

  virtual bool is_exists () const;
  virtual Variable *get_variable () const;
  virtual Expr *get_body () const;


  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};


/***************************************************************************/
/*! \brief
 *  Left-values: define the modifiable expressions of the microcode language:
 *  memory cells and registers.
 *
 *  Note that like Expr class, the class LValue is abstract and thus can not be
 *  instanciated directly.
 ***************************************************************************/
class LValue : public Expr   /* Abstract class */ {
public:
  LValue(int bv_offset, int bv_size);
  virtual LValue *ref () const { return (LValue *) Expr::ref (); }

};

/*! \brief The tag identifies different address spaces */
typedef std::string Tag;
#define DEFAULT_TAG ""

/***************************************************************************/
/*! \brief
 *  A memory cell is defined by a term indicating the address of the
 *  cell.
 ***************************************************************************/
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
  static MemCell *create (Expr *addr, Tag tag, int bv_offset,
			  int bv_size);
  static MemCell *create (Expr *addr, int bv_offset,
			  int bv_size);

  /*! \brief The tag define the address space in which is defined the
      memory cell. */
  Tag get_tag() const;

  /*! \brief The address of the memory cell in the address space
      tag. */
  Expr *get_addr() const ;

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

/***************************************************************************/

/***************************************************************************/
/*! \brief
 *  A register is uniquely defined by an integer index. It is supposed
 *  to contain a word.
 *
 * \todo replace RegisterExpr by variable and variable by symbol.
 ***************************************************************************/
class RegisterExpr : public LValue {
private:
  RegisterDesc *regdesc;

  RegisterExpr (RegisterDesc *reg, int bv_offset, int bv_size);

  virtual ~RegisterExpr ();

protected:
  virtual Expr *change_bit_vector (int new_bv_offset, int new_bv_size) const;

public:

  static RegisterExpr *create (RegisterDesc *reg);
  static RegisterExpr *create (RegisterDesc *reg, int bv_offset,
			       int bv_size);

  RegisterDesc *get_descriptor () const;
  const std::string &get_name() const;

  /*! \brief syntaxic equality of registers */
  virtual bool equal (const Expr *F) const;
  virtual size_t hash () const;
  virtual bool has_type_of (const Expr *F) const;

  bool contains(const Expr *o) const;
  virtual unsigned int get_depth() const;

  virtual void acceptVisitor (ExprVisitor *visitor);
  virtual void acceptVisitor (ConstExprVisitor *visitor) const;
};

#endif /* KERNEL_EXPRESSIONS_HH */

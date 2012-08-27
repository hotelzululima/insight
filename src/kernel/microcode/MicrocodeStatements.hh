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

#ifndef KERNEL_MICROCODE_MICROCODE_STATEMENTS_HH
#define KERNEL_MICROCODE_MICROCODE_STATEMENTS_HH

#include <vector>
#include <kernel/Expressions.hh>

/*****************************************************************************/
/*! \brief This class define the framework for statements. All
 *  statements must inherit of it. MicrocodeNode are:
 *   - Assignment (lvalue := expression)
 *   - Skip (for jump and conditionnal jump)
 *****************************************************************************/
class Statement { /* Abstract */

public:
  Statement();
  Statement(const Statement &);
  virtual ~Statement();
  virtual Statement * clone() const = 0;

  bool is_Assignment();
  bool is_Skip();
  bool is_Jump();
  bool is_External();

  bool equal(Statement * other); // \todo remove
  static bool equal(Statement * s1, Statement * s2); // \todo equals ...

  /*!\brief construct the list of all the expressions present in the
   * statement, this includes expressions used in arrows.
   * \return a vector containing pointers on pointers to expression.
   * This allows to modify the expressions. */
  virtual std::vector<Expr **>* expr_list() = 0;

  virtual std::string pp() = 0;
};

/*****************************************************************************/
/*! \brief This class defines assignments.
 *  Assignment defines an l-value and an expression.
 *****************************************************************************/
class Assignment : public Statement {

private:
  LValue * lval;
  Expr * rval;

/*****************************************************************************/
public:
  Assignment(LValue *lv, Expr *v);
  Assignment(const Assignment &as);
  virtual ~Assignment();
  Statement *clone() const;

  const LValue * get_lval() const;
  void set_lval(LValue *lv);
  const Expr * get_rval() const;
  void set_rval(LValue *rv);

  std::string pp();
  std::vector<Expr **>* expr_list();
};

/*****************************************************************************/
/*! \brief The skip statement is defined here. Skip statement does
 *  nothing, however it is needed to maintain the consistancy of code
 *  addresses.
 *****************************************************************************/
class Skip : public Statement {
public:
  Skip();
  Skip(const Skip &);
  ~Skip();
  Statement *clone() const;
  std::string pp();
  std::vector<Expr **>* expr_list();
};

/*****************************************************************************/

class Jump : public Statement {
private:
  Expr * target;

public:
  Jump(Expr *target);
  Jump(const Jump &jp);
  ~Jump();

  Expr * get_target();
  std::vector<Expr **>* expr_list();
  Statement *clone() const;
  std::string pp();
};

/*****************************************************************************/

class External : public Statement {
private:
  std::string id;

public:
  External(std::string id);
  External(const External &bb);
  ~External();
  std::string get_id();

  Statement *clone() const;
  std::string pp();
  std::vector<Expr **>* expr_list();
};

#endif /* KERNEL_MICROCODE_MICROCODE_STATEMENTS_HH */

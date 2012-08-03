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

#ifndef PATTERNMATCHING_HH
#define PATTERNMATCHING_HH

#include <iostream>
#include <kernel/Expressions.hh>

class PatternMatching :  public Object
{
public:
  typedef std::tr1::unordered_map<const Variable *, Expr *,
			     Formula::Hash, Formula::Equal> Matching;
  typedef std::list<const Variable *> VarList;
  typedef Matching::const_iterator const_iterator;

  class Failure { };

  PatternMatching ();
  virtual ~PatternMatching ();

  virtual void merge (const PatternMatching *other);
  virtual const Expr *get (const Variable *v) const;
  virtual bool has (const Variable *v) const;
  virtual void set (const Variable *v, Expr *F);
  virtual void output_text (std::ostream &out) const;

  virtual const_iterator begin() const;
  virtual const_iterator end() const;

  virtual bool equal (const PatternMatching *other) const;

  static PatternMatching *match (const Expr *F,
				 const Expr *pattern, 
				 const VarList &free_variables)
    throw (Failure);
				 
private:
  typedef Matching::iterator iterator;
  Matching matching;
};

#endif /* PATTERNMATCHING_HH */

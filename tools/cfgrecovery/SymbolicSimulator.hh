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
#ifndef SYMBOLICSIMULATOR_HH
#define SYMBOLICSIMULATOR_HH

#include <list>
#include <decoders/Decoder.hh>
#include <kernel/Microcode.hh>
#include "SymbolicState.hh"

class SymbolicSimulator 
{
public:
  typedef std::list<StmtArrow *> ArrowSet;

  SymbolicSimulator (const ConcreteMemory *base, Decoder *dec, 
		     Microcode *prog);

  virtual ~SymbolicSimulator();

  virtual SymbolicState *init (const ConcreteAddress &entrypoint);
  
  virtual ArrowSet get_arrows (const SymbolicState *ctx) const
    throw (Decoder::Exception);

  virtual std::vector<SymbolicState *> *
  step (const SymbolicState *ctx, const StmtArrow *arrow);

  virtual MicrocodeNode *get_node (const MicrocodeAddress &pp) const
    throw (Decoder::Exception);

  virtual const Microcode *get_program () const;

private:
  SymbolicValue eval (const SymbolicState *ctx, const Expr *e) const;
  std::vector<address_t> * 
  eval_to_addresses (const SymbolicState *ctx, const Expr *e) const;

  void exec (SymbolicState *ctxt, const Statement *st, 
	     const MicrocodeAddress &tgt) const;

  void step (SymbolicState *ctxt, const StaticArrow *sa,
	     std::vector<SymbolicState *> *new_states);
  void step (SymbolicState *ctxt, const DynamicArrow *d, 
	     std::vector<SymbolicState *> *new_states);

  Option<bool> to_bool (const SymbolicState *ctx, const Expr *e, 
			Expr **symbval = NULL) const;
  SymbolicState *check_guard (const SymbolicState *ctx, const Expr *cond) const;
  SymbolicValue simplify (const SymbolicState *ctx, const Expr *e) const;

  const ConcreteMemory *base;  
  Decoder *decoder;

  class ExprSolver *solver;
  Microcode *program;
  const Architecture *arch;

  class StateSpace;
  class StateSpace *states;

  Expr *regexpr (const char *s);
};

#endif /* SYMBOLICSIMULATOR_HH */

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

#include <iomanip>
#include <iostream>
#include <stdexcept>

#include <analyses/microcode_exec.hh>
#include <analyses/slicing/Slicing.hh>
#include <domains/ExprSemantics.hh>
#include <domains/concrete/ConcreteExprSemantics.hh>
#include <domains/concrete/concrete_context.hh>
#include <io/binary/BinutilsBinaryLoader.hh>
#include <io/expressions/expr-parser.hh>
#include <kernel/insight.hh>
#include <kernel/Microcode.hh>
#include <utils/Log.hh>

using namespace std;

static void 
test_slicing (const char *filename, int max_step_nb, int target_addr, 
	      const string &target_lv)
{
  log::display << "*** Test of slicing algorithm ***" << endl
       << endl
       << "max number of steps: " << max_step_nb << endl
       << "targeted address: " << target_addr << endl
       << "lvalue: " << target_lv << endl
       << endl;
  
  BinaryLoader *loader = new BinutilsBinaryLoader (filename);
  MicrocodeArchitecture *mcarch = 
    new MicrocodeArchitecture (loader->get_architecture ());
  ConcreteMemory *mem = loader->get_memory ();
  Microcode *prg = Build_Microcode (mcarch, mem, ConcreteAddress (0));
  
  Expr *lvalue = expr_parser (target_lv, mcarch);
  vector<StmtArrow*> stmt_deps =
    DataDependency::slice_it (prg, MicrocodeAddress (target_addr), lvalue);
  
  for (int i = 0; i < (int) stmt_deps.size (); i++)
    log::display  << stmt_deps[i]->pp() << endl;
  log::display << endl;

  lvalue->deref ();

  log::display << "* Useless statements:" << endl;

  std::vector<StmtArrow*> useless_arrows = 
    DataDependency::useless_statements (prg);
  for (int i = 0; i < (int) useless_arrows.size (); i++)
    log::display << useless_arrows[i]->pp() << endl;
  log::display << endl;

  /* TO BE KEPT : For high-precision computation of dependency path
  DataDependency invfix(prg_cpy, seeds);

  invfix.ComputeFixpoint(max_step_nb);

  Formula * deps = invfix.get_dependencies(ConcreteProgramPoint(0), 0);
  log::display << "RESULT:" << deps->pp() << endl;
  deps->deref ();
  log::display << "SIMPLIFIED:" ;
  log::emph ("{ ", 2);
  std::vector<Expr*> upper_set = invfix.get_simple_dependencies(ConcreteProgramPoint(0), 0);
  for (int i=0; i<(int) upper_set.size(); i++) {
    log::emph (upper_set[i]->pp() + " ", 2);
    upper_set[i]->deref ();
  }
  log::emph (" }\n", 2);
  delete prg_cpy;
  for (list<LocatedLValue>::iterator i = seeds.begin(); i != seeds.end(); i++)
    {
      (*i).lv->deref ();
    }
  */

  delete prg;
  delete mcarch;
  delete mem;
  delete loader;
}

int main(int argc, char **argv)
{
  if (argc != 5)
    {
      cerr << "wrong # of arguments" << endl
	   << endl
	   << "USAGE: " << argv[0] << " inputfile max-step addr lvalue" << endl;
      exit (EXIT_FAILURE);
    }
  ConfigTable ct;
  ct.set (log::DEBUG_ENABLED_PROP, true);
  ct.set (log::STDIO_ENABLED_PROP, true);
  ct.set (Expr::NON_EMPTY_STORE_ABORT_PROP, true);

  insight::init (ct);
  {
    DataDependency::ConsiderJumpCondMode(true);
    DataDependency::OnlySimpleSetsMode(true);
    
    test_slicing(argv[1], atoi(argv[2]), strtol(argv[3],0,0), argv[4]);
    log::display << endl;
  }
  insight::terminate ();

  return EXIT_SUCCESS;
}

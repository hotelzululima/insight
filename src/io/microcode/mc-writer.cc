/*
 * Copyright (c) 2010-2014, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite de Bordeaux.
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "mc-writer.hh"

#include <set>
#include <sstream>
#include <cassert>
#include <cstring>
#include <cstdio>
#include <list>
#include <algorithm>

#include <kernel/annotations/NextInstAnnotation.hh>
#include <kernel/annotations/AsmAnnotation.hh>
#include <kernel/annotations/SolvedJmpAnnotation.hh>
#include <utils/unordered11.hh>

using namespace std;

static bool
s_sort_microcode (const MicrocodeNode *e1, const MicrocodeNode *e2)
{
  return (*e1) < (*e2);
}

static void
s_mc_writer (ostream &out, vector<MicrocodeNode *> nodes)
{
  for (unsigned int i = 0; i < nodes.size (); i++)
    {
      out << nodes.at (i)->pp() << endl;
    }
}

void
mc_writer (ostream &out, const Microcode *mc)
{
  vector<MicrocodeNode *> nodes (mc->get_number_of_nodes ());
  std::copy (mc->begin_nodes(), mc->end_nodes (), nodes.begin ());
  if (nodes.empty ())
    return;
  std::sort (nodes.begin (), nodes.end (), s_sort_microcode);

  s_mc_writer (out, nodes);
}

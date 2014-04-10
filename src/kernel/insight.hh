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

#ifndef KERNEL_INSIGHT_HH
#define KERNEL_INSIGHT_HH

# include <utils/ConfigTable.hh>

/*!
 * \mainpage The Insight Project
 *
 * The Insight project is devoted to binary analysis to serve several
 * purposes such as:
 *
 *   \li Binary verification
 *   \li Reverse engineering
 *   \li Binary test cases extraction
 *   \li Decompilation to higher-level languages
 *
 * We aim to have a full and efficient platform to easily try out
 * novel algorithms or techniques. For this, we provide a full C++
 * framework designed for Unix systems (*BSD, Linux, MacOS X, ...)
 * which contains a wide-spectrum binary format loaders (ELF, PE,
 * Mach-O, ...), a decoder translating from assembly code (x86-32 and
 * ARM for now others will come) into our intermediate language, an
 * interpreter to execute the program over a (potentially abstract)
 * domain and several facilities to simplify, manipulate or transform
 * the graph and the expressions extracted from the original program.
 *
 * \b Warning: The insight framework is still not feature complete and
 * is a work in progress. Yet, one can try the tool cfgrecovery in
 * \c insight/tools/cfgrecovery/ directory once you have compiled
 * everything.
 */

namespace insight
{
  void init (const ConfigTable &cfg = ConfigTable ());

  void terminate();
}

#endif /* KERNEL_INSIGHT_HH */

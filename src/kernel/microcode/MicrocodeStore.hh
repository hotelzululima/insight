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
#ifndef KERNEL_MICROCODE_MICROCODE_STORE_HH
#define KERNEL_MICROCODE_MICROCODE_STORE_HH

#include "kernel/microcode/MicrocodeAddress.hh"
#include "kernel/microcode/MicrocodeNode.hh"

/*****************************************************************************
 * \brief The microcode interface is the view for interpretation. It
 *   can be implemented in several ways:
 *   - from a program.
 *   - from the decoder itself plugged on the concrete memory.
 *****************************************************************************/
class MicrocodeStore   /* abstract */
{

public:
  virtual ~MicrocodeStore() {};

  /*! \brief try to retrieve the node at address addr, throw
      GetNodeNotFoundExc if there is no node at this address. */
  virtual MicrocodeNode *get_node(MicrocodeAddress addr) const = 0;

  /*! \brief the entry point of the program */
  virtual MicrocodeAddress entry_point() = 0 ;
};

#endif /* KERNEL_MICROCODE_MICROCODE_STORE_HH */

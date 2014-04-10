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

#include <config.h>

#include <bfd.h>

#include <list>

#include "DecoderFactory.hh"

#include <decoders/Decoder.hh>
#include <decoders/binutils/BinutilsDecoder.hh>

using namespace std;

Decoder *DecoderFactory::get_Decoder(MicrocodeArchitecture *arch,
                                     ConcreteMemory *mem)
{
  Decoder *decoder = new BinutilsDecoder(arch, mem);

  return decoder;
}

/* Check if supported architectures are really available from local
 * installation of binutils and returns a list of it. */
list<string> *get_BinutilsDecoder_supported_architectures()
{
  /* NOTE: It is of no use for now, but listing all the available
   * architectures from the local binutils libraries is done by
   * calling bfd_arch_list():
   *
   * const char **targets = bfd_arch_list();
   * list<string> *archs = new list<string>();
   *
   *  for (int i = 0; targets[i] != NULL; i++)
   *    archs->push_back(string(targets[i]));
   *
   * Of course, this list of supported architectures is much wider
   * than ours and it is of no use to display it to the user. So, we
   * are only checking if each item of our short list is here through
   * a call to bfd_scan_arch("arch").
   */

  list<string> *architectures = new list<string>();

  /* Checking for arm architecture support */
  if (bfd_scan_arch("arm") != NULL)
    architectures->push_back("arm");
  else
    architectures->push_back("arm: warning support not found in binutils!");

  /* Checking for sparc architecture support */
  if (bfd_scan_arch("sparc") != NULL)
    architectures->push_back("sparc");
  else
    architectures->push_back("sparc: warning support not found in binutils!");

  /* Checking for x86-32 architecture support */
  /* NOTE: "i386" is the binutils' label for x86-32 */
  if (bfd_scan_arch("i386") != NULL)
    architectures->push_back("x86-32");
  else
    architectures->push_back("x86-32: warning: support not found in binutils!");

  /* Checking for x86-64 architecture support */
  /* NOTE: "i386:x86-64" is the binutils' label for x86-64 */
  if (bfd_scan_arch("i386:x86-64") != NULL)
    architectures->push_back("x86-64");
  else
    architectures->push_back("x86-64: warning: support not found in binutils!");

  return architectures;
}

list<string> *DecoderFactory::get_Decoder_supported_architectures()
{
  return get_BinutilsDecoder_supported_architectures();
}

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

#ifndef LOADERS_PROCESSLOADER_HH
#define LOADERS_PROCESSLOADER_HH

#include <unistd.h>
#include <stdexcept>

#include <domains/concrete/ConcreteAddress.hh>
#include <domains/concrete/ConcreteMemory.hh>

#include <utils/tools.hh>

/******************** ProcessLoader Exceptions ***********************/

/* Thrown when the pid do not correspond to a valid process. */
class ProcessNotFound : public std::runtime_error
{
public:
  ProcessNotFound(pid_t pid) :
    std::runtime_error("'" + itos(pid) + "' : Process not found") { };
};

/* Thrown when user has no sufficient rights to attach to the process. */
class ProcessPermissionDenied : public std::runtime_error
{
public:
  ProcessPermissionDenied(pid_t pid) :
    std::runtime_error("'" + itos(pid) + "' : Permission denied") { };
};

/* Thrown when the target architecture is not recognized. */
class UnknownArch : public std::runtime_error
{
public:
  UnknownArch(pid_t pid) :
    std::runtime_error("'" + itos(pid) +
                       "': Architecture is not recognized") { };
};

/***************** ProcessLoader class definition ********************/

/* Pure abstract class to group all the process loader implementations.
 * This class is intended to load any process into the analyzer.
 *
 * As defined in the Loader class, the initialization of a 'Loader' is
 * done through a call to the static method 'getLoader(pid_t)' which
 * will issue an appropriate Loader for this process. */

class ProcessLoader
{
public:
  virtual ~ProcessLoader() { };

  /* Note that the interface of this abstract class also requires an
   * implementation of the 'getLoader' method in order to issue an
   * adequate Loader:
   * static ProcessLoader *getProcessLoader(pid_t pid); */

  pid_t get_pid();
  std::string get_architecture();

  virtual ConcreteMemory get_memory() = 0;

protected:
  virtual void set_architecture(std::string arch) = 0;

  pid_t pid;
  std::string architecture;
};

#endif /* LOADERS_PROCESSLOADER_HH */

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
#ifndef UTILS_LOG_HH
#define UTILS_LOG_HH

#include <set>
#include <kernel/Architecture.hh>

#include "config.h"

class Log
{
public:

  class Listener {
  public:
    virtual ~Listener () { }
    virtual void fatal_error (std::string) { }

    virtual void error (std::string, int) { }
    virtual void warning (std::string, int) { }
    virtual void print (std::string, int) { } 
    virtual void separator (int) { } 
    virtual void emph (std::string, int) { }
  };

  static Listener *STD_STREAM_LOG;

  static void add_listener (Listener *listener, bool once = true);
  static void remove_listener (Listener *listener);

  static void set_verbose_level (int level);
  static void fatal_error (std::string msg) NORETURN;
  static void check (std::string msg, bool cond);

  static void error (std::string msg, int verbose = 0);
  static void errorln (std::string msg, int verbose = 0);

  static void warning (std::string msg, int verbose = 0);
  static void warningln (std::string msg, int verbose = 0);

  static void print (std::string msg, int verbose = 0);
  static void println (std::string msg, int verbose = 0);

  static void emph (std::string str, int verbose = 0);
  static void emphln (std::string str, int verbose = 0);

  static void separator (int verbose = 0);

private:
  typedef std::multiset<Listener *> listener_set;
  typedef listener_set::iterator listener_iterator; 

  static listener_set listeners;

  static int verbose_level;  
};

#endif /* ! UTILS_LOG_HH */

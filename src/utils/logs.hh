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
#ifndef UTILS_LOGS_HH
#define UTILS_LOGS_HH

# include <iostream>
# include <utils/ConfigTable.hh>
# include <config.h>

namespace logs 
{
  class Listener {
  public:
    virtual ~Listener () { }
    virtual void error (const std::string &) { }
    virtual void warning (const std::string &) { }
    virtual void display (const std::string &) { } 
    virtual void debug (const std::string &, int) { } 
  };


  extern bool debug_is_on;
  
  extern std::string DEBUG_ENABLED_PROP;
  extern std::string STDIO_ENABLED_PROP;
  extern std::string STDIO_ENABLE_WARNINGS_PROP;
  extern std::string STDIO_DEBUG_IS_CERR_PROP;
  extern std::string STDIO_DEBUG_MAXLEVEL_PROP;
  extern std::string STDIO_DEBUG_TABSIZE_PROP;

  /*
   * Configuration properties:
   * logs.stdio.enabled:
   *   if true then a default listener based on standard streams is set using
   *   add_listener.
   * 
   * logs.stdio.enable-warnings:
   *   if true then warning message are displayed.
   *
   * logs.debug.enabled:
   *   debug_is_on variable is assign the value of this property
   *
   * logs.stdio.debug.is_cerr:
   *   if true then std::cerr stream is used for the debug stream instead of 
   *   std::cout.
   * 
   * logs.stdio.debug.maxlevel:
   *   set the maximal output level for debug stream; if the maxlevel is not 
   *   set or is negative then no limit is positioned.
   */
  extern void init (const ConfigTable &cfg);
  extern void terminate ();

  extern void add_listener (Listener *listener, bool once = true);
  extern void remove_listener (Listener *listener);

  extern void inc_debug_level ();
  extern void dec_debug_level ();

  extern void start_debug_block (const std::string &msg);
  extern void end_debug_block ();

  extern void fatal_error (const std::string &msg) NORETURN; // for compat
  extern void check (const std::string &msg, bool cond); // for compat
  extern const std::string separator;

  extern std::ostream error;
  extern std::ostream warning;
  extern std::ostream display;
  extern std::ostream debug;
}

# define BEGIN_DBG_BLOCK(_m)						\
  do { if (logs::debug_is_on) logs::start_debug_block (_m); } while (0)

# define END_DBG_BLOCK() \
  do { if (logs::debug_is_on) logs::end_debug_block (); } while (0)

#endif /* ! UTILS_LOGS_HH */

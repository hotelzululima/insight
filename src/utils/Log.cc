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

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <unistd.h>

#include "Log.hh"

using namespace std;

class StdStreamListener : public Log::Listener
{
  void fatal_error (std::string msg) { 
    cerr << "FATAL ERROR : " << msg << endl;
  }

  void error (std::string msg, int) { 
    cerr << msg;
  }

  void warning (std::string msg, int verbose) { 
    cout << "LOG["<< verbose << "]: " << msg << endl;
    cout.flush ();
  }

  void print (std::string msg, int) { 
    cout << msg;
    cout.flush ();    
  } 

  void separator (int) { 
    cout << string (80, '=') << endl;
    cout.flush ();
  } 

  void emph (std::string str, int) { 
    if (isatty(1))
      cout << "\033[32m" << str << "\033[0m";
    else
      cout << str;
    cout.flush ();
  }
};

			/* --------------- */

Log::listener_set Log::listeners;

int Log::verbose_level = 1;

Log::Listener *Log::STD_STREAM_LOG = new StdStreamListener;

			/* --------------- */

void 
Log::add_listener (Listener *listener, bool once)
{
  assert (listener != NULL);
  if (listeners.find (listener) != listeners.end () && once)
    return;

  listeners.insert (listener);
}

void 
Log::remove_listener (Listener *listener)
{
  assert (listener != NULL);
  listeners.erase (listener);
}

void 
Log::set_verbose_level (int level)
{
  verbose_level = level;
}

void 
Log::fatal_error (std::string msg) 
{
  for (listener_iterator i = listeners.begin (); i != listeners.end (); i++)
    (*i)->fatal_error (msg);
  abort ();
}

void 
Log::check (std::string msg, bool cond)
{
  if (cond) 
    return;
  fatal_error (string ("ASSERTION FAILED") + msg);
}

void 
Log::error (std::string msg, int verbose)
{
  if (verbose_level < verbose) 
    return;

  for (listener_iterator i = listeners.begin (); i != listeners.end (); i++)
    (*i)->error  (msg, verbose);
}

void 
Log::errorln (std::string msg, int verbose)
{
  error (msg + "\n", verbose);
}


void 
Log::warning (std::string msg, int verbose)
{
  if (verbose_level < verbose) 
    return;

  for (listener_iterator i = listeners.begin (); i != listeners.end (); i++)
    (*i)->warning  (msg, verbose);
}

void 
Log::warningln (std::string msg, int verbose)
{
  warning (msg + "\n", verbose);
}

void 
Log::print (std::string msg, int verbose)
{
  if (verbose_level < verbose) 
    return;

  for (listener_iterator i = listeners.begin (); i != listeners.end (); i++)
    (*i)->print (msg, verbose);
}

void 
Log::println (std::string msg, int verbose)
{
  print (msg + "\n", verbose);
}

void 
Log::emph (std::string str, int verbose)
{
  if (verbose_level < verbose) 
    return;

  for (listener_iterator i = listeners.begin (); i != listeners.end (); i++)
    (*i)->emph (str, verbose);
}

void 
Log::emphln (std::string str, int verbose)
{
  emph (str + "\n", verbose);
}

void 
Log::separator(int verbose)
{
  if (verbose_level < verbose) 
    return;

  for (listener_iterator i = listeners.begin (); i != listeners.end (); i++)
    (*i)->separator (verbose);
}


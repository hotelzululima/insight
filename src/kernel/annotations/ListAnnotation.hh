/*
 * Copyright (c) 2010-2013, Centre National de la Recherche Scientifique,
 *                          Institut Polytechnique de Bordeaux,
 *                          Universite Bordeaux 1.
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
#ifndef LISTANNOTATION_HH
# define LISTANNOTATION_HH

# include <algorithm>
# include <list>
# include <kernel/annotations/AbstractAnnotation.hh>

template <typename T>
class ListAnnotation : public AbstractAnnotation< std::list<T> >
{
public:
  typedef typename std::list<T>::iterator iterator;
  typedef typename std::list<T>::const_iterator const_iterator;


  ListAnnotation () : AbstractAnnotation< std::list<T> > (std::list<T> ()) { 
  }

  ListAnnotation (const std::list<T> &s) 
    : AbstractAnnotation< std::list<T> > (s) { 
  }

  virtual ~ListAnnotation () { } 

  virtual void add (const T &t) { this->value.push_back (t); }
  virtual iterator begin () { return this->value.begin (); }
  virtual iterator end () { return this->value.end (); }
  virtual const_iterator begin () const { return this->value.begin (); }
  virtual const_iterator end () const { return this->value.end (); }


  virtual void output_text (std::ostream &out) const {
    out << "{";
    for (const_iterator i = this->begin (); i != this->end (); i++)
      {
	out << " ";
	output (out, *i);
      }
    out << "}";
  }

protected:
  virtual void output (std::ostream &out, const T &t) const = 0;
};

#endif /* ! LISTANNOTATION_HH */

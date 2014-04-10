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
#ifndef KERNEL_ANNOTATION_HH
#define KERNEL_ANNOTATION_HH

#include <utils/Object.hh>


/*****************************************************************************/
/*! \brief Annotation are defined here. This is a general use class to
 *  store information in Node of the microcode.
 *****************************************************************************/
class Annotation : public Object
{

public:
  /*! \brief base constructor */
  Annotation() : Object() {}

  /*! \brief copy constructor */
  Annotation(const Annotation &a) : Object(a) {}

  /*! \brief virtual destructor */
  virtual ~Annotation() {}

  virtual void output_text(std::ostream &) const = 0;

  /*! \brief clone the annotation for copy constructor for instance.
   *  Note that the method returns a void pointer instead of
   *  Annotation* This is to uniformize the clone methods of inherited
   *  classes which do not really want to be attached to the
   *  Annotation class. Thus this method must be used with an explicit
   *  cast. */
  virtual void *clone() const = 0;

};

#endif /* KERNEL_ANNOTATION_HH */

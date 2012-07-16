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
#ifndef KERNEL_ANNOTATION_HH
#define KERNEL_ANNOTATION_HH

#include <string>
#include <list>
#include <map>
#include <ext/hash_map>
#include <utils/tools.hh>



/*****************************************************************************/
/*! \brief Annotation are defined here. This is a general use class to
 *  store information in Node of the microcode.
 *****************************************************************************/
class Annotation
{

public:
  /*! \brief base constructor */
  Annotation() {};

  /*! \brief copy constructor */
  Annotation(const Annotation &) {};

  /*! \brief virtual destructor */
  virtual ~Annotation() {};

  /*! \brief pretty printing */
  virtual std::string pp(std::string prefix = "") const = 0;

  /*! \brief clone the annotation for copy constructor for instance.
   *  Note that the method returns a void pointer instead of
   *  Annotation* This is to uniformize the clone methods of inherited
   *  classes which do not really want to be attached to the
   *  Annotation class. Thus this method must be used with an explicit
   *  cast. */
  virtual void *clone() const = 0;

};


typedef std::string AnnotationId;
#define AnnotationMap __gnu_cxx::hash_map<AnnotationId,Annotation*>



/* ***************************************************/
/**
 * \brief  Interface for annotable objects
 */
/* ***************************************************/
class Annotable
{
private:
  AnnotationMap amap;

public:
  Annotable(const AnnotationMap *o = 0);
  Annotable(AnnotationMap &o);

  /*! \brief Copy constructor */
  Annotable(const Annotable &o);
  /*! \brief Destructor */
  virtual ~Annotable();

  /*! \brief get annotations. Renamed this method in order to
   * lower the number of name conflicts on methods such as begin().
   * That's why the inheritance on std::hash_map is private */
  AnnotationMap *get_annotations();
  /*! \brief get a specific annotation. */
  Annotation *get_annotation(AnnotationId &id);
  /*! \brief get a specific annotation. */
  Annotation *get_annotation(const char id[]);

  /*! \brief add an annotation. Cf. previous remark */
  void add_annotation(AnnotationId &id, Annotation *a);
  /*! \brief add an annotation. Cf. previous remark */
  void add_annotation(const char id[], Annotation *a);
  /*! \brief returns true if contains at least one annotation */
  bool is_annotated() const;
  /*! \brief returns true if contains an annotation of id <id> */
  bool has_annotation(AnnotationId &id) const;

  /*! \brief returns true if contains an annotation of id <id> */
  bool has_annotation(const char id[]) const;

  /*! \brief delete an annotation of id <id> */
  void del_annotation(const char id[]);
  /*! \brief delete an annotation of id <id> */
  void del_annotation(AnnotationId &id);

  std::string pp(std::string prefix = "") const;
private:
  void copy_from_map(const AnnotationMap &o);
};

#endif /* KERNEL_ANNOTATION_HH */

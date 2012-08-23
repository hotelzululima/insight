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

#include <kernel/Annotable.hh>

#include <sstream>
#include <string>
#include <typeinfo>

#include <assert.h>

Annotable::Annotable(const AnnotationMap *o)
{
  if (o != NULL)
    copy_from_map(*o);
}

Annotable::Annotable(const Annotable &o)
{
  copy_from_map(o.amap);
}

Annotable::Annotable(AnnotationMap &o)
{
  copy_from_map(o);
}

Annotable::~Annotable()
{
  for (AnnotationMap::iterator it = amap.begin(); it != amap.end(); it++)
    {
      delete it->second;
    }
}

void
Annotable::copy_from_map(const AnnotationMap &o) {
  for (AnnotationMap::const_iterator it = o.begin(); it != o.end(); it++)
    {
      amap[it->first] = (Annotation *)it->second->clone();
    }
}

void Annotable::del_annotation(const char *id)
{
  AnnotationId tmp(id);
  return this->del_annotation(tmp);
}

void Annotable::del_annotation(const AnnotationId &id)
{
  assert(this->has_annotation(id));
  delete amap[id];
  amap.erase(id);
}


Annotable::AnnotationMap *
Annotable::get_annotations()
{
  return &amap;
}

Annotation *Annotable::get_annotation (const AnnotationId &id) const
{
  if (!has_annotation (id))
    return NULL;

  return amap.find (id)->second;
}

Annotation *Annotable::get_annotation(const char *id) const
{
  AnnotationId tmp(id);
  return this->get_annotation(tmp);
}

void Annotable::add_annotation(const AnnotationId &id, Annotation *a)
{
  amap[id] = a;
}

void Annotable::add_annotation(const char *id, Annotation *a)
{
  AnnotationId tmp(id);
  this->add_annotation(tmp, a);
}


bool Annotable::has_annotation(const AnnotationId &id) const
{

  return amap.find(id) != amap.end();
}


bool Annotable::has_annotation(const char *id) const
{
  AnnotationId tmp(id);
  return this->has_annotation(tmp);
}

bool Annotable::is_annotated() const
{
  return amap.size() > 0;
}

void 
Annotable::output_annotations (std::ostream &out) const
{
  out << "{";
  for (AnnotationMap::const_iterator it = amap.begin(); it != amap.end(); it++)
    {
      if (it != amap.begin())
        {
          out << ", ";
        }
      out << it->first << ":=" << *(it->second);
    }
  out << "}";
}

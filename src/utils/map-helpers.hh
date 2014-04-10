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
#ifndef UTILS_MAP_HELPERS_HH_
#define UTILS_MAP_HELPERS_HH_

/*
 * These two "functors" are helpers to substitute the default less<>
 * and equal_to<> template to avoid using operators < and == respectively
 */

template <class T>
struct LessThanFunctor
{
    bool operator() (const T &a, const T&b) const {
	return a.lessThan(b);
    }
};

template <class T>
struct EqualsFunctor
{
    bool operator() (const T &a, const T&b) const {
	return a.equals(b);
    }
};

template <class T>
struct HashFunctor
{
  std::size_t operator() (const T &a) const {
    return a.hashcode ();
  }
};

template <class T>
struct EqualsPtrFunctor
{
    bool operator() (const T *a, const T *b) const {
	return a->equals(b);
    }
};

template <class T>
struct HashPtrFunctor
{
  std::size_t operator() (const T *a) const {
    return a->hashcode ();
  }
};


#endif /* UTILS_MAP_HELPERS_HH_ */

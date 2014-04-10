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

#include <utils/FileStreamBuffer.hh>

#include <string>

using namespace std;

template <>
FileStreamBuffer<char, char_traits<char> >::FileStreamBuffer(FILE *f) {
  file = f;

  setg(read_buffer, read_buffer + 2, read_buffer + 2);
}

template <>
FileStreamBuffer<char, char_traits<char> >::~FileStreamBuffer() {
  fclose(file);
}

template <> char_traits<char>::int_type
FileStreamBuffer<char, char_traits<char> >::underflow() {
  int ret;

  ret = fgetc(file);

  if (ret == EOF)
    return char_traits<char>::eof();

  read_buffer[1] = ret;
  setg(read_buffer, read_buffer + 1, read_buffer + 2);

  return (char_traits<char>::int_type) ret;
}

template <> char_traits<char>::int_type
FileStreamBuffer<char, char_traits<char> >::overflow(char_traits<char>::int_type c) {
  if (!char_traits<char>::eq_int_type(c, char_traits<char>::eof())) {
    int ret = fputc((int) c, file);
    if (ret == EOF)
      return char_traits<char>::eof();
  }

  return char_traits<char>::not_eof(c);
}

template <> int
FileStreamBuffer<char, char_traits<char> >::sync() {
  return (fflush(file) != 0)? -1 : 0;
}

/*
 * microcode-asm-dump.hh -- add a comment about this file
 * 
 * This file is a part of XXX SET PROJECT NAME XXX. 
 * 
 * Copyright (C) 2012 CNRS UMR 5800 & Université Bordeaux I (see AUTHORS file).
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301  USA
 */

/*!
 * \file
 * \brief
 * 
 */
#include <kernel/annotations/AsmAnnotation.hh>
#include "asm-writer.hh"

void 
asm_writer (std::ostream &out, const Microcode *mc)
{
  std::vector<MicrocodeNode *> *nodes = mc->get_nodes();
  int nb_nodes = nodes->size ();
  
  for (int i = 0; i < nb_nodes; i++)
    {
      MicrocodeNode *N = nodes->at (i);

      if (! N->has_annotation (AsmAnnotation::ID))
	continue;

      AsmAnnotation *a = (AsmAnnotation *) 
	N->get_annotation (AsmAnnotation::ID);

      out << std::right << std::hex << std::setw (8) 
	  << N->get_loc ().getGlobal () << ":\t" 
	  << a->get_value () << std::endl;
    }
}

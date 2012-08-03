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
#include <kernel/expressions/Formula.hh>

#include <cassert>
#include <iostream>
#include <sstream>
#include <typeinfo>

#include <kernel/Expressions.hh>
#include <kernel/expressions/FormulaVisitor.hh>

using namespace std;

void 
Formula::init ()
{
  formula_store = new FormulaStore (100);
}

void 
Formula::terminate () 
{
  if (Formula::formula_store == NULL)
    return;
   
  if (Formula::formula_store->size () > 0)
    {      
      int nb = Formula::formula_store->size ();
      FormulaStore::iterator i = Formula::formula_store->begin ();
      FormulaStore::iterator end = Formula::formula_store->end ();
      cerr << "**** some formulas have not been deleted:" << endl;
      for (; i != end; i++, nb--)
	{
	  assert (nb > 0);
	  cerr << "**** refcount = " << (*i)->refcount 
	       << " formula = " << (*i)->pp () << endl;
	}
	  
    }
  delete Formula::formula_store;
  Formula::formula_store = NULL;
}

void 
Formula::dumpStore ()
{
  int nb = Formula::formula_store->size ();
  FormulaStore::iterator i = Formula::formula_store->begin ();
  FormulaStore::iterator end = Formula::formula_store->end ();
  for (; i != end; i++, nb--)
    {
      assert (nb > 0);
      cerr << (*i)->pp () << endl;
    }
}

/*****************************************************************************/
// Constructors
/*****************************************************************************/
Formula::Formula() : refcount(0) {}


/*****************************************************************************/
/* Destructor                                                                */
/*****************************************************************************/

Formula::~Formula() {}

/*****************************************************************************/
/* Hash                                                                      */
/*****************************************************************************/

size_t 
Formula::hash () const
{
  return std::tr1::hash<const char*>()(typeid(*this).name());
}


/*****************************************************************************/
/* Pretty Printing                                                           */
/*****************************************************************************/

#define FORMULA_TAB "    "

string 
Formula::to_string () const 
{
  return pp ("");
}

//
// FORMULA SHARING
//

size_t 
Formula::Hash::operator()(const Formula *const &F) const 
{
  return F->hash ();
}

bool 
Formula::Equal::operator()(const Formula *const &F1, 
			   const Formula * const &F2) const
{  
  return F1->equal (F2);
}


Formula::FormulaStore *Formula::formula_store = NULL;

Formula *
Formula::ref () const
{ 
  assert (refcount > 0);

  refcount++; 
  return (Formula *) this;
}

void 
Formula::deref () 
{ 
  assert (refcount > 0);
  refcount--; 
  if (refcount == 0) 
    {
      assert (formula_store->find (this) != formula_store->end ());
      formula_store->erase (this);

      delete this; 
    }
}

Formula *
Formula::find_or_add_formula (Formula *F)
{
  FormulaStore::iterator i = formula_store->find (F);
  assert (F->refcount == 0);

  if (i == formula_store->end ())
    {
      formula_store->insert (F);
      F->refcount = 1;
    }
  else
    {
      if (F != *i)
	delete F;
      F = *i;
      F->ref ();
    }

  return F;
}

//
// VISITORS 
//

void 
Formula::acceptVisitor (FormulaVisitor &visitor)
{
  acceptVisitor (&visitor);
}

void 
Formula::acceptVisitor (ConstFormulaVisitor &visitor) const
{
  acceptVisitor (&visitor);
}


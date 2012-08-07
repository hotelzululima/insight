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

#ifndef DOMAINS_SETS_SETS_MEMORY_HH
#define DOMAINS_SETS_SETS_MEMORY_HH

#include <domains/common/ConcreteAddressMemory.hh>
#include <domains/sets/SetsAddress.hh>
#include <domains/sets/SetsValue.hh>
#include <kernel/Memory.hh>
#include <kernel/RegisterMap.hh>

/*
   CHANTIER -- CHANTIER -- CHANTIER

   - il faut modifier l'interpreteur: pour un arc avec une condition, il faut selectionner les
     les sous-ensembles qui realise la condition, et construire un contexte correspondant.
     en l'occurence ici, filtrer les bonnes valeurs.

   - en fait, il faut faire un filtre qui à partir d'un contexte et
     d'une condition donnée par une expression, produit un nouveau
     contexte qui réalise la condition. Il faut ajouter cette fonction
     dans la classe Contexte.

   - c'est du fait qu'un contexte encode en fait plusieurs possibilités de contexte.

   - attention à l'evaluateur, il faut peut-être l'affiner en vue d'en faire un filtre.

   - méthode 1:
       une passe sur l'expression pour déterminer les parties de l'états accédées en lecture.
       --> construction d'un état limité à ces accès seulement.
       --> faire le produit de cet état pour construire un énumérateur d'état
       --> selectionner l'ensemble des états rendant la condition vraie.
       --> construire l'état union.
       --> o optimisation exponentielle: les lectures s'enchainent de façon arborescente, sur la base de l'expression.
           o ensuite, on fait le produit des feuilles.

       --> En fait, on peut faire un evaluateur qui retourne une liste de résultats associés à des états, ou bien une
           liste de choix des etats (moins gourmand) = l'état original + une liste de choix.

       --> Ensuite, pour chaque bonne valeur,
           on produit un nouvel etat, puis, on
           l'union des etats.

       --> mais attention, l'union des etats ne marche
           pas vraiment, ca introduit des combinaisons
           de valeurs eventuellement fausses. C'est pas si
           grave, c'est une surapproximation grossiere
           mais bon, toute l'abstraction fonctionne sur ce
           principe. Introduisant des combinaisons de valeurs
           n'arrivant en fait pas.f

       --> ATTENTION, il faut modifier le stepper !

       --> GRRR recompilation des automates dépendant des ConcreteAddressMemory...

 */

// TODO cloning function
// TODO TODO TODO En fait, SetsMemory contient 2 tables de registres : 1 dans son heritage et 1 dans celui de ConcreteAddressMemory...
// Meme pb pour toutes les memoires en fait...
class SetsMemory :
  public Memory<SetsAddress, SetsValue>,
  public RegisterMap<SetsValue>
{

  /*! \brief The data structure for memory. It associates a set of value to
   * concrete addresses. */
  ConcreteAddressMemory<SetsValue> mem;

public:

  /*! \brief construct an empty memory */
  SetsMemory();

  SetsMemory(const SetsMemory &other);

  /*! \brief destructor, RAS. */
  virtual ~SetsMemory();

  /*! \brief Retrieve all the contents of cells pointed by addresses
      in a and makes the union of all these sets. size is given in bytes */
  virtual SetsValue get(const SetsAddress &a, int size, 
			Architecture::endianness_t e)
    throw (Architecture::UndefinedValue);

  /*! \brief For each concrete address ca contained in a, adds the
   *  elements of v into the set pointed by ca.
   *  \return true iff the cell has indeed been modified, i.e. iff its value
   *  has changed. It is used to compute the merge function return value. */
  bool add_to_cells(const SetsAddress &a,
                    const SetsValue &v,
                    Architecture::endianness_t e);

  /*! \brief There is three cases for the put operation:
   *  1) if the address a is determined, i.e., is a singleton, then one
   *     replace the corresponding set.
   *  2) if the address a is not determined, i.e., has several possible values,
   *     then one adds the contents of v to each corresponding memory cells.
   *  3) if a is TOP, at the moment one does nothing (just comment output).
   *     Possible Method:
   *     One adds it to all cells of the memory. Caution, in the
   *     implementation, one does not add the values of v in the hash table
   *     which does not contains the whole memory a priori. Instead of that,
   *     one adds it to a special value (global) whose meaning is to be added to
   *     any cell in the memory.
   */
  virtual void put(const SetsAddress &a, const SetsValue &v, 
		   Architecture::endianness_t e);

  /*! \brief Clear the set pointed by the addresses in a. size is given in bytes */
  void clear(ConcreteAddress addr, int size);

  /*! \brief Tells whether at least one of the addresses contained in
      a has a contents */
  virtual bool is_defined(const SetsAddress &a) const;

  /*! \brief For each defined memory cell of this instance or the
      dother one, makes the union of the two sets of possible
      values. */
  virtual bool merge(const SetsMemory &);

  /*! \brief Provides an iterator on all the values contained in the
      memory */
  ConcreteAddressMemory<SetsValue>::ValueIterator get_value_iterator() const;

  using RegisterMap<SetsValue>::is_defined;
  using RegisterMap<SetsValue>::get;
  using RegisterMap<SetsValue>::put;
  using RegisterMap<SetsValue>::clear;

  /*! \brief Pretty print */
  virtual std::string pp();
};

#endif /* DOMAINS_SETS_SETS_MEMORY_HH */

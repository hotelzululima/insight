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

#include <domains/sets/SetsContext.hh>
#include <domains/sets/SetsAddress.hh>
#include <domains/sets/SetsExprSemantics.hh>
#include <domains/sets/SetsMemory.hh>
#include <domains/sets/SetsValue.hh>

#include <utils/tools.hh>

#include <list>
#include <map>

using namespace std;

SetsContext::SetsContext(SetsMemory *mem)
{
  memory = mem;
}

SetsContext::~SetsContext() {}

SetsContext *SetsContext::clone()
{
  return new SetsContext(new SetsMemory(*memory));
}

bool SetsContext::merge(AbstractContext<SETS_CLASSES> * other)
{
  SetsContext *ctx = dynamic_cast<SetsContext *>(other);
  if (ctx == NULL)
    logs::fatal_error("Set context: merge with other kind of context");

  return this->memory->merge(*(other->memory));
}

SetsContext *SetsContext::empty_context()
{
  return new SetsContext(new SetsMemory());
}

/*****************************************************************************/
/* Non Deterministic Evaluation                                              */
/*****************************************************************************/
// TODO: optim: recopie du resultat peut etre un peu abusee...

void
add_value_with_same_context(ND_eval_result &current_list,
                            SpecializedContext *s_ctxt,
                            SetsValue s)
{
  try
    {
      std::list<ConcreteValue> values = s.get_values().getValue();
      for (std::list<ConcreteValue>::iterator v = values.begin(); v != values.end(); v++)
        current_list.push_back(pair< Option<ConcreteValue>, SpecializedContext * > (Option<ConcreteValue>(*v), s_ctxt));
    }
  catch (OptionNoValueExc &)
    {
      current_list.push_back(pair< Option<ConcreteValue>, SpecializedContext * > (Option<ConcreteValue>() , s_ctxt));
    }
}

/** ** **/

ND_eval_result
ND_eval_unary_expr_generic(SetsValue(*op_sem)(SetsValue, int, int),
                           SpecializedContext *s_ctxt,
                           Expr *e, int offset, int size)
{

  ND_eval_result arg_vals = ND_eval(s_ctxt, e);
  ND_eval_result result;
  for (ND_eval_result::iterator arg_pair = arg_vals.begin(); arg_pair != arg_vals.end(); arg_pair++)
    result.push_back(std::pair< Option<ConcreteValue>, SpecializedContext * > (op_sem(SetsValue(arg_pair->first), offset, size).extract_value(),
                     arg_pair->second));
  return result;
}

/** ** **/

ND_eval_result
ND_eval_unary_expr(SpecializedContext *s_ctxt, UnaryApp *ua)
{

  switch (ua->get_op())
    {
    case BV_OP_NEG:
      return ND_eval_unary_expr_generic(SetsExprSemantics::BV_OP_NEG_eval,
					s_ctxt,
					ua->get_arg1(), ua->get_bv_offset (),
					ua->get_bv_size ());
    case BV_OP_NOT:
      return ND_eval_unary_expr_generic(SetsExprSemantics::BV_OP_NOT_eval,
					s_ctxt, ua->get_arg1(),
					ua->get_bv_offset (),
					ua->get_bv_size ());
    default:
      logs::fatal_error("Context::eval Unknown unary operator");
    }

}

/** ** **/

ND_eval_result
ND_eval_binary_expr_generic(SetsValue(*op_sem)(SetsValue, SetsValue, int, int),
                            SpecializedContext *s_ctxt,
                            Expr *arg1_expr,
                            Expr *arg2_expr, int offset, int size)
{

  ND_eval_result arg1_vals = ND_eval(s_ctxt, arg1_expr);
  ND_eval_result result;
  for (ND_eval_result::iterator arg1_pair  = arg1_vals.begin();
       arg1_pair != arg1_vals.end(); arg1_pair++)
    {
      ND_eval_result arg2_vals = ND_eval(arg1_pair->second, arg2_expr);
      for (ND_eval_result::iterator arg2_pair  = arg2_vals.begin();
           arg2_pair != arg2_vals.end(); arg2_pair++)
        result.push_back(std::pair< Option<ConcreteValue>, SpecializedContext * > (op_sem(arg1_pair->first, arg2_pair->first, offset, size).extract_value(),
                         arg2_pair->second));
    }

  return result;
}

// TODO: free memory

/** ** **/

ND_eval_result
ND_eval_binary_expr(SpecializedContext *s_ctxt, BinaryApp *e)
{
  int offset = e->get_bv_offset ();
  int size = e->get_bv_size ();

  switch (e->get_op())
    {
    case BV_OP_ADD:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_ADD_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_SUB:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_SUB_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_MUL_U:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_MUL_U_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_MUL_S:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_MUL_S_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_DIV_U:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_DIV_U_eval, s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_DIV_S:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_DIV_S_eval, s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);

    case BV_OP_AND:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_AND_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_OR:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_OR_eval,   s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_XOR:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_XOR_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_LSH:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LSH_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_RSH_U:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_RSH_U_eval,
					 s_ctxt, e->get_arg1(), e->get_arg2(),
					 offset, size);
    case BV_OP_RSH_S:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_RSH_S_eval,
					 s_ctxt, e->get_arg1(), e->get_arg2(),
					 offset, size);
    case BV_OP_ROR:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_ROR_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_ROL:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_ROL_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);

    case BV_OP_EQ:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_EQ_eval,
					 s_ctxt, e->get_arg1(), e->get_arg2(),
					 offset, size);

    case BV_OP_LEQ_S:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LEQ_S_eval,
					 s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_GEQ_S:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LEQ_S_eval,  s_ctxt, e->get_arg2(), e->get_arg1(), offset, size);
    case BV_OP_LT_S:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LEQ_S_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_GT_S:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LT_S_eval,   s_ctxt, e->get_arg2(), e->get_arg1(), offset, size);

    case BV_OP_LEQ_U:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LEQ_U_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_GEQ_U:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LEQ_U_eval,  s_ctxt, e->get_arg2(), e->get_arg1(), offset, size);
    case BV_OP_LT_U:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LEQ_U_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_GT_U:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_LT_U_eval,   s_ctxt, e->get_arg2(), e->get_arg1(), offset, size);

    case BV_OP_POW:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_POW_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);
    case BV_OP_CONCAT:
      return ND_eval_binary_expr_generic(SetsExprSemantics::BV_OP_CONCAT_eval,  s_ctxt, e->get_arg1(), e->get_arg2(), offset, size);

    default:
      logs::fatal_error("Context::eval Unknown binary operator");
    }

#undef APPLY_BINARY

}

/** ** **/

ND_eval_result
ND_eval(SpecializedContext *s_ctxt, const Expr *e)
{

  ND_eval_result result;

  if (e->is_Variable())
    logs::fatal_error("GenericContext:eval: Variable are not supported by interpreter");

  if (e->is_Constant())
    {
      add_value_with_same_context(result, s_ctxt,
                                  SetsValue((Constant *) e));
      return result;
    }

  if (e->is_UnaryApp())
    return ND_eval_unary_expr(s_ctxt, (UnaryApp *) e);

  if (e->is_BinaryApp())
    return ND_eval_binary_expr(s_ctxt, (BinaryApp *) e);

  if (e->is_MemCell())
    {
      // Here we take all possible addresses, and then, all possible
      // values pointed by each addresses
      MemCell *mc = (MemCell *) e;

      ND_eval_result addresses = ND_eval(s_ctxt, mc->get_addr());

      if (addresses.size() == 0) logs::fatal_error("ND_eval : empty address");

      for (ND_eval_result::iterator addr_pair = addresses.begin(); addr_pair != addresses.end(); addr_pair++)
        {
          SpecializedContext *current_s_ctxt = addr_pair->second;
          ConcreteAddress addr;
          try
            {
              new(&addr) ConcreteAddress((addr_pair->first).getValue());
            }
          catch (OptionNoValueExc &)
            {
              logs::warning << "ND_eval: TOP value for address : returns TOP"
			   << std::endl;
              result.push_back(std::pair< Option<ConcreteValue>, SpecializedContext * > (Option<ConcreteValue>() , current_s_ctxt));
              return result;
            }

          try
            {
              Option<ConcreteValue> val = current_s_ctxt->get_specialized(addr);
              result.push_back(std::pair< Option<ConcreteValue>, SpecializedContext * > (val, current_s_ctxt));
            }
          catch (SpecializedContextNotSpecialized &)
            {
              // addr is not specialized : one produces any possible specialisation for addr
              SetsValue s_val =
                current_s_ctxt->underlying_context->memory->get(SetsAddress(SetsValue(addr_pair->first)),
                    mc->get_bv_size() / 8, Architecture::LittleEndian);  // TODO: attention au LittleEndian
              try
                {
                  std::list<ConcreteValue> possible_values = s_val.get_values().getValue(); // Raise an exception if it is TOP
                  for (std::list<ConcreteValue>::iterator v = possible_values.begin(); v != possible_values.end(); v++)
                    {
                      SpecializedContext *new_s_ctxt = new SpecializedContext(*s_ctxt);
                      new_s_ctxt->specialize(addr, *v);
                      result.push_back(pair< Option<ConcreteValue>, SpecializedContext * > (Option<ConcreteValue>(*v), new_s_ctxt));
                    }
                }
              catch (OptionNoValueExc &)     // case TOP
                {
                  SpecializedContext *new_s_ctxt = new SpecializedContext(*s_ctxt);
                  new_s_ctxt->specialize(addr, Option<ConcreteValue>());
                  result.push_back(pair< Option<ConcreteValue>, SpecializedContext * > (Option<ConcreteValue>() , new_s_ctxt));
                }
            }
        }
      return result;
    }

  if (e->is_RegisterExpr())
    {
      const RegisterDesc *reg = ((RegisterExpr *) e)->get_descriptor();

      try
        {
          Option<ConcreteValue> val = s_ctxt->get_specialized(reg);
          result.push_back(std::pair< Option<ConcreteValue>, SpecializedContext * > (val, s_ctxt));
        }
      catch (SpecializedContextNotSpecialized &)
        {
          // reg is not specialized : one produces any possible specialisation for addr
          SetsValue s_val =
	    s_ctxt->underlying_context->memory->get(reg);
          try
            {
              std::list<ConcreteValue> possible_values = s_val.get_values().getValue(); // Raise an exception if it is TOP
              for (std::list<ConcreteValue>::iterator v = possible_values.begin(); v != possible_values.end(); v++)
                {
                  SpecializedContext *new_s_ctxt = new SpecializedContext(*s_ctxt);
                  new_s_ctxt->specialize(reg, *v);
                  result.push_back(pair< Option<ConcreteValue>, SpecializedContext * > (Option<ConcreteValue>(*v), new_s_ctxt));
                }
            }
          catch (OptionNoValueExc &)     // case TOP
            {
              SpecializedContext *new_s_ctxt = new SpecializedContext(*s_ctxt);
              new_s_ctxt->specialize(reg, Option<ConcreteValue>());
              result.push_back(pair< Option<ConcreteValue>, SpecializedContext * > (Option<ConcreteValue>() , new_s_ctxt));
            }
        }
      return result;
    }

  logs::fatal_error("Context::eval Expression Type unknown");
}


/*****************************************************************************/

SetsValue SetsContext::eval(const Expr *e)
{

  SpecializedContext s_ctxt(this);
  ND_eval_result nd_evaluation = ND_eval(&s_ctxt, e);

  SetsValue the_value(BV_DEFAULT_SIZE);  // \todo check size
  for (std::list< std::pair< Option<ConcreteValue>, SpecializedContext *> >::iterator
       v = nd_evaluation.begin();
       v != nd_evaluation.end();
       v++)
    the_value.add_value(v->first);

  return the_value;
}


/*****************************************************************************/
/* Specialized Context                                                       */
/*****************************************************************************/

SpecializedContext::SpecializedContext(SetsContext *ctxt)
{
  underlying_context = ctxt;
}

SpecializedContext::~SpecializedContext() {}

/*****************************************************************************/

void
SpecializedContext::
specialize(ConcreteAddress addr, Option<ConcreteValue> v)
{
  specialised_mem_cells.push_front(std::pair < ConcreteAddress, Option<ConcreteValue> > (addr, v));
}

Option<ConcreteValue>
SpecializedContext::
get_specialized(ConcreteAddress addr)
{
  for (std::list < std::pair < ConcreteAddress, Option<ConcreteValue> > > ::const_iterator
       p = specialised_mem_cells.begin();
       p != specialised_mem_cells.end();
       p++)
    if (p->first.get_address() == addr.get_address()) return p->second;
  throw SpecializedContextNotSpecialized();
}

void
SpecializedContext::
specialize(const RegisterDesc *reg, Option<ConcreteValue> v)
{
  specialised_registers.push_front(std::pair < const RegisterDesc *, Option<ConcreteValue> > (reg, v));
}

Option<ConcreteValue>
SpecializedContext::
get_specialized(const RegisterDesc *reg)
{
  for (std::list < std::pair <const RegisterDesc *, Option<ConcreteValue> > > ::const_iterator
       p = specialised_registers.begin();
       p != specialised_registers.end();
       p++)
    if (p->first == reg)
      return p->second;
  throw SpecializedContextNotSpecialized();
}

/*****************************************************************************/

Option<AbstractContext<SETS_CLASSES>*>
SpecializedContext::
merge_contexts(std::list< SpecializedContext *> s_ctxts)
{

  // 0. check that all specialised contexts have the same underlying context
  if (s_ctxts.size() == 0) return Option<AbstractContext<SETS_CLASSES>*>();
  SpecializedContext *first_ctxt = s_ctxts.front();
  SetsContext *underlying_ctxt = first_ctxt->underlying_context;
  for (std::list< SpecializedContext *>::const_iterator ctxt = s_ctxts.begin(); ctxt != s_ctxts.end(); ctxt++)
    if ((*ctxt)->underlying_context != underlying_ctxt) logs::fatal_error("SetsContext:merge_contexts: underlying contexts different");

  // 1. collect all specialized address and registers in all the specialised context
  std::list < std::pair < ConcreteAddress, Option<ConcreteValue> > > all_specialised_mem_cells;
  std::list < std::pair < const RegisterDesc *, Option<ConcreteValue> > > all_specialised_registers;
  for (std::list< SpecializedContext *>::const_iterator ctxt = s_ctxts.begin(); ctxt != s_ctxts.end(); ctxt++)
    { /* Concatenate all_specialised_mem_cells and (*ctxt)->specialised_mem_cells */
      all_specialised_mem_cells.insert(all_specialised_mem_cells.end(),
				       (*ctxt)->specialised_mem_cells.begin(),
				       (*ctxt)->specialised_mem_cells.end());
      /* Concatenate all_specialised_registers and (*ctxt)->specialised_registers */
      all_specialised_registers.insert(all_specialised_registers.end(),
				       (*ctxt)->specialised_registers.begin(),
				       (*ctxt)->specialised_registers.end());
    }

  // 2. for each specialized address (resp. register),
  //    2.1 delete the corresponding value in a copy of the underlying context
  SetsContext *underlying_ctxt_cpy = underlying_ctxt->clone();

  for (std::list < std::pair < ConcreteAddress, Option<ConcreteValue> > >::const_iterator
       cell = all_specialised_mem_cells.begin();
       cell != all_specialised_mem_cells.end();
       cell++)
    underlying_ctxt_cpy->memory->clear(cell->first, BV_DEFAULT_SIZE); // \todo check size

  for (std::list < std::pair < const RegisterDesc *, Option<ConcreteValue> > >::const_iterator
       reg = all_specialised_registers.begin();
       reg != all_specialised_registers.end();
       reg++)
    underlying_ctxt_cpy->memory->clear(reg->first);

  //    2.2 put all the specialized values corresponding to the address (resp. registers) in the
  //        copy of the underlying context.

  for (std::list < std::pair < ConcreteAddress, Option<ConcreteValue> > >::const_iterator
       cell = all_specialised_mem_cells.begin();
       cell != all_specialised_mem_cells.end();
       cell++)
    underlying_ctxt_cpy->memory->put(cell->first, SetsValue(cell->second),
				     Architecture::LittleEndian); // TODO: LittleEndian?

  for (std::list < std::pair < const RegisterDesc *, Option<ConcreteValue> > >::const_iterator
       reg = all_specialised_registers.begin();
       reg != all_specialised_registers.end();
       reg++)
    {
      if (underlying_ctxt_cpy->memory->is_defined(reg->first))
        {
          SetsValue v = underlying_ctxt_cpy->memory->get(reg->first);
          v.add(SetsValue(reg->second));
          underlying_ctxt_cpy->memory->put(reg->first, v);
        }
      else
        {
          underlying_ctxt_cpy->memory->put(reg->first, SetsValue(reg->second));
        }
    }

  return Option<AbstractContext<SETS_CLASSES>*>(underlying_ctxt_cpy);
}

/*****************************************************************************/

pair< Option<AbstractContext<SETS_CLASSES>*>, Option<AbstractContext<SETS_CLASSES>*> >
SetsContext::
split_context(Expr *condition)
{

  SpecializedContext s_ctxt(this);
  ND_eval_result nd_evaluation = ND_eval(&s_ctxt, condition);

  std::list< SpecializedContext *> true_contexts;
  std::list< SpecializedContext *> false_contexts;

  SetsValue the_value(BV_DEFAULT_SIZE);
  for (std::list< std::pair< Option<ConcreteValue>, SpecializedContext *> >::iterator
       v = nd_evaluation.begin();
       v != nd_evaluation.end();
       v++)
    {

      if (v->first.hasValue())
        {
          if (v->first.getValue().to_bool().getValue())
            true_contexts.push_back(v->second);
          else
            false_contexts.push_back(v->second);
        }
      else   // v is TOP
        {
          true_contexts.push_back(v->second);
          false_contexts.push_back(v->second);
        }
    }

  return std::pair<Option<AbstractContext<SETS_CLASSES>*>, Option<AbstractContext<SETS_CLASSES>*> >
         (SpecializedContext::merge_contexts(true_contexts),
          SpecializedContext::merge_contexts(false_contexts));
}

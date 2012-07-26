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

#include <string>
#include <vector>
#include <sstream>

#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>

#include "xml_microcode_parser.hh"
#include "xml_microcode_generator.hh"

using namespace std;

string tab = "  ";

string
xml_indent(string str)
{
  if (str.length() == 0)
    return tab;

  string indented = str;

  indented.insert(0, tab);

  for (int i = 0; i < (int)indented.length(); i++)
    if (indented[i] == '\n')
      indented.insert(i + 1, tab);

  return indented;
}

bool
is_on_one_line(string str)
{
  for (int i = 0; i < (int) str.length(); i++)
    if (str[i] == '\n') return false;

  return true;
}
/*****************************************************************************/

string
xml_elt(string id, string str)
{
  if (is_on_one_line(str) && str.length() < 32)  // esthetic :-)
    return "<" + id  + ">" + str + "</" + id  + ">";
  else
    return "<" + id  + ">\n" + xml_indent(str) + "\n" + "</" + id  + ">";
}

string
xml_atom(string id)
{
  return "<" + id + "/>";
}

/** \brief Adds the attribute to the highest level node */
string
xml_add_attribute(string attribute_id, string value, string elt)
{
  string result = elt;
  string attribute_def = " " + attribute_id + "=\"" + value + "\"";
  for (int i = 0; i < (int)result.length(); i++)
    {
      if (result[i] == '>')
        {
          if (i > 0 && result[i - 1] == '/')
            result.insert(i - 1, attribute_def);
          else result.insert(i, attribute_def);

          break;
        }
    }
  return result;
}

string
string_of_int(int n)
{
  ostringstream oss;
  oss << n;
  return oss.str();
}

/*****************************************************************************/

string
xml_of_constant(Constant *c)
{
  return xml_add_attribute("size", string_of_int(c->get_bv_size()),
                           xml_elt("const", string_of_int(c->get_val())));
}

string
xml_of_variable(Variable *v)
{
  return xml_add_attribute("id", v->get_id(), xml_atom("formalvar"));
}

string
xml_of_register(RegisterExpr *reg)
{
  string id;

  if (reg->get_name() == "")
    id = "R" + string_of_int(reg->get_descriptor()->get_index());
  else
    id = string(reg->get_name());

  if (xml_get_register(id) == NULL)
    xml_declare_register(id.c_str(), reg->get_bv_size());

  return xml_add_attribute("var", id, xml_atom("var"));
}

string
xml_of_memcell(MemCell *m)
{
  string addr = xml_of_expr(m->get_addr());
  // TODO: endiannness
  string result = xml_elt("memref", addr);
  string mem = string(m->get_tag());

  if (mem.length() > 0)
    result = xml_add_attribute("mem", mem, result);

  result = xml_add_attribute("size", string_of_int(m->get_bv_size()), result);

  return result;
}

string
xml_of_binary_op(BinaryOp op)
{
  switch (op)
    {
    case ADD:
      return xml_atom("plus");
    case SUB:
      return xml_atom("minus");
    case MUL_U:
      return xml_atom("times_u");
    case MUL_S:
      return xml_atom("times_s");
    case DIV_S:
      return xml_atom("divs");
    case DIV_U:
      return xml_atom("divu");
    case MODULO:
      return xml_atom("mods");
    case OR:
      return xml_atom("or");
    case AND_OP:
      return xml_atom("and");
    case LOR:
      return xml_atom("lor");
    case LAND:
      return xml_atom("land");
    case XOR:
      return xml_atom("xor");
    case CONCAT:
      return xml_atom("concat");
    case LSH:
      return xml_atom("lshift");
    case RSH_S:
      return xml_atom("rshifts");
    case RSH_U:
      return xml_atom("rshiftu");
    case EQ:
      return xml_atom("eq");
    case LEQ_U:
      return xml_atom("lequ");
    case LT_U:
      return xml_atom("ltu");
    case LEQ_S:
      return xml_atom("leqs");
    case LT_S:
      return xml_atom("lts");
    default:
      Log::fatal_error("xml_of_binary_op:: operator not supported");
    }
}

string
xml_of_binaryapp(BinaryApp *b)
{
  string arg1 = xml_of_expr(b->get_arg1());
  string arg2 = xml_of_expr(b->get_arg2());
  string op = xml_of_binary_op(b->get_op());
  return xml_elt("apply", op + "\n" + arg1 + "\n" + arg2);
}

string
xml_of_unary_op(UnaryOp op)
{
  switch (op)
    {
    case NOT:
      return xml_atom("not");
    case NEG:
      return xml_atom("minus");
    default:
      Log::fatal_error("xml_of_unary_op:: operator not supported");
    }
}

string
xml_of_unaryapp(UnaryApp *u)
{
  string arg1 = xml_of_expr(u->get_arg1());
  string op = xml_of_unary_op(u->get_op());
  return xml_elt("apply", op + "\n" + arg1);
}


string
xml_of_lvalue(Expr *lv)
{
  if (lv->is_MemCell())
    return xml_of_memcell((MemCell *) lv);
  if (lv->is_RegisterExpr())
    return xml_of_register((RegisterExpr *) lv);

  Log::fatal_error("xml_of_lvalue:: lvalue type unknown");
}

string
xml_of_expr(Expr *e)
{

  if (e->is_Variable())
    return xml_of_variable((Variable *) e);
  if (e->is_Constant())
    return xml_of_constant((Constant *) e);
  if (e->is_UnaryApp())
    return xml_of_unaryapp((UnaryApp *) e);
  if (e->is_BinaryApp())
    return xml_of_binaryapp((BinaryApp *) e);
  if (e->is_LValue())
    return xml_of_lvalue((LValue *) e);

  Log::fatal_error("xml_of_expr:: expr type unknown");
}


/*****************************************************************************/

string
xml_of_mcaddress(MicrocodeAddress addr)
{
  char glob[16], loc[16];
  sprintf(glob, "%X", addr.getGlobal());
  sprintf(loc, "%X", addr.getLocal());
  return "x" + string(glob) + "-" + string(loc);
}

string
xml_guard_of_static_arrow(StaticArrow *arr)
{
  return
    xml_add_attribute("next", xml_of_mcaddress(arr->get_target()),
                      xml_elt("guard", xml_of_expr(arr->get_condition())));
}

string
xml_of_stmtarrow(StmtArrow *arr)
{
  string new_stmtarrow("");

  if (!(arr->is_dynamic()))
    {
      StaticArrow *sarr = (StaticArrow *) arr;

      if (sarr->get_stmt()->is_Assignment())
        {
          if (!(sarr->get_condition()->eval_level0()))
            Log::fatal_error("Assignment arrow with condition not supported");
          string lv = xml_of_lvalue(((Assignment *) sarr->get_stmt())->get_lval());
          string v = xml_of_expr(((Assignment *) sarr->get_stmt())->get_rval());
          new_stmtarrow =
            xml_add_attribute("next", xml_of_mcaddress(sarr->get_target()),
                              xml_add_attribute("id", xml_of_mcaddress(sarr->get_origin()),
                                                xml_elt("assign", lv + "\n" + v)));
	  goto finish;
        }

      if (sarr->get_stmt()->is_Skip())
        {
          string guard = xml_guard_of_static_arrow(sarr);
          new_stmtarrow =
            xml_add_attribute("id", xml_of_mcaddress(sarr->get_origin()),
                              xml_elt("skip", guard));
	  goto finish;
        }

      if (sarr->get_stmt()->is_Jump())
        Log::fatal_error("xml_of_stmtarrow:: static jump statement not supported");
    }
  else   // Arrow is dynamic
    {

      DynamicArrow *darr = (DynamicArrow *) arr;
      string target = xml_of_expr(darr->get_target());
       new_stmtarrow =
	 xml_add_attribute("id", xml_of_mcaddress(darr->get_origin()),
			   xml_elt("jump", target));
       goto finish;
    }

 finish:
  return new_stmtarrow;

}


/*****************************************************************************/

string
xml_of_microcode_element(MicrocodeNode *elt)
{
  string result = "";
  vector<StmtArrow *> * succs = elt->get_successors();

  //--- particular case of the switch
  bool is_switch = true;
  string guards = "";
  for (int i = 0; i < (int) succs->size(); i++)
    {
      if (!((*succs)[i]->is_dynamic()) &&
          (*succs)[i]->get_stmt()->is_Skip())
        {
          guards = guards + xml_guard_of_static_arrow((StaticArrow *)(*succs)[i]);

          if (i < (int) succs->size() - 1)
	    guards = guards + "\n";
        }
      else
        {
          is_switch = false;
          break;
        }
    }

  if (is_switch)
    {
      result = xml_add_attribute("id", xml_of_mcaddress(elt->get_loc()),
                                 xml_elt("switch", guards));
    }
  else   //--- general case
    {
      for (int i = 0; i < (int) succs->size(); i++)
        {
          result = result + xml_of_stmtarrow((*succs)[i]);
        }
    }

  return result;
}

/*****************************************************************************/

string
xml_register_declarations()
{
  string result = "";

  for (XmlRegisterStore::iterator reg = xml_register_store.begin();
       reg != xml_register_store.end();
       reg++)
    {
      result = result +
               xml_add_attribute("id", string(reg->first),
                                 xml_add_attribute("size", string_of_int(reg->second->get_bv_size()),
                                     xml_atom("vardecl"))) + "\n";
    }
  return result;
}

/*****************************************************************************/

string
xml_of_microcode(const Microcode *prg)
{
  xml_reset_register_store();

  string result = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
  result = result + "<!DOCTYPE program SYSTEM \"bincoa.dtd\">\n";


  vector<MicrocodeNode *> * elts = prg->get_nodes();
  string nodes = "";
  for (int i = 0; i < (int) elts->size(); i++)
    nodes = nodes + xml_of_microcode_element((*elts)[i]) + "\n\n";

  result = result + xml_elt("program", xml_register_declarations() + "\n" + xml_elt("code", nodes));
  return result;
}

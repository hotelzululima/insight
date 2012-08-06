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

#include <stdlib.h>
#include <string.h>

#include <map>
#include <string>
#include <iomanip>
#include <iostream>
#include <tr1/unordered_map>

#include <libxml2/libxml/tree.h>
#include <libxml2/libxml/parser.h>

#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>

#include "xml_microcode_parser.hh"

using namespace std;

/*****************************************************************************/
/* Tools                                                                     */
/*****************************************************************************/

#define XML_PARSER_DEBUG_MODE 0

#if XML_PARSER_DEBUG_MODE
#define XML_DBG(x...) printf(x)
#else
#define XML_DBG(x...)
#endif

#define XML_PARSE_ERROR(node, reason...) {                         \
    char prefix[1024];                                             \
    char the_reason[1024];                                         \
    sprintf(prefix, "Xml parse error [line %d]: ", node->line);    \
    sprintf(the_reason, reason);                                   \
    strcat(prefix, the_reason);                                    \
    Log::fatal_error(prefix);                                      \
  }

/*****************************************************************************/

int parse_hexadecimal(char *str)
{
  std::string s(str);
  uint32_t v;
  std::istringstream iss(s);
  iss >> std::setbase(16) >> v;
  return v;
}

/*****************************************************************************/
// Xml General
/*****************************************************************************/
pair<xmlDocPtr, xmlNodePtr> xml_get_root_from_file(const string filename);
bool xml_has_attribute(xmlNodePtr node, const string id);
char *xml_get_attribute(xmlNodePtr node, const char *attribute_id);
int xml_get_int_attribute(xmlNodePtr node, const char *attribute_id);
char *xml_get_text(xmlNodePtr node);
xmlNodePtr xml_nth_child(xmlNodePtr node, int n);
int xml_child_nb(xmlNodePtr node);
/*****************************************************************************/

pair<xmlDocPtr, xmlNodePtr> xml_get_root_from_file(const string filename)
{
  xmlDocPtr doc;
  xmlNodePtr root;

  xmlKeepBlanksDefault(0);
  doc = xmlParseFile(filename.c_str());
  if (doc == NULL)
    Log::fatal_error("Xml Document XML not valid\n");

  root = xmlDocGetRootElement(doc);
  if (root == NULL)
    {
      xmlFreeDoc(doc);
      Log::fatal_error("XML Document empty\n");
    }

  return pair<xmlDocPtr, xmlNodePtr> (doc, root);
}

bool xml_has_attribute(xmlNodePtr node, const char *id)
{
  return xmlGetProp(node, (const xmlChar *) id) != NULL;
}

char *xml_get_attribute(xmlNodePtr node, const char *attribute_id)
{
  char *val;
  if ((val = (char *) xmlGetProp(node, (const xmlChar *) attribute_id)) == NULL)
    XML_PARSE_ERROR(node, "Xml parser: expecting %s attribute at line %d\n",
		    attribute_id, node->line);
  return val;
}

int xml_get_int_attribute(xmlNodePtr node, const char *attribute_id)
{
  return atoi(xml_get_attribute(node, attribute_id));
}

char *xml_get_text(xmlNodePtr node)
{
  if (node->children != NULL && node->children->type == XML_TEXT_NODE)
    {
      xmlChar *content = xmlNodeGetContent(node);
      char *result = strdup((char *) content);
      xmlFree(content);
      return result;
    }
  else
    return NULL;
}

xmlNodePtr xml_nth_child(xmlNodePtr node, int n)
{
  int k = 0;
  xmlNodePtr child = node->children;
  while (k < n && child != NULL)
    {
      child = child->next;
      k++;
    }
  return child;
}

int xml_child_nb(xmlNodePtr node)
{
  int n = 0;
  xmlNodePtr child = node->children;
  while (child != NULL)
    {
      child = child->next;
      n++;
    }
  return n;
}

#define check_name(node, ident) \
  if (xmlStrcmp (node->name, (const xmlChar*) ident) != 0) return NULL;

/*****************************************************************************/
/* Register                                                                  */
/*****************************************************************************/

XmlRegisterStore xml_register_store;

int xml_current_idx = 0;

void xml_delete_register_store()
{
  /* TODO */
}

RegisterExpr *xml_get_register(string ident)
{
  XmlRegisterStore::iterator reg = xml_register_store.find(ident);

  if (reg == xml_register_store.end())
    return NULL;
  else
    return reg->second;
}

void xml_reset_register_store()
{
  xml_register_store.clear();
};

void xml_declare_register(const string ident, int size)
{
  RegisterDesc * regdesc =
    new RegisterDesc(xml_current_idx++, ident, size);

  RegisterExpr *reg =
    RegisterExpr::create (regdesc, 0, size);

  xml_register_store[ident] = reg;
  XML_DBG("new register : %s\n", xml_get_register(ident)->pp());

  delete regdesc;
}

/*****************************************************************************/
/* Expressions                                                               */
/*****************************************************************************/

LValue *lvalue_of_xml(xmlNodePtr node);
Expr *expr_of_xml(xmlNodePtr node);
RegisterExpr *register_of_xml(xmlNodePtr node);
Constant *constant_of_xml(xmlNodePtr node);
MemCell *memcell_of_xml(xmlNodePtr node);
UnaryApp *unary_app_of_xml(xmlNodePtr node);
BinaryApp *binary_app_of_xml(xmlNodePtr node);

/*****************************************************************************/

UnaryOp unary_op_of_xml(xmlNodePtr node, char *ident)
{
  if (strcmp(ident, "not") == 0)
    return BV_OP_NOT;

  if (strcmp(ident, "minus") == 0)
    return BV_OP_NEG;

  XML_PARSE_ERROR(node, "unary operator %s unknown", ident);
}

UnaryApp *unary_app_of_xml(xmlNodePtr node)
{
  check_name(node, "apply");

  if (xml_child_nb(node) != 2)
    return NULL;

  Expr *arg = expr_of_xml(xml_nth_child(node, 1));

  return UnaryApp::create(unary_op_of_xml(node, (char *) xml_nth_child(node, 0)->name), arg);
}

/*****************************************************************************/

BinaryOp binary_op_of_xml(xmlNodePtr node, char *ident)
{
  if (strcmp(ident, "plus") == 0) return BV_OP_ADD;
  if (strcmp(ident, "minus") == 0) return BV_OP_SUB;
  if (strcmp(ident, "times_s") == 0) return BV_OP_MUL_S;
  if (strcmp(ident, "times_u") == 0) return BV_OP_MUL_U;
  if (strcmp(ident, "divs") == 0) return BV_OP_DIV_S;
  if (strcmp(ident, "divu") == 0) return BV_OP_DIV_U;
  if (strcmp(ident, "mods") == 0) return BV_OP_MODULO;
  if (strcmp(ident, "or") == 0) return BV_OP_OR;
  if (strcmp(ident, "and") == 0) return BV_OP_AND;
  if (strcmp(ident, "xor") == 0) return BV_OP_XOR;
  if (strcmp(ident, "concat") == 0) return BV_OP_CONCAT;
  if (strcmp(ident, "lshift") == 0) return BV_OP_LSH;
  if (strcmp(ident, "rshiftu") == 0) return BV_OP_RSH_U;
  if (strcmp(ident, "rshifts") == 0) return BV_OP_RSH_S;

  if (strcmp(ident, "eq") == 0) return BV_OP_EQ;
  if (strcmp(ident, "leqs") == 0) return BV_OP_LEQ_S;
  if (strcmp(ident, "lts") == 0) return BV_OP_LT_S;
  if (strcmp(ident, "lequ") == 0) return BV_OP_LEQ_U;
  if (strcmp(ident, "ltu") == 0) return BV_OP_LT_U;

  /* Not supported:
  if (strcmp(ident, "modu") == 0) return MODULO;
  <!ELEMENT rshifts EMPTY>
  <!ELEMENT exts EMPTY>
  <!ELEMENT extu EMPTY>
  <!ELEMENT lequ EMPTY>
  <!ELEMENT ltu EMPTY>
  */

  XML_PARSE_ERROR(node, "binary operator %s unknown", ident);
}

BinaryApp *binary_app_of_xml(xmlNodePtr node)
{
  check_name(node, "apply");
  if (xml_child_nb(node) != 3) return NULL;
  Expr *arg1 = expr_of_xml(xml_nth_child(node, 1));
  Expr *arg2 = expr_of_xml(xml_nth_child(node, 2));
  return BinaryApp::create (binary_op_of_xml(node, (char *) xml_nth_child(node, 0)->name), arg1, arg2);
}

/*****************************************************************************/

RegisterExpr *register_of_xml(xmlNodePtr node)
{
  check_name(node, "var");
  RegisterExpr *reg = xml_get_register(string(xml_get_attribute(node, "var")));
  if (reg == NULL) 
    XML_PARSE_ERROR(node, "register %s not declarated", 
		    xml_get_attribute(node, "var"));
  return (RegisterExpr *) reg->ref ();
}

/*****************************************************************************/

Constant *constant_of_xml(xmlNodePtr node)
{
  check_name(node, "const");
  char *val = xml_get_text(node);
  if (val == NULL)
    XML_PARSE_ERROR(node, "const with no value");
  Constant *cst = Constant::create (atoi(val), 0, 
			       xml_get_int_attribute(node, "size"));

  return cst;
}

/*****************************************************************************/

MemCell *memcell_of_xml(xmlNodePtr node)
{
  check_name(node, "memref");
  char *tag;
  if (xml_has_attribute(node, "mem"))
    tag = xml_get_attribute(node, "mem");
  else
    tag = (char *) "";

  // TODO: endianness

  Expr *addr = expr_of_xml(node->children);
  MemCell *m = MemCell::create (addr, string(tag),  
			   xml_get_int_attribute(node, "size"));
  return m;
}

/*****************************************************************************/

LValue *lvalue_of_xml(xmlNodePtr node)
{
  LValue *e;
  if ((e = register_of_xml(node)) != NULL) return e;
  if ((e = memcell_of_xml(node)) != NULL) return e;
  return NULL;
}

/*****************************************************************************/

Expr *expr_of_xml(xmlNodePtr node)
{
  Expr *e;
  if ((e = constant_of_xml(node)) != NULL) return e;
  if ((e = binary_app_of_xml(node)) != NULL) return e;
  if ((e = unary_app_of_xml(node)) != NULL) return e;
  if ((e = lvalue_of_xml(node)) != NULL) return e;
  return NULL;
}

/*****************************************************************************/
// Statements
/*****************************************************************************/

MicrocodeAddress extract_microcode_address_attribute(xmlNodePtr node, const char *id)
{
  char *attr;

  if ((attr = (char *) xmlGetProp(node, (const xmlChar *) id)) == NULL)
    XML_PARSE_ERROR(node, "extract_loc_of_xml:: cannot find the location (%s)", id);

  if (attr[0] != 'x')
    XML_PARSE_ERROR(node,
		    "extract_loc_of_xml:: expecting hexadecimal form \"xGLOBAL-LOCAL\" (miss the 'x')");

  int idx = 1;
  while (attr[idx] != 0 && attr[idx] != '-') idx++;
  if (attr[idx] == 0)
    XML_PARSE_ERROR(node,
		    "extract_loc_of_xml:: expecting hexadecimal form \"xGLOBAL-LOCAL\" (miss the '-')");

  attr[idx] = 0;
  return MicrocodeAddress(parse_hexadecimal(&attr[1]),
			  parse_hexadecimal(&attr[idx + 1]));
}

/*****************************************************************************/

MicrocodeNode *xml_parse_assign(xmlNodePtr node)
{
  check_name(node, "assign");

  MicrocodeAddress origin = extract_microcode_address_attribute(node, "id");
  MicrocodeAddress target = extract_microcode_address_attribute(node, "next");

  LValue *lv = lvalue_of_xml(xml_nth_child(node, 0));

  if (lv == NULL)
    XML_PARSE_ERROR(node,
		    "xml_parse_assign:: expecting a lvalue as first child");

  Expr *e = expr_of_xml(xml_nth_child(node, 1));
  if (e == NULL)
    XML_PARSE_ERROR(node,
		    "xml_parse_assign:: expecting an expression as second child");

  StaticArrow *arr =
    new StaticArrow(origin, target, new Assignment(lv, e), Constant::create (1));

  return new MicrocodeNode(origin, arr);
}

/*****************************************************************************/

StaticArrow *xml_parse_guard(MicrocodeAddress origin, xmlNodePtr node)
{
  check_name(node, "guard");
  MicrocodeAddress target =
    extract_microcode_address_attribute(node, "next");

  if (xml_child_nb(node) != 1)
    XML_PARSE_ERROR(node, "xml_parse_guard:: guard expects 1 xml child");

  Expr *cond = expr_of_xml(xml_nth_child(node, 0));

  if (cond == NULL)
    XML_PARSE_ERROR(node,
		    "xml_parse_guard:: expecting an expression for the condition");

  return new StaticArrow(origin, target, new Skip(), cond);
}

MicrocodeNode *xml_parse_switch(xmlNodePtr node)
{
  check_name(node, "switch");

  MicrocodeAddress origin = extract_microcode_address_attribute(node, "id");

  int n = xml_child_nb(node);
  vector<StmtArrow *> * arrow_list = new vector<StmtArrow *>();
  for (int c = 0; c < n; c++)
    {
      StaticArrow *arr = xml_parse_guard(origin, xml_nth_child(node, c));
      if (arr == NULL)
	XML_PARSE_ERROR(node, "xml_parse_switch:: expecting a guard expression");

      arrow_list->push_back(arr);
    }

  return new MicrocodeNode(origin, arrow_list);
}

/*****************************************************************************/

MicrocodeNode *xml_parse_jump(xmlNodePtr node)
{
  check_name(node, "jump");

  MicrocodeAddress origin = extract_microcode_address_attribute(node, "id");

  // static jump
  if (xml_has_attribute(node, "next"))
    {
      MicrocodeAddress target = extract_microcode_address_attribute(node, "next");
      return new MicrocodeNode(origin, new StaticArrow(origin, target, new Skip(), Constant::create (1)));
    }

  else   // dynamic jump
    {
      if (xml_child_nb(node) != 1)
	XML_PARSE_ERROR(node, "xml_parse_jump:: dynamic jump expects 1 xml child");

      Expr *e = expr_of_xml(xml_nth_child(node, 0));

      if (e == NULL)
	XML_PARSE_ERROR(node, "xml_parse_jump:: dynamic jump expects an expression as child");

      return new MicrocodeNode(origin,
			       new DynamicArrow(origin, e, new Skip(), Constant::create (1)));
    }
}

/*****************************************************************************/

MicrocodeNode *MicrocodeNode_of_xml(xmlNodePtr node)
{

  MicrocodeNode *elt;

  if ((elt = xml_parse_assign(node)) != NULL) return elt;
  if ((elt = xml_parse_switch(node)) != NULL) return elt;
  if ((elt = xml_parse_jump(node)) != NULL) return elt;

  return NULL;
}

/*****************************************************************************/
/*****************************************************************************/

void prefix_run(xmlNodePtr node, vector<MicrocodeNode *> * elts)
{

  xmlNodePtr n;
  MicrocodeNode *elt;
  for (n = node; n != NULL; n = n->next)
    {

      if (!xmlStrcmp(n->name, (const xmlChar *) "vardecl"))
        xml_declare_register(xml_get_attribute(n, "id"),
			     xml_get_int_attribute(n, "size"));

      if ((elt = MicrocodeNode_of_xml(n)) != NULL)
	elts->push_back(elt);

      if ((n->type == XML_ELEMENT_NODE) && (n->children != NULL))
        prefix_run(n->children, elts);
    }

}

/*****************************************************************************/

Microcode *
xml_parse_mc_program(const string filename)
{

  XML_DBG("--------------------------------------------\n");
  XML_DBG("Parsing Microcode from xml file %s\n", filename);
  XML_DBG("--------------------------------------------\n");

  pair<xmlDocPtr, xmlNodePtr>
    xml_doc_handler = xml_get_root_from_file(filename.c_str());

  xmlNodePtr root = xml_doc_handler.second;
  vector<MicrocodeNode *> * elts = new vector<MicrocodeNode *>();

  xml_reset_register_store();
  prefix_run(root, elts);
  delete xml_doc_handler.first;
  xml_delete_register_store();

  XML_DBG("--------------------------------------------\n");
  XML_DBG("Parsing process successfull : %d nodes\n", (int) elts->size());
  XML_DBG("--------------------------------------------\n");

  if (elts->size() == 0)
    {
      Log::warning ("xml_parse_mc_program:: empty program !");
      return new Microcode(elts, MicrocodeAddress(0, 0));
    }

  Microcode *the_prg = new Microcode(elts, (*elts)[0]->get_loc());
  the_prg->regular_form();
  return the_prg;
}

/*****************************************************************************/
/*****************************************************************************/

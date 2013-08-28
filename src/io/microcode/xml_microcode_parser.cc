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
#include <cassert>
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

struct ParserData
{
  Microcode *mc;
  MicrocodeArchitecture *mcArch;
  const string &filename;
  std::ostream &error (xmlNodePtr node) {
    logs::error << filename << ":" << node->line << ": error:";
    return logs::error;
  }
};

/*****************************************************************************/
/* Tools                                                                     */
/*****************************************************************************/

#define XML_PARSER_DEBUG_MODE 0

/*****************************************************************************/

int parse_hexadecimal(char *str)
{
  std::string s(str);
  uint32_t v;
  std::istringstream iss(s);
  iss >> std::setbase(16) >> v;
  return v;
}

static pair<xmlDocPtr, xmlNodePtr> 
s_xml_get_root_from_file (const string filename)
{
  xmlDocPtr doc;
  xmlNodePtr root;

  xmlKeepBlanksDefault(0);
  doc = xmlParseFile(filename.c_str());
  if (doc == NULL)
    logs::fatal_error("Xml Document XML not valid\n");

  root = xmlDocGetRootElement(doc);
  if (root == NULL)
    {
      xmlFreeDoc(doc);
      logs::fatal_error("XML Document empty\n");
    }

  return pair<xmlDocPtr, xmlNodePtr> (doc, root);
}

static bool 
s_xml_has_attribute (xmlNodePtr node, const char *id)
{
  return xmlGetProp(node, (const xmlChar *) id) != NULL;
}

static char *
s_xml_get_attribute (xmlNodePtr node, const char *attribute_id, 
		     ParserData &data)
{
  char *val;
  if ((val = (char *) xmlGetProp(node, (const xmlChar *) attribute_id)) == NULL)
    data.error (node) << "expecting " << attribute_id << " attribute." << endl;

  return val;
}

static int 
s_xml_get_int_attribute (xmlNodePtr node, const char *attribute_id, 
			 ParserData &data)
{
  return atoi (s_xml_get_attribute (node, attribute_id, data));
}

static char *
s_xml_get_text(xmlNodePtr node)
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

static xmlNodePtr 
s_xml_nth_child(xmlNodePtr node, int n)
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

static int 
s_xml_child_nb (xmlNodePtr node)
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
/* Expressions                                                               */
/*****************************************************************************/


static Expr * 
s_expr_of_xml(xmlNodePtr node, ParserData &data);

static UnaryOp 
s_unary_op_of_xml (xmlNodePtr node, char *ident, ParserData &data)
{
  if (strcmp(ident, "not") == 0)
    return BV_OP_NOT;

  if (strcmp(ident, "minus") == 0)
    return BV_OP_NEG;
  
  data.error (node) << "unary operator " << ident << " unknown." << endl;
}

static UnaryApp * 
s_unary_app_of_xml (xmlNodePtr node, ParserData &data)
{
  check_name(node, "apply");

  if (s_xml_child_nb (node) != 2)
    return NULL;

  Expr *arg = s_expr_of_xml (s_xml_nth_child (node, 1), data);
  UnaryOp op = s_unary_op_of_xml (node, 
				  (char *) s_xml_nth_child (node, 0)->name,
				  data);

  return UnaryApp::create (op, arg);
}

/*****************************************************************************/

static BinaryOp 
s_binary_op_of_xml (xmlNodePtr node, char *ident, ParserData &data)
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

  data.error (node) << "binary operator " << ident << "is unknown." << endl;
}

static BinaryApp * 
s_binary_app_of_xml (xmlNodePtr node, ParserData &data)
{
  check_name(node, "apply");
  if (s_xml_child_nb (node) != 3) return NULL;
  Expr *arg1 = s_expr_of_xml(s_xml_nth_child (node, 1), data);
  Expr *arg2 = s_expr_of_xml(s_xml_nth_child (node, 2), data);
  BinaryOp op = 
    s_binary_op_of_xml (node, (char *) s_xml_nth_child (node, 0)->name, data);

  return BinaryApp::create (op, arg1, arg2);
}

/*****************************************************************************/

static RegisterExpr *
s_register_of_xml (xmlNodePtr node, ParserData &data)
{
  check_name(node, "var");
  string regname (s_xml_get_attribute (node, "var", data));
  const RegisterDesc *rdesc = data.mcArch->get_register (regname);
  if (rdesc == NULL) 
    data.error (node) << "register " << regname << " not declared." << endl;

  return RegisterExpr::create (rdesc);
}

/*****************************************************************************/

static Constant *
s_constant_of_xml (xmlNodePtr node, ParserData &data)
{
  check_name(node, "const");
  char *val = s_xml_get_text (node);
  if (val == NULL)
    data.error (node) << "const with no value." << endl;
  int size = s_xml_get_int_attribute (node, "size", data);
  Constant *cst = Constant::create (atoi(val), 0, size);

  return cst;
}

/*****************************************************************************/

static MemCell *
s_memcell_of_xml (xmlNodePtr node, ParserData &data)
{
  check_name(node, "memref");
  char *tag;
  if (s_xml_has_attribute (node, "mem"))
    tag = s_xml_get_attribute (node, "mem", data);
  else
    tag = (char *) "";

  // TODO: endianness

  Expr *addr = s_expr_of_xml(node->children, data);
  int size = s_xml_get_int_attribute (node, "size", data);
  MemCell *m = MemCell::create (addr, string(tag), 0, size);

  return m;
}

/*****************************************************************************/

static LValue * 
s_lvalue_of_xml (xmlNodePtr node, ParserData &data)
{
  LValue *e = s_register_of_xml (node, data);

  if (e == NULL)
    e = s_memcell_of_xml (node, data);
  return e;
}

/*****************************************************************************/

static Expr * 
s_expr_of_xml (xmlNodePtr node, ParserData &data)
{
  Expr *e;

  if ((e = s_constant_of_xml (node, data)) != NULL) return e;
  if ((e = s_binary_app_of_xml (node, data)) != NULL) return e;
  if ((e = s_unary_app_of_xml (node, data)) != NULL) return e;
  if ((e = s_lvalue_of_xml (node, data)) != NULL) return e;

  return NULL;
}

/*****************************************************************************/
// Statements
/*****************************************************************************/

static MicrocodeAddress 
s_extract_microcode_address_attribute(xmlNodePtr node, const char *id,
				      ParserData &data)
{
  char *attr;

  if ((attr = (char *) xmlGetProp(node, (const xmlChar *) id)) == NULL)
    data.error (node) << "extract_loc_of_xml:: cannot find the location ("
		      << id << ")." << endl;

  if (attr[0] != 'x')
    data.error (node) << "extract_loc_of_xml:: expecting hexadecimal form "
      "\"xGLOBAL-LOCAL\" (miss the 'x')." << endl;

  int idx = 1;
  while (attr[idx] != 0 && attr[idx] != '-') idx++;
  if (attr[idx] == 0)
    data.error (node) 
      << "extract_loc_of_xml:: expecting hexadecimal form \"xGLOBAL-LOCAL\" "
      << "(miss the '-')." << endl;

  attr[idx] = 0;
  return MicrocodeAddress (parse_hexadecimal(&attr[1]),
			   parse_hexadecimal(&attr[idx + 1]));
}

/*****************************************************************************/

static MicrocodeNode * 
s_xml_parse_assign (xmlNodePtr node, ParserData &data)
{
  check_name(node, "assign");

  MicrocodeAddress origin = 
    s_extract_microcode_address_attribute (node, "id", data);
  MicrocodeAddress target = 
    s_extract_microcode_address_attribute (node, "next", data);

  LValue *lv = s_lvalue_of_xml (s_xml_nth_child (node, 0), data);

  if (lv == NULL)
    data.error (node) 
      << "xml_parse_assign:: expecting a lvalue as first child." << endl;

  Expr *e = s_expr_of_xml (s_xml_nth_child (node, 1), data);
  if (e == NULL)
    data.error (node) 
      << "xml_parse_assign:: expecting an expression as second child." << endl;

  StaticArrow *arr =
    new StaticArrow(origin, target, new Assignment(lv, e), Constant::True ());

  return new MicrocodeNode(origin, arr);
}

/*****************************************************************************/

static StaticArrow * 
s_xml_parse_guard (MicrocodeAddress origin, xmlNodePtr node, ParserData &data)
{
  check_name (node, "guard");
  MicrocodeAddress target =
    s_extract_microcode_address_attribute (node, "next", data);

  if (s_xml_child_nb (node) != 1)
    data.error (node) << "xml_parse_guard:: guard expects 1 xml child." << endl;

  Expr *cond = s_expr_of_xml (s_xml_nth_child (node, 0), data);

  if (cond == NULL)
    data.error (node) 
      << "xml_parse_guard:: expecting an expression for the condition." << endl;

  return new StaticArrow(origin, target, new Skip(), cond);
}

static MicrocodeNode *
s_xml_parse_switch (xmlNodePtr node, ParserData &data)
{
  check_name (node, "switch");

  MicrocodeAddress origin = 
    s_extract_microcode_address_attribute (node, "id", data);

  int n = s_xml_child_nb (node);
  vector<StmtArrow *> * arrow_list = new vector<StmtArrow *>();
  for (int c = 0; c < n; c++)
    {
      StaticArrow *arr = 
	s_xml_parse_guard (origin, s_xml_nth_child (node, c), data);
      if (arr == NULL)
	data.error (node) 
	  << "xml_parse_switch:: expecting a guard expression" << endl;

      arrow_list->push_back(arr);
    }

  return new MicrocodeNode(origin, arrow_list);
}

/*****************************************************************************/

static MicrocodeNode *
s_xml_parse_jump (xmlNodePtr node, ParserData &data)
{
  check_name(node, "jump");

  MicrocodeAddress origin = 
    s_extract_microcode_address_attribute (node, "id", data);

  // static jump
  if (s_xml_has_attribute(node, "next"))
    {
      MicrocodeAddress target = 
	s_extract_microcode_address_attribute(node, "next", data);
      return new MicrocodeNode(origin, new StaticArrow(origin, target, new Skip(), Constant::True ()));
    }

  else   // dynamic jump
    {
      if (s_xml_child_nb (node) != 1)
	data.error (node) 
	  << "xml_parse_jump:: dynamic jump expects 1 xml child." << endl;

      Expr *e = s_expr_of_xml (s_xml_nth_child (node, 0), data);

      if (e == NULL)
	data.error (node) 
	  << "xml_parse_jump:: dynamic jump expects an expression as child."
	  << endl;

      return new MicrocodeNode(origin,
			       new DynamicArrow(origin, e, new Skip(), Constant::True ()));
    }
}

/*****************************************************************************/

static MicrocodeNode * 
s_MicrocodeNode_of_xml (xmlNodePtr node, ParserData &data)
{

  MicrocodeNode *elt;

  if ((elt = s_xml_parse_assign (node, data)) != NULL) return elt;
  if ((elt = s_xml_parse_switch (node, data)) != NULL) return elt;
  if ((elt = s_xml_parse_jump (node, data)) != NULL) return elt;

  return NULL;
}

/*****************************************************************************/
/*****************************************************************************/

static void 
s_prefix_run (xmlNodePtr node, ParserData &data)
{
  xmlNodePtr n;

  for (n = node; n != NULL; n = n->next)
    {
      if (!xmlStrcmp(n->name, (const xmlChar *) "vardecl"))
	{
	  string regname = s_xml_get_attribute (n, "id", data);
	  int size = s_xml_get_int_attribute (n, "size", data);
	  if (data.mcArch->get_reference_arch ()->has_register (regname))
	    {
	      const RegisterDesc *rdesc = 
		data.mcArch->get_reference_arch ()->get_register (regname);
	      assert (rdesc->get_register_size () == size);
	    }
	  else if (! data.mcArch->has_tmp_register (regname))
	    data.mcArch->add_tmp_register (regname, size);
	}
      else
	{
	  MicrocodeNode *elt = s_MicrocodeNode_of_xml (n, data);
	  if (elt != NULL)
	    data.mc->add_node (elt);

	}
    }
}

/*****************************************************************************/

Microcode *
xml_parse_mc_program(const string &filename, MicrocodeArchitecture *arch)
{
  ParserData data = { new Microcode (), arch, filename };

  logs::debug << "--------------------------------------------" << endl
	     << "Parsing Microcode from xml file " << filename << endl
	     << "--------------------------------------------" << endl;

  pair<xmlDocPtr, xmlNodePtr>
    xml_doc_handler = s_xml_get_root_from_file (filename.c_str ());

  xmlNodePtr root = xml_doc_handler.second;

  s_prefix_run (root->children, data);
  delete xml_doc_handler.first;

  logs::debug << "--------------------------------------------" << endl
	     << "Parsing process successfull" << endl
	     << "--------------------------------------------" << endl;

  data.mc->regular_form ();

  return data.mc;
}

/*****************************************************************************/
/*****************************************************************************/

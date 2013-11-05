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
  ostringstream oss;

  ParserData (Microcode *mc, MicrocodeArchitecture *mcArch, 
	      const string &filename) : mc (mc), mcArch (mcArch), 
					filename (filename), oss () { }

  std::ostream &error (xmlNodePtr node) {    
    oss << filename << ": ";
    if (node != NULL)
      oss << node->line << ": ";
    oss << "error: ";

    return oss;
  }
};

#define RAISE_ERROR(data) \
  do { throw XmlParserException ((data).oss.str ()); } while (0)

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
  throw (XmlParserException)
{
  xmlKeepBlanksDefault (0);
  xmlDocPtr doc = xmlParseFile (filename.c_str ());
  if (doc == NULL)
    throw XmlParserException ("while loading file.");

  xmlNodePtr root = xmlDocGetRootElement (doc);
  if (root == NULL)
    {
      xmlFreeDoc (doc);
      throw XmlParserException ("empty XML document.");
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
  throw (XmlParserException)
{
  char *val = (char *) xmlGetProp (node, (const xmlChar *) attribute_id);

  if (val == NULL)
    {
      data.error (node) << "expecting " << attribute_id << " attribute.";
      RAISE_ERROR (data);
    }

  return val;
}

static int 
s_xml_get_int_attribute (xmlNodePtr node, const char *attribute_id, 
			 ParserData &data)
  throw (XmlParserException)
{
  return atoi (s_xml_get_attribute (node, attribute_id, data));
}

static char *
s_xml_get_text (xmlNodePtr node)
{
  if (node->children != NULL && node->children->type == XML_TEXT_NODE)
    {
      xmlChar *content = xmlNodeGetContent (node);
      char *result = strdup ((char *) content);
      xmlFree (content);

      return result;
    }

  return NULL;
}

static xmlNodePtr 
s_xml_nth_child (xmlNodePtr node, int n)
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

#define return_if_not_named(node, ident) \
  if (xmlStrcmp (node->name, (const xmlChar*) ident) != 0) return NULL;

#define assert_name(node, ident) \
  assert (xmlStrcmp (node->name, (const xmlChar*) ident) == 0);

/*****************************************************************************/
/* Expressions                                                               */
/*****************************************************************************/


static Expr * 
s_expr_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException);

static UnaryOp 
s_unary_op_of_xml (xmlNodePtr node, char *ident, ParserData &data)
  throw (XmlParserException)
{
  if (strcmp(ident, "not") == 0)
    return BV_OP_NOT;

  if (strcmp(ident, "minus") == 0)
    return BV_OP_NEG;
  
  data.error (node) << "unary operator " << ident << " unknown.";
  throw XmlParserException (data.oss.str ());
}

static UnaryApp * 
s_unary_app_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  assert_name (node, "apply");
  assert (s_xml_child_nb (node) == 2);

  UnaryOp op = 
    s_unary_op_of_xml (node, (char *) s_xml_nth_child (node, 0)->name,
		       data);
  int offset = s_xml_get_int_attribute (node, "offset", data);
  int size = s_xml_get_int_attribute (node, "size", data);
  Expr *arg = s_expr_of_xml (s_xml_nth_child (node, 1), data);

  return UnaryApp::create (op, arg, offset, size);
}

/*****************************************************************************/

static BinaryOp 
s_binary_op_of_xml (xmlNodePtr node, char *ident, ParserData &data)
  throw (XmlParserException)
{
  if (strcmp (ident, "plus") == 0) return BV_OP_ADD;
  if (strcmp (ident, "minus") == 0) return BV_OP_SUB;
  if (strcmp (ident, "times_s") == 0) return BV_OP_MUL_S;
  if (strcmp (ident, "times_u") == 0) return BV_OP_MUL_U;
  if (strcmp (ident, "divs") == 0) return BV_OP_DIV_S;
  if (strcmp (ident, "divu") == 0) return BV_OP_DIV_U;
  if (strcmp (ident, "mods") == 0) return BV_OP_MODULO;
  if (strcmp (ident, "or") == 0) return BV_OP_OR;
  if (strcmp (ident, "and") == 0) return BV_OP_AND;
  if (strcmp (ident, "xor") == 0) return BV_OP_XOR;
  if (strcmp (ident, "concat") == 0) return BV_OP_CONCAT;
  if (strcmp (ident, "lshift") == 0) return BV_OP_LSH;
  if (strcmp (ident, "rshiftu") == 0) return BV_OP_RSH_U;
  if (strcmp (ident, "rshifts") == 0) return BV_OP_RSH_S;

  if (strcmp (ident, "eq") == 0) return BV_OP_EQ;
  if (strcmp (ident, "neq") == 0) return BV_OP_NEQ;
  if (strcmp (ident, "leqs") == 0) return BV_OP_LEQ_S;
  if (strcmp (ident, "lts") == 0) return BV_OP_LT_S;
  if (strcmp (ident, "lequ") == 0) return BV_OP_LEQ_U;
  if (strcmp (ident, "ltu") == 0) return BV_OP_LT_U;

  if (strcmp (ident, "geqs") == 0) return BV_OP_GEQ_S;
  if (strcmp (ident, "gts") == 0) return BV_OP_GT_S;
  if (strcmp (ident, "gequ") == 0) return BV_OP_GEQ_U;
  if (strcmp (ident, "gtu") == 0) return BV_OP_GT_U;

  if (strcmp (ident, "exts") == 0) return BV_OP_EXTEND_S;
  if (strcmp (ident, "extu") == 0) return BV_OP_EXTEND_U;

  data.error (node) << "binary operator " << ident << " is unknown.";
  RAISE_ERROR (data);
}

static BinaryApp * 
s_binary_app_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  assert_name (node, "apply");
  assert (s_xml_child_nb (node) == 3);
 
  BinaryOp op = 
    s_binary_op_of_xml (node, (char *) s_xml_nth_child (node, 0)->name, data);
  int offset = s_xml_get_int_attribute (node, "offset", data);
  int size = s_xml_get_int_attribute (node, "size", data);
  Expr *arg1 = s_expr_of_xml(s_xml_nth_child (node, 1), data);

  try {
    Expr *arg2 = s_expr_of_xml(s_xml_nth_child (node, 2), data);

    return BinaryApp::create (op, arg1, arg2, offset, size);
  } catch (XmlParserException) {
    arg1->deref ();
    throw;
  }    
}

static TernaryOp 
s_ternary_op_of_xml (xmlNodePtr node, char *ident, ParserData &data)
  throw (XmlParserException)
{
  if (strcmp (ident, "extract") == 0) return BV_OP_EXTRACT;
    
  data.error (node) << "ternary operator " << ident << " is unknown.";
  RAISE_ERROR (data);
}

static TernaryApp * 
s_ternary_app_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  assert_name(node, "apply");
  assert (s_xml_child_nb (node) == 4);
  TernaryOp op = 
    s_ternary_op_of_xml (node, (char *) s_xml_nth_child (node, 0)->name, data);
  int offset = s_xml_get_int_attribute (node, "offset", data);
  int size = s_xml_get_int_attribute (node, "size", data);
  Expr *args[] = { NULL, NULL, NULL }; 

  try 
    {  
      args[0] = s_expr_of_xml(s_xml_nth_child (node, 1), data);
      args[1] = s_expr_of_xml(s_xml_nth_child (node, 2), data);
      args[2] = s_expr_of_xml(s_xml_nth_child (node, 3), data);
      return TernaryApp::create (op, args[0], args[1], args[2], offset, size);
    }
  catch (XmlParserException)
    {
      if (args[0])
	args[0]->deref ();
      if (args[1])
	args[1]->deref ();
      assert (args[2] == NULL);
      throw;
    }
}

static Expr * 
s_apply_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named (node, "apply");
  switch (s_xml_child_nb (node))
    {
    case 2: 
      return s_unary_app_of_xml (node, data);
    case 3:
      return s_binary_app_of_xml (node, data);
    case 4:
      return s_ternary_app_of_xml (node, data);
      break;
    }
  data.error (node) << "invalid apply node.";
  RAISE_ERROR (data);
}

/*****************************************************************************/

static RegisterExpr *
s_register_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named(node, "var");

  string regname (s_xml_get_attribute (node, "var", data));
  const RegisterDesc *rdesc = data.mcArch->get_register (regname);
  if (rdesc == NULL) 
    {
      data.error (node) << "register " << regname << " not declared.";
      RAISE_ERROR (data);
    }

  int offset, size;
  if (s_xml_has_attribute (node, "size"))
    {
      size = s_xml_get_int_attribute (node, "size", data);
      offset = s_xml_get_int_attribute (node, "offset", data);
    }
  else if (! rdesc->is_alias ())
    {      
      size = rdesc->get_register_size ();
      offset = 0;
    }
  else
    {
      data.error (node) << "alias registers are not allowed.";
      RAISE_ERROR (data);
    }

  return RegisterExpr::create (rdesc, offset, size);
}

/*****************************************************************************/

static Constant *
s_constant_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named (node, "const");

  int offset = s_xml_get_int_attribute (node, "offset", data);
  int size = s_xml_get_int_attribute (node, "size", data);
  char *val = s_xml_get_text (node);
  if (val == NULL)
    {
      data.error (node) << "const with no value.";
      RAISE_ERROR (data);
    }

  Constant *cst = Constant::create (atoi (val), offset, size);

  return cst;
}

static RandomValue *
s_random_value_of_xml (xmlNodePtr node, ParserData &data) 
  throw (XmlParserException)
{
  return_if_not_named (node, "random");
  int size = s_xml_get_int_attribute (node, "size", data);
  RandomValue *r = RandomValue::create (size);

  return r;
}

/*****************************************************************************/

static MemCell *
s_memcell_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named (node, "memref");

  char *tag;
  if (s_xml_has_attribute (node, "mem"))
    tag = s_xml_get_attribute (node, "mem", data);
  else
    tag = (char *) "";

  // TODO: endianness
  int offset = s_xml_get_int_attribute (node, "offset", data);
  int size = s_xml_get_int_attribute (node, "size", data);
  Expr *addr = s_expr_of_xml (node->children, data);

  MemCell *m = MemCell::create (addr, tag, offset, size);

  return m;
}

/*****************************************************************************/

static LValue * 
s_lvalue_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  LValue *e = s_register_of_xml (node, data);

  if (e == NULL)
    e = s_memcell_of_xml (node, data);
  return e;
}

/*****************************************************************************/

static Expr * 
s_expr_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  Expr *e;

  if ((e = s_constant_of_xml (node, data)) != NULL) return e;
  if ((e = s_random_value_of_xml (node, data)) != NULL) return e;
  if ((e = s_apply_of_xml (node, data)) != NULL) return e;
  if ((e = s_lvalue_of_xml (node, data)) != NULL) return e;

  return NULL;
}

/*****************************************************************************/
// Statements
/*****************************************************************************/

static MicrocodeAddress 
s_extract_microcode_address_attribute(xmlNodePtr node, const char *id,
				      ParserData &data)
  throw (XmlParserException)
{
  char *attr = (char *) xmlGetProp(node, (const xmlChar *) id);

  if (attr == NULL)
    {
      data.error (node) << "extract_loc_of_xml:: cannot find the location ("
			<< id << ").";
      RAISE_ERROR (data);
    }

  if (attr[0] != 'x')
    {
      data.error (node) << "extract_loc_of_xml:: expecting hexadecimal form "
	"\"xGLOBAL-LOCAL\" (miss the 'x').";
      RAISE_ERROR (data);
    }

  int idx = 1;
  while (attr[idx] != 0 && attr[idx] != '-') 
    idx++;
  if (attr[idx] == 0)
    {
      data.error (node) 
	<< "extract_loc_of_xml:: expecting hexadecimal form \"xGLOBAL-LOCAL\" "
	<< "(miss the '-').";
      RAISE_ERROR (data);
    }

  attr[idx] = 0;
  return MicrocodeAddress (parse_hexadecimal(&attr[1]),
			   parse_hexadecimal(&attr[idx + 1]));
}

/*****************************************************************************/

static MicrocodeNode * 
s_xml_parse_assign (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named(node, "assign");

  MicrocodeAddress origin = 
    s_extract_microcode_address_attribute (node, "id", data);
  MicrocodeAddress target = 
    s_extract_microcode_address_attribute (node, "next", data);

  LValue *lv = s_lvalue_of_xml (s_xml_nth_child (node, 0), data);

  if (lv == NULL)
    {
      data.error (node) 
	<< "xml_parse_assign:: expecting a lvalue as first child." << endl;
      RAISE_ERROR (data);
    }

  try
    {
      Expr *e = s_expr_of_xml (s_xml_nth_child (node, 1), data);
      if (e == NULL)
	{
	  data.error (node) 
	    << "xml_parse_assign:: expecting an expression as second child." 
	    << endl;
	  RAISE_ERROR (data);
	}
      StaticArrow *arr =
	new StaticArrow(origin, target, new Assignment (lv, e), 
			Constant::True ());

      return new MicrocodeNode(origin, arr);
    }
  catch (XmlParserException)
    {
      lv->deref ();
      throw;
    }
}

/*****************************************************************************/

static StaticArrow * 
s_xml_parse_guard (MicrocodeAddress origin, xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named (node, "guard");
  MicrocodeAddress target =
    s_extract_microcode_address_attribute (node, "next", data);

  if (s_xml_child_nb (node) != 1)
    {
      data.error (node) << "xml_parse_guard:: guard expects 1 xml child.";
      RAISE_ERROR (data);
    }

  Expr *cond = s_expr_of_xml (s_xml_nth_child (node, 0), data);

  if (cond == NULL)
    {
      data.error (node) 
	<< "xml_parse_guard:: expecting an expression for the condition.";
      RAISE_ERROR (data);
    }

  return new StaticArrow(origin, target, new Skip(), cond);
}

static MicrocodeNode *
s_xml_parse_switch (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named (node, "switch");

  MicrocodeAddress origin = 
    s_extract_microcode_address_attribute (node, "id", data);

  int n = s_xml_child_nb (node);
  vector<StmtArrow *> * arrow_list = new vector<StmtArrow *> ();
  try 
    {
      for (int c = 0; c < n; c++)
	{
	  StaticArrow *arr = 
	    s_xml_parse_guard (origin, s_xml_nth_child (node, c), data);
	  if (arr == NULL)
	    {
	      data.error (node) 
		<< "xml_parse_switch:: expecting a guard expression";
	      RAISE_ERROR (data);
	    }
	  arrow_list->push_back (arr);
	}
      return new MicrocodeNode (origin, arrow_list);
    }
  catch (XmlParserException)
    {
      for (vector<StmtArrow *>::iterator i = arrow_list->begin ();
	   i != arrow_list->end (); i++)
	delete *i;
      delete arrow_list;
      throw;
    }
}

/*****************************************************************************/

static MicrocodeNode *
s_xml_parse_jump (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
{
  return_if_not_named (node, "jump");

  MicrocodeAddress origin = 
    s_extract_microcode_address_attribute (node, "id", data);

  // static jump
  if (s_xml_has_attribute (node, "next"))
    {
      MicrocodeAddress target = 
	s_extract_microcode_address_attribute (node, "next", data);

      return new MicrocodeNode (origin, 
				new StaticArrow (origin, target, 
						 new Skip (), 
						 Constant::True ()));
    }
  else   // dynamic jump
    {
      if (s_xml_child_nb (node) != 1)
	{
	  data.error (node) 
	    << "xml_parse_jump:: dynamic jump expects 1 xml child.";
	  RAISE_ERROR (data);
	}

      Expr *e = s_expr_of_xml (s_xml_nth_child (node, 0), data);

      if (e == NULL)
	{
	  data.error (node) 
	    << "xml_parse_jump:: dynamic jump expects an expression as child.";
	  RAISE_ERROR (data);
	}

      return new MicrocodeNode (origin,
				new DynamicArrow (origin, e, new Skip (), 
						  Constant::True ()));
    }
}

/*****************************************************************************/

static MicrocodeNode * 
s_MicrocodeNode_of_xml (xmlNodePtr node, ParserData &data)
  throw (XmlParserException)
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
      if (xmlStrcmp(n->name, (const xmlChar *) "vardecl") == 0)
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
	  assert (xmlStrcmp(n->name, (const xmlChar *) "code") == 0);
	  for (xmlNodePtr child = n->children; child; child = child->next)
	    {
	      MicrocodeNode *elt = s_MicrocodeNode_of_xml (child, data);
	      if (elt != NULL)
		data.mc->add_node (elt);
	    }
	}
    }
}

/*****************************************************************************/

Microcode *
xml_parse_mc_program(const string &filename, MicrocodeArchitecture *arch)
  throw (XmlParserException)
{
  pair<xmlDocPtr, xmlNodePtr> xml_doc_handler = 
    s_xml_get_root_from_file (filename.c_str ());
  ParserData data (new Microcode (), arch, filename);

  try 
    {
      xmlNodePtr root = xml_doc_handler.second;
      s_prefix_run (root->children, data);
    }
  catch (XmlParserException)
    {
      delete xml_doc_handler.first;
      delete data.mc;
      throw;
    }
  delete xml_doc_handler.first;

  data.mc->regular_form ();

  return data.mc;
}

/*****************************************************************************/
/*****************************************************************************/

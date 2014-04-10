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

#include <sstream>
#include <string>
#include <libxml2/libxml/tree.h>

#include <kernel/Microcode.hh>
#include <kernel/Expressions.hh>
#include "xml_annotations.hh"
#include "xml_microcode_generator.hh"

using namespace std;

static xmlNodePtr 
xml_of_expr (const Expr *expr);

static string
string_of_int(int n)
{
  ostringstream oss;
  oss << n;
  return oss.str();
}

static string
xml_of_mcaddress (const MicrocodeAddress &addr)
{  
  char glob[16], loc[16];
  sprintf(glob, "%X", addr.getGlobal());
  sprintf(loc, "%X", addr.getLocal());
  return "x" + string(glob) + "-" + string(loc);
}


static void
s_add_prop (xmlNodePtr node, const char *propid, const char *value)
{
  xmlNewProp (node, BAD_CAST propid, BAD_CAST value);
}

static void
s_add_prop (xmlNodePtr node, const char *propid, const string &value)
{
  s_add_prop (node, propid, value.c_str ());
}

static void
s_add_prop (xmlNodePtr node, const char *propid, int value)
{
  s_add_prop (node, propid, string_of_int (value));
}

static void
s_add_prop (xmlNodePtr node, const char *propid, bool value)
{
  s_add_prop (node, propid, value ? 1 : 0);
}

static void
s_add_prop (xmlNodePtr node, const char *propid, const MicrocodeAddress &addr)
{
  s_add_prop (node, propid, xml_of_mcaddress (addr));
}

/*
 * ANNOTATIONS
 */
static xmlNodePtr 
s_new_annotation_node (const string &id)
{
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST id.c_str ());

  return result;
}

static xmlNodePtr 
s_annotation_to_xml (const SolvedJmpAnnotation *a)
{
  xmlNodePtr result = s_new_annotation_node (a->ID);
  for (SolvedJmpAnnotation::const_iterator i = a->begin (); i != a->end ();
       i++)
    {      
      xmlNodePtr jmp = xmlNewChild (result, NULL, BAD_CAST "addr", NULL);
      assert (i->getLocal () == 0);
      s_add_prop (jmp, "value", *i);
    }

  return result;
}

static xmlNodePtr 
s_annotation_to_xml (const AsmAnnotation *a)
{
  xmlNodePtr result = s_new_annotation_node (a->ID);
  s_add_prop (result, "value", a->get_value ());

  return result;
}

static xmlNodePtr 
s_annotation_to_xml (const CallRetAnnotation *a)
{
  xmlNodePtr result = s_new_annotation_node (a->ID);
  bool is_call = a->is_call ();

  s_add_prop (result, "is-call", is_call);
  if (is_call)
    {
      xmlNodePtr target = xml_of_expr (a->get_target ());
      xmlAddChild (result, target);
    }

  return result;
}

static xmlNodePtr 
s_annotation_to_xml (const NextInstAnnotation *a)
{
  xmlNodePtr result = s_new_annotation_node (a->ID);

  s_add_prop (result, "value", a->get_value ());

  return result;
}

static void
s_add_annotations (xmlNodePtr parent, const Annotable *annotable, 
		   const MicrocodeAddress *location = NULL)
{
  const Annotable::AnnotationMap *annotations = annotable->get_annotations ();

  if (annotations->size () == 0)
    return;

  xmlNodePtr root = xmlNewChild (parent, NULL, BAD_CAST "annotations", NULL);
  if (location != NULL)
    s_add_prop (root, "addr", *location);

  vector<Annotable::AnnotationId> *ids = annotable->get_sorted_annotation_ids();
  for (vector<Annotable::AnnotationId>::const_iterator i = ids->begin();
       i != ids->end(); i++)
    {
      Annotable::AnnotationId id = *i;
      const Annotation *a = annotable->get_annotation(id);
      xmlNodePtr annotation;

      if (id == SolvedJmpAnnotation::ID)
	annotation = 
	  s_annotation_to_xml (dynamic_cast<const SolvedJmpAnnotation *> (a));
      else if (id == AsmAnnotation::ID)
	annotation = 
	  s_annotation_to_xml (dynamic_cast<const AsmAnnotation *> (a));
      else if (id == CallRetAnnotation::ID)
	annotation =
	  s_annotation_to_xml (dynamic_cast<const CallRetAnnotation *> (a));
      else if (id == NextInstAnnotation::ID)
	annotation =
	  s_annotation_to_xml (dynamic_cast<const NextInstAnnotation *> (a));
      else
	{
	  logs::warning << "translation of annotation type " << id << " is not "
			<< "implemented. " << endl;
	  continue;
	}
      xmlAddChild (root, annotation);
    }
  delete ids;
}

static void
s_generate_annotations_for_nodes (xmlNodePtr root, const Microcode *prg)
{
  xmlNodePtr annotations = 
    xmlNewChild (root, NULL, BAD_CAST "nodes-annotations", NULL);

  for (Microcode::const_node_iterator n = prg->begin_nodes (); 
       n != prg->end_nodes (); n++)
    s_add_annotations (annotations, *n, &((*n)->get_loc ()));
}

/*
 * EXPRESSIONS
 */
static xmlNodePtr 
xml_of_constant (const Constant *c)
{
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "const");
  int val = c->get_not_truncated_value ();
  xmlNodeAddContent (result, BAD_CAST string_of_int(val).c_str ());

  return result;
}

static xmlNodePtr 
xml_of_random_value (const RandomValue *)
{
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "random");

  return result;
}

static xmlNodePtr 
xml_of_variable (const Variable *v)
{
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "formalvar");
  s_add_prop (result, "id", v->get_id ());

  return result;
}

static xmlNodePtr 
xml_of_ternary_op (TernaryOp op)
{
  const char *opname;

  switch (op)
    {
    case BV_OP_EXTRACT: opname = "extract"; break;
    default: opname = NULL;
    }
 
  if (opname == NULL)
    logs::fatal_error("xml_of_ternary_op:: operator not supported");

  return xmlNewNode (NULL, BAD_CAST opname);
}

static xmlNodePtr 
xml_of_ternaryapp(const TernaryApp *b)
{
  xmlNodePtr arg1 = xml_of_expr (b->get_arg1 ());
  xmlNodePtr arg2 = xml_of_expr (b->get_arg2 ());
  xmlNodePtr arg3 = xml_of_expr (b->get_arg3 ());
  xmlNodePtr op = xml_of_ternary_op (b->get_op ());
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "apply");
  xmlAddChild (result, op);
  xmlAddChild (result, arg1);
  xmlAddChild (result, arg2);
  xmlAddChild (result, arg3);

  return result;
}

static xmlNodePtr 
xml_of_binary_op (BinaryOp op)
{
  const char *opname;

  switch (op)
    {
    case BV_OP_ADD: opname = "plus"; break;
    case BV_OP_SUB: opname = "minus"; break;
    case BV_OP_MUL_U: opname = "times_u"; break;
    case BV_OP_MUL_S: opname = "times_s"; break;
    case BV_OP_DIV_S: opname = "divs"; break;
    case BV_OP_DIV_U: opname = "divu"; break;
    case BV_OP_MODULO: opname = "mods"; break;
    case BV_OP_OR: opname = "or"; break;
    case BV_OP_AND: opname = "and"; break;
    case BV_OP_XOR: opname = "xor"; break;
    case BV_OP_CONCAT: opname = "concat"; break;
    case BV_OP_LSH: opname = "lshift"; break;
    case BV_OP_RSH_S: opname = "rshifts"; break;
    case BV_OP_RSH_U: opname = "rshiftu"; break;
    case BV_OP_EQ: opname = "eq"; break;
    case BV_OP_LEQ_U: opname = "lequ"; break;
    case BV_OP_LT_U: opname = "ltu"; break;
    case BV_OP_LEQ_S: opname = "leqs"; break;
    case BV_OP_LT_S: opname = "lts"; break;
    case BV_OP_NEQ: opname = "neq"; break;
    case BV_OP_GEQ_U: opname = "gequ"; break;
    case BV_OP_GT_U: opname = "gtu"; break;
    case BV_OP_GEQ_S: opname = "geqs"; break;
    case BV_OP_GT_S: opname = "gts"; break;
    case BV_OP_EXTEND_S: opname = "exts"; break;
    case BV_OP_EXTEND_U: opname = "extu"; break;
    default: opname = NULL; break;
    }
 
  if (opname == NULL)
    logs::fatal_error("xml_of_binary_op:: operator not supported");

  return xmlNewNode (NULL, BAD_CAST opname);
}


static xmlNodePtr 
xml_of_binaryapp(const BinaryApp *b)
{
  xmlNodePtr arg1 = xml_of_expr(b->get_arg1());
  xmlNodePtr arg2 = xml_of_expr(b->get_arg2());
  xmlNodePtr op = xml_of_binary_op (b->get_op ());
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "apply");
  xmlAddChild (result, op);
  xmlAddChild (result, arg1);
  xmlAddChild (result, arg2);

  return result;
}

static xmlNodePtr 
xml_of_unary_op (UnaryOp op)
{  
  const char *opname;

  switch (op)
    {
    case BV_OP_NOT: opname = "not"; break;
    case BV_OP_NEG: opname = "minus"; break;
    default: opname = NULL; break;
    }
  if (opname == NULL)
    logs::fatal_error("xml_of_unary_op:: operator not supported");
  return xmlNewNode (NULL, BAD_CAST opname);
}

static xmlNodePtr 
xml_of_unaryapp (const UnaryApp *u)
{ 
  xmlNodePtr arg1 = xml_of_expr (u->get_arg1 ());
  xmlNodePtr op = xml_of_unary_op (u->get_op ());
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "apply");
  xmlAddChild (result, op);
  xmlAddChild (result, arg1);

  return result;
}

static xmlNodePtr 
xml_of_register (const RegisterExpr *reg)
{
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "var");

  assert (reg->get_name().length () > 0);
  s_add_prop (result, "var", reg->get_descriptor()->get_label ());

  return result;
}

static xmlNodePtr 
xml_of_memcell (const MemCell *m)
{
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "memref");
  xmlNodePtr addr = xml_of_expr (m->get_addr());

  xmlAddChild (result, addr);
  string mem = string (m->get_tag ());

  if (mem.length() > 0)
    s_add_prop (result, "mem", mem);
  
  return result;
}

static xmlNodePtr 
xml_of_lvalue (const Expr *lv, bool with_bv = false)
{
  xmlNodePtr result;

  if (lv->is_MemCell ())
    result =  xml_of_memcell ((const MemCell *) lv);
  else if (lv->is_RegisterExpr ())
    result = xml_of_register ((const RegisterExpr *) lv);
  else 
    result = NULL;

  if (with_bv)
    {
      s_add_prop (result, "size", lv->get_bv_size ());
      s_add_prop (result, "offset", lv->get_bv_offset ());
    }
  if (result == NULL)
    logs::fatal_error("xml_of_lvalue:: lvalue type unknown");

  return result;
}

static xmlNodePtr 
xml_of_expr (const Expr *e)
{
  xmlNodePtr result;

  if (e->is_Variable ())
    result = xml_of_variable ((const Variable *) e);
  else if (e->is_Constant ())
    result = xml_of_constant ((const Constant *) e);
  else if (e->is_RandomValue ())
    result = xml_of_random_value ((const RandomValue *) e);
  else if (e->is_UnaryApp ())
    result = xml_of_unaryapp ((const UnaryApp *) e);
  else if (e->is_BinaryApp ())
    result = xml_of_binaryapp ((const BinaryApp *) e);
  else if (e->is_LValue ())
    result = xml_of_lvalue ((const LValue *) e);
  else if (e->is_TernaryApp ())
    result = xml_of_ternaryapp ((const TernaryApp *) e);
  else 
    result = NULL;
  s_add_prop (result, "size", e->get_bv_size ());
  s_add_prop (result, "offset", e->get_bv_offset ());

  if (result == NULL)
    logs::fatal_error ("xml_of_expr:: expr type unknown");
  
  return result;
}

static xmlNodePtr 
xml_guard_of_static_arrow (const StaticArrow *arr)
{
  xmlNodePtr result = xmlNewNode (NULL, BAD_CAST "guard");
  xmlNodePtr g = xml_of_expr (arr->get_condition ());
  xmlAddChild (result, g);
  s_add_prop (result, "next", arr->get_target ());

  return result;
}

static void
xml_of_stmtarrow (xmlNodePtr root, const StmtArrow *arr)
{
  string new_stmtarrow("");

  if (!(arr->is_dynamic()))
    {
      StaticArrow *sarr = (StaticArrow *) arr;

      if (sarr->get_stmt()->is_Assignment())
        {
          if (!(sarr->get_condition()->eval_level0()))
            logs::fatal_error("Assignment arrow with condition not supported");

          xmlNodePtr lv = 
	    xml_of_lvalue (((Assignment *) sarr->get_stmt())->get_lval(), true);
	  
	  xmlNodePtr v = 
	    xml_of_expr (((Assignment *) sarr->get_stmt ())->get_rval ());
	  xmlNodePtr xarrow = xmlNewChild (root, NULL, BAD_CAST "assign", NULL);
	  xmlAddChild (xarrow, lv);
	  xmlAddChild (xarrow, v);
	  s_add_prop (xarrow, "id", sarr->get_origin());
	  s_add_prop (xarrow, "next", sarr->get_target());
	  return;
        }

      if (sarr->get_stmt()->is_Skip())
        {
	  xmlNodePtr xarrow = xmlNewChild (root, NULL, BAD_CAST "skip", NULL);
	  xmlNodePtr guard = xml_guard_of_static_arrow (sarr);
	  xmlAddChild (xarrow, guard);
	  s_add_prop (xarrow, "id", sarr->get_origin ());
	  return;
        }

      if (sarr->get_stmt ()->is_Jump ())
        logs::fatal_error ("xml_of_stmtarrow:: static jump statement "
			   "not supported");
    }
  else   // Arrow is dynamic
    {
      DynamicArrow *darr = (DynamicArrow *) arr;
      xmlNodePtr target = xml_of_expr (darr->get_target ());
      xmlNodePtr xarrow = xmlNewChild (root, NULL, BAD_CAST "jump", NULL);
      xmlAddChild (xarrow, target);
      s_add_prop (xarrow, "id", darr->get_origin ());
      s_add_annotations (xarrow, darr);

      return;
    }
}


static void
xml_of_microcode_element (xmlNodePtr root, const MicrocodeNode *elt)
{
  vector<StmtArrow *> * succs = elt->get_successors();

  //--- particular case of the switch
  bool is_switch = true;

  for (int i = 0; i < (int) succs->size() && is_switch; i++)
    is_switch = (!((*succs)[i]->is_dynamic()) &&
		 (*succs)[i]->get_stmt()->is_Skip());

  if (is_switch)
    {
      string addr = xml_of_mcaddress (elt->get_loc ());
      xmlNodePtr sw = xmlNewChild (root, NULL, BAD_CAST "switch", NULL);
      for (int i = 0; i < (int) succs->size(); i++)
	{
	  assert (!((*succs)[i]->is_dynamic()) &&
		  (*succs)[i]->get_stmt()->is_Skip());
	  xmlNodePtr guard = 
	    xml_guard_of_static_arrow ((StaticArrow *)(*succs)[i]);
	  xmlAddChild (sw, guard);
        }
      s_add_prop (sw, "id", addr);
    }
  else   //--- general case
    {
      for (int i = 0; i < (int) succs->size(); i++)
        xml_of_stmtarrow (root, (*succs)[i]);
    }

}

static void
s_generate_code (xmlNodePtr root, const Microcode *prg)
{
  xmlNodePtr code = xmlNewNode (NULL, BAD_CAST "code");
  xmlAddChild (root, code);

  for (Microcode::const_node_iterator n = prg->begin_nodes (); 
       n != prg->end_nodes (); n++)
    xml_of_microcode_element (code, *n);
}

struct CmpRegisterDesc
{
  bool operator() (const RegisterDesc *r1, const RegisterDesc *r2) {
    return r1->get_label () < r2->get_label ();
  }
};

static void 
s_declare_registers (xmlNodePtr root, const MicrocodeArchitecture *mcarch)
{
  const RegisterSpecs *regs[] = {
    mcarch->get_reference_arch ()->get_registers (),
    mcarch->get_tmp_registers (),
    NULL
  };
  list<const RegisterDesc *> reglist;

  for (const RegisterSpecs **r = regs; *r; r++)
    {
      RegisterSpecs::const_iterator reg = (*r)->begin ();
      for (; reg != (*r)->end (); reg++)
	{
	  if (reg->second->is_alias ())
	    continue;
	  reglist.push_back (reg->second);
	}
    }
  CmpRegisterDesc c;
  reglist.sort<CmpRegisterDesc> (c);

  for (list<const RegisterDesc *>::iterator r = reglist.begin();
       r != reglist.end (); r++)
    {
      xmlNodePtr node = xmlNewChild (root, NULL, BAD_CAST "vardecl", NULL);
      s_add_prop (node, "id", (*r)->get_label ());
      s_add_prop (node, "size", (*r)->get_register_size ());
    }
}

static int 
s_xml_output_write_callback (void *context, const char *buffer, int len)
{
  ostream *out = (ostream *) context;

  out->write (buffer, len);
  return len;
}

static int
s_xml_output_close_callback (void * context)
{
  ostream *out = (ostream *) context;

  out->flush ();
  return 0;
}

void 
xml_of_microcode (ostream &out, 
		  const Microcode *prg, 
		  const MicrocodeArchitecture *mcarch)
{
  xmlOutputBufferPtr xout =
    xmlOutputBufferCreateIO (&s_xml_output_write_callback, 
			     &s_xml_output_close_callback,
			     &out,
			     NULL);

  xmlDocPtr doc = xmlNewDoc (BAD_CAST "1.0");
  xmlCreateIntSubset (doc, BAD_CAST "program", NULL, BAD_CAST "insight.dtd");
  xmlNodePtr root = xmlNewNode (NULL, BAD_CAST "program");
  xmlDocSetRootElement (doc, root);
  if (mcarch)
    s_declare_registers (root, mcarch);
  s_generate_code (root, prg);
  s_generate_annotations_for_nodes (root, prg);
  xmlThrDefIndentTreeOutput (1);
  xmlSaveFormatFileTo (xout, doc, "UTF-8", 1);
  xmlFreeDoc (doc);
}


/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assoc.h"
#include "node.h"
#include "type.h"
#include "y.tab.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>

/*------------------------------------------------------------------------*/

int mangle_identifiers = 0;

/*------------------------------------------------------------------------*/

static const char * op(int tag)
{
  switch(tag)
    {
      case A: return "A";
      case ACCESS: return "ACCESS";
      case AF: return "AF";
      case AG: return "AG";
      case AND: return "&";
      case ARRAY: return "ARRAY";
      case ASSIGN: return "ASSIGN";
      case AT: return "AT";
      case ATOM: return "ATOM";
      case AU: return "AU";
      case AX: return "AX";
      case BOOLEAN: return "BOOLEAN";
      case CASE: return "case";
      case COLON: return "COLON";
      case COMPUTE: return "COMPUTE";
      case DECL: return "DECL";
      case DEFINE: return "DEFINE";
      case DEFINEASSIGNMENT: return "DEFINEASSIGNMENT";
      case DIVIDE: return "/";
      case DOT: return "DOT";
      case E: return "E";
      case EF: return "EF";
      case EG: return "EG";
      case ENUM: return "ENUM";
      case EQDEF: return ":=";
      case EQUAL: return "=";
      case ESAC: return "esac";
      case EU: return "EU";
      case EX: return "EX";
      case FAIRNESS: return "FAIRNESS";
      case GE: return ">=";
      case GT: return ">";
      case IFF: return "<->";
      case IMPLIES: return "->";
      case INIT: return "INIT";
      case INITASSIGNMENT: return "INITASSIGNMENT";
      case INSTANCE: return "INSTANCE";
      case INVAR: return "INVAR";
      case INVARASSIGNMENT: return "INVARASSIGNMENT";
      case ISA: return "ISA";
      case LE: return "<=";
      case LIST: return "LIST";
      case LT: return "<";
      case MAX: return "MAX";
      case MIN: return "MIN";
      case MINU: return "MINU";
      case MINUS: return "-";
      case MOD: return "mod";
      case MODULE: return "MODULE";
      case NEXT: return "next";
      case NOT: return "!";
      case NOTEQUAL: return "!=";
      case NUMBER: return "NUMBER";
      case OF: return "OF";
      case OR: return "|";
      case PLUS: return "+";
      case PROCESS: return "PROCESS";
      case SETIN: return "in";
      case SETNOTIN: return "notin";
      case SMALLINIT: return "init";
      case SPEC: return "SPEC";
      case TIMES: return "*";
      case TRANS: return "TRANS";
      case TRANSASSIGNMENT: return "TRANSASSIGNMENT";
      case TWODOTS: return "..";
      case UMINUS: return "UMINUS";
      case UNION: return "union";
      case UNTIL: return "UNTIL";
      case VAR: return "VAR";
      default: 
        assert(0);
	return 0;
    }
}

/*------------------------------------------------------------------------*/

static int is_op(int tag)
{
  int res;

  switch(tag)
    {
      case AND:
      case DIVIDE:
      case EQUAL:
      case GE:
      case GT:
      case IFF:
      case IMPLIES:
      case LE:
      case LT:
      case MINUS:
      case MOD:
      case NOTEQUAL:
      case OR:
      case PLUS:
      case SETIN:
      case SETNOTIN:
      case TIMES:
      case AF:
      case AG:
      case AX:
      case EF:
      case EG:
      case EX:
      case NOT:
      case UMINUS:
      case UNION:
        res = 1;
	break;

      default:
	res = 0;
        break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

static int is_binary(int tag)
{
  int res;

  switch(tag)
    {
      case AND:
      case AU:
      case DIVIDE:
      case EQUAL:
      case EU:
      case GE:
      case GT:
      case IFF:
      case IMPLIES:
      case LE:
      case LT:
      case MINUS:
      case MOD:
      case NOTEQUAL:
      case OR:
      case PLUS:
      case SETIN:
      case SETNOTIN:
      case TIMES:
      case UNION:
        res = 1;
	break;

      case AF:
      case AG:
      case AX:
      case EF:
      case EG:
      case EX:
      case NOT:
      case UMINUS:
        res = 0;
 	break;

      default:
        assert(0);
	res = 0;
        break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/
#endif /* NDEBUG */
/*------------------------------------------------------------------------*/

static int is_unary(int tag)
{
  int res;

  switch(tag)
    {
      case AND:
      case AU:
      case DIVIDE:
      case EQUAL:
      case EU:
      case GE:
      case GT:
      case IFF:
      case IMPLIES:
      case LE:
      case LT:
      case MINUS:
      case MOD:
      case NOTEQUAL:
      case OR:
      case PLUS:
      case SETIN:
      case SETNOTIN:
      case TIMES:
      case UNION:
        res = 0;
	break;

      case AF:
      case AG:
      case AX:
      case EF:
      case EG:
      case EX:
      case NOT:
      case UMINUS:
        res = 1;
  	break;

      default:
        assert(0);
	res = 0;
        break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static void pr(
  FILE * file, Assoc * types, int indent, Node * node, int outer);

/*------------------------------------------------------------------------*/

static const char * tag2macro(int tag)
{
  switch(tag)
    {
      case A: return "A";
      case AF: return "AF";
      case AG: return "AG";
      case AND: return "AND";
      case ARRAY: return "ARRAY";
      case ASSIGN: return "ASSIGN";
      case ATOM: return "ATOM";
      case AU: return "AU";
      case AX: return "AX";
      case BOOLEAN: return "BOOLEAN";
      case CASE: return "CASE";
      case COLON: return "COLON";
      case DEFINE: return "DEFINE";
      case DIVIDE: return "DIVIDE";
      case DOT: return "DOT";
      case E: return "E";
      case EF: return "EF";
      case EG: return "EG";
      case EQDEF: return "EQDEF";
      case EQUAL: return "EQUAL";
      case ESAC: return "ESAC";
      case EU: return "EU";
      case EX: return "EX";
      case GE: return "GE";
      case GT: return "GT";
      case IFF: return "IFF";
      case IMPLIES: return "IMPLIES";
      case INIT: return "INIT";
      case INVAR: return "INVAR";
      case LE: return "LE";
      case LIST: return "LIST";
      case LT: return "LT";
      case MIN: return "MIN";
      case MAX: return "MAX";
      case MINU: return "MINU";
      case MINUS: return "MINUS";
      case MOD: return "MOD";
      case MODULE: return "MODULE";
      case NEXT: return "NEXT";
      case NOT: return "NOT";
      case NOTEQUAL: return "NOTEQUAL";
      case NUMBER: return "NUMBER";
      case OF: return "OF";
      case OR: return "OR";
      case PLUS: return "PLUS";
      case SETIN: return "SETIN";
      case SETNOTIN: return "SETNOTIN";
      case SMALLINIT: return "SMALLINIT";
      case SPEC: return "SPEC";
      case TIMES: return "TIMES";
      case TRANS: return "TRANS";
      case TWODOTS: return "TWODOTS";
      case UMINUS: return "UMINUS";
      case UNION: return "UNION";
      case UNTIL: return "UNTIL";
      case VAR: return "VAR";
      default: return "???";
    }
}

/*------------------------------------------------------------------------*/

static int priority(int tag)
{
  int res;

  switch(tag)
    {
      case MODULE: res = 7; break;
      case EU: res = 12; break;
      case AU: res = 13; break;
      case MINU: res = 16; break;
      case VAR: res = 18; break;
      case DEFINE: res = 19; break;
      case INIT: res = 20; break;
      case TRANS: res = 21; break;
      case INVAR: res = 22; break;
      case SPEC: res = 25; break;
      case ASSIGN: res = 30; break;
      case BOOLEAN: res = 36; break;
      case ARRAY: res = 37; break;
      case OF: res = 38; break;
      case LIST: res = 40; break;
      case EQDEF: res = 50; break;
      case TWODOTS: res = 51; break;
      case CASE: res = 58; break;
      case ESAC: res = 59; break;
      case COLON: res = 60; break;
      case ATOM: res = 61; break;
      case NUMBER: res = 62; break;
      case IMPLIES: res = 65; break;
      case IFF: res = 66; break;
      case OR: res = 67; break;
      case AND: res = 68; break;
      case NOT: res = 69; break;
      case EX: res = 70; break;
      case AX: res = 71; break;
      case EF: res = 72; break;
      case AF: res = 73; break;
      case EG: res = 74; break;
      case AG: res = 75; break;
      case E: res = 76; break;
      case A: res = 77; break;
      case UNTIL: res = 78; break;
      case MIN: res = 84; break;
      case EQUAL: res = 88; break;
      case NOTEQUAL: res = 89; break;
      case LT: res = 90; break;
      case GT: res = 91; break;
      case LE: res = 92; break;
      case GE: res = 93; break;
      case UNION: res = 94; break;
      case SETIN: res = 95; break;
      case SETNOTIN: res = 96; break;
      case MOD: res = 97; break;
      case PLUS: res = 98; break;
      case MINUS: res = 99; break;
      case TIMES: res = 100; break;
      case DIVIDE: res = 101; break;
      case UMINUS: res = 102; break;
      case NEXT: res = 103; break;
      case SMALLINIT: res = 104; break;
      case DOT: res = 105; break;
      default:
	fprintf(stderr,
	  "*** priority(%s) not implemented\n",
	  tag2macro(tag));
	assert(0);
	res = 0;
	exit(1);
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static void pr_list(FILE * file, Node * node, int print_comma)
{
  Node * p;

  assert(node);
  assert(node -> tag == LIST);

  pr(file, 0, 0, car(node), 0);
  for(p = cdr(node); p; p = cdr(p))
    {
      assert(p -> tag == LIST);
      if(print_comma) fputc(',', file);
      fputc(' ', file);
      pr(file, 0, 0, car(p), 0);
    }
}

/*------------------------------------------------------------------------*/

static void pr_access(FILE * file, Node * node)
{
  Node * p, * head;

  for(p = node; p && p -> tag != AT; p = cdr(p))
    {
      assert(p -> tag == ACCESS || p -> tag == AT);

      head = car(p);
      switch(head -> tag)
        {
	  /* This won't work if variables are allowed as arguments to
	   * arrays.
	   */
	  case NUMBER:
	    if(mangle_identifiers) fputs("_L_", file);
	    else fputc('[', file);
	    pr(file, 0, 0, head, 0);
	    if(mangle_identifiers) fputs("_R_", file);
	    else fputc(']', file);
	    break;
	  
	  case ATOM:
	    if(mangle_identifiers) fputs("_o_", file);
	    else fputc('.', file);
	    pr(file, 0, 0, head, 0);
	    break;

	  default:
	    assert(0);
	    break;
	}
    }
  
  if(p)
    {
      assert(p -> tag == AT);
      assert(!cdr(p));
      assert(car(p) -> tag == NUMBER);

      if(mangle_identifiers) fputs("_a_", file);
      else fputc('@', file);

      fprintf(file, "%u", (int)(long) car(car(p)));
    }
}

/*------------------------------------------------------------------------*/

static void pr_identifier(const char * id, FILE * file)
{
  const char * p;

  if(mangle_identifiers)
    {
      for(p = id; *p; p++)
	{
	  switch(*p)
	    {
	      case '_': fputs("___", file); break;
	      case '.': fputs("_o_", file); break;
	      default: fputc(*p, file); break;
	    }
	}
    }
  else fputs(id, file);
}

/*------------------------------------------------------------------------*/

static int is_associative(int tag)
{
  int res;

  switch(tag)
    {
      case AND:
      case AU:
      case EQUAL:
      case EU:
      case OR:
      case PLUS:
      case TIMES:
        res = 1;
	break;

      case DIVIDE:
      case GE:
      case GT:
      case IMPLIES:
      case LE:
      case LT:
      case MINUS:
      case MOD:
      case NOTEQUAL:
      case SETIN:
      case SETNOTIN:
      case IFF:			/* for flatsmv */
        res = 0;
	break;

      case AF:
      case AG:
      case AX:
      case EF:
      case EG:
      case EX:
      case NOT:
      case UMINUS:
      default:
        assert(0);
	res = 0;
        break;
    };
  
  return res;
}

/*------------------------------------------------------------------------*/

static void pr_toplevel_conjunction(
  FILE * file, int start, Node * node, int outer)
{
  int inner;

  if(node -> tag == AND)
    {
      inner =  priority(AND);
      pr_toplevel_conjunction(file, start, car(node), inner);
      pr_toplevel_conjunction(file, 0, cdr(node), inner);
    }
  else
    {
      if(!start) fputs(" &", file);
      if(node -> tag != CASE) fputs("\n  ", file);
      pr(file, 0, 1, node, outer);
    }
}

/*------------------------------------------------------------------------*/

static void tab(FILE * file, int n)
{
  int i;

  for(i = 0; i < n; i++) fputs("  ", file);
}

/*------------------------------------------------------------------------*/

static unsigned get_at_index(Node * node)
{
  Node * number;
  unsigned res;

  assert(node);

  switch(node -> tag)
    {
      case AT:
        number = car(node);
	res = (long) car(number);
	break;
      
      case ACCESS:
        res = get_at_index(cdr(node));
        break;
      
      default:
        assert(0);
	res = 0;
	break;
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

static int is_MSB(Node * var, Node * type)
{
  unsigned n, i;
  int res;

  i = get_at_index(var);
  n = num_bits(type);
  res = (n - 1 == i);

  return res;
}

/*------------------------------------------------------------------------*/

static void pr(
  FILE * file, Assoc * types, int indent, Node * node, int outer)
{
  int inner, print_parenthesis;
  Node * a, * prev, * type;

  if(node)
    {
      if(is_op(node -> tag))
	{
	  inner = priority(node -> tag);

	  if(is_unary(node -> tag))
	    {
	      print_parenthesis = (inner < outer);
	      if(print_parenthesis) fputc('(', file);

	      a = node;
	      do {
		fputs(op(a -> tag), file);
		if(a -> tag != UMINUS && a -> tag != NOT) fputc(' ', file);
		prev = a;
		a = car(a);
	      } while(is_op(a -> tag) && is_unary(a -> tag));

	      inner = priority(prev -> tag);
	      pr(file, types, indent, a, inner);
	      if(print_parenthesis) fputc(')', file);
	    }
	  else
	    {
	      assert(is_binary(node -> tag));

	      print_parenthesis = 
		((inner < outer) ||
		 (inner == outer && !is_associative(node -> tag)));

	      if(print_parenthesis) fputc('(', file);
	      pr(file, types, indent, car(node), inner);
	      fputc(' ', file);
	      fputs(op(node -> tag), file);
	      fputc(' ', file);

	      if(cdr(node) -> tag == NOT && 
	         inner >= priority(EQUAL) &&
		 outer <= priority(NOT))
	        {
		  /* Special case for `a = !b' etc.  The SMV priority of `='
		   * is stronger than the priority of `!'.  Thus the term
		   * `a = !b & c' which is parsed as (a = !b) & c' is
		   * printed as a = (!b) & c.  However in this situatio,
		   * where `&' has a lower priority than `!' we can omit the
		   * parenthesis.
		   */
	          pr(file, types, indent, cdr(node), priority(NOT));
		}
	      else pr(file, types, indent, cdr(node), inner);
	      if(print_parenthesis) fputc(')', file);
	    }
	}
      else
	{
	  switch(node -> tag)
	    {
	      case ACCESS:
		pr(file, types, indent, car(node), outer);
		pr_access(file, cdr(node));
		break;
	      
	      case ARRAY:
		fputs("array ", file);
		pr(file, types, indent, car(node), outer);
		fputs(" of ", file);
		pr(file, types, indent, cdr(node), outer);
		break;
	      
	      case ASSIGN:
		fputs("ASSIGN\n", file);
		pr(file, types, indent, car(node), 0);
		break;
	      
	      case ATOM:
		pr_identifier((char*) car(node), file);
		break;

	      case AU:
		fputs("A [ ", file);
		pr(file, types, indent, car(node), 0);
		fputs(" U ", file);
		pr(file, types, indent, cdr(node), 0);
		fputs(" ]", file);
		break;

	      case BOOLEAN:
		fputs("boolean", file);
		break;
	      
	      case CASE:
		fputc('\n', file);
		tab(file, indent);
		fputs("case", file);
		if(car(car(car(node))) -> tag != CASE) fputc('\n', file);
		pr(file, types, indent + 1, car(node), 0);
		tab(file, indent);
		fputs("esac", file);
		break;

	      case COLON:
		if(car(node) -> tag != CASE) tab(file, indent);
		pr(file, types, indent, car(node), 0);
		fputs(" :", file);
		if(cdr(node) -> tag != CASE) fputc(' ', file);
		pr(file, types, indent + 1, cdr(node), 0);
		fputs(";\n", file);
		break;

	      case DECL:
		fputs("  ", file);
		pr(file, types, indent, car(node), 0);
		fputs(" : ", file);
		pr(file, types, indent, cdr(node), 0);
		fputs(";", file);
		if(types)
		  {
		    type = get_association(types, car(node));
		    assert(type);
		    switch(type -> tag)
		      {
			case BOOLEAN:
			  break;

			case ENUM:
			  if(is_MSB(car(node), type))
			    {
			      fputs(" --TYPE-- ", file);
			      pr_list(file, car(type), 0);
			    }
			  break;

			case TWODOTS:
			  if(is_MSB(car(node), type))
			    {
			      fputs(" --TYPE-- ", file);
			      pr(file, 0, 0, type, 0);
			    }
			  break;

		        default:
			  assert(0);
			  break;
		      }
		  }
		fputc('\n', file);
		break;
	      
	      case DEFINE:
		fputs("DEFINE\n", file);
		pr(file, types, indent, car(node), 0);
		break;
	      
	      case ENUM:
		fputc('{', file);
		pr_list(file, car(node), 1);
		fputc('}', file);
		break;

	      case EU:
		fputs("E [ ", file);
		pr(file, types, indent, car(node), 0);
		fputs(" U ", file);
		pr(file, types, indent, cdr(node), 0);
		fputs(" ]", file);
		break;

	      case INITASSIGNMENT:
		fputs("  init(", file);
		pr(file, types, indent, car(node), 0);
		fputs(") :=", file);
		if(cdr(node) -> tag != CASE) fputc(' ', file);
		pr(file, types, 2, cdr(node), 0);
		fputs(";\n", file);
		break;

	      case INSTANCE:
		pr(file, types, indent, car(car(node)), outer);
		a = cdr(car(node));
		if(a)
		  {
		    fputc('(', file);
		    pr_list(file, a, 1);
		    fputc(')', file);
		  }
		break;
	      
	      case DEFINEASSIGNMENT:
	      case INVARASSIGNMENT:
		fputs("  ", file);
		pr(file, types, indent, car(node), 0);
		fputs(" :=", file);
		if(cdr(node) -> tag != CASE) fputc(' ', file);
		pr(file, types, 2, cdr(node), 0);
		fputs(";\n", file);
		break;
	      
	      case ISA:
	        fputs("ISA ", file);
	        pr(file, types, indent, car(node), outer);
		fputc('\n', file);
	        break;

	      case LIST:
		pr(file, types, indent, car(node), outer);
		if(car(node) && car(node) -> tag == MODULE && cdr(node))
		  fputc('\n', file);
		if(cdr(node)) pr(file, types, indent, cdr(node), outer);
		break;
	      
	      case MODULE:
		fputs("MODULE ", file);
		pr(file, types, indent, car(car(node)), 0);
		a = cdr(car(node));
		if(a)
		  {
		    fputc('(', file);
		    pr_list(file, a, 1);
		    fputc(')', file);
		  }
		fputc('\n', file);
		pr(file, types, indent, cdr(node), 0);
		break;
	      
	      case PROCESS:
	        fputs("process ", file);
		pr(file, types, indent, car(node), outer);
		break;
	      
	      case MIN:
	      case MAX:
		fputs(op(node -> tag), file);
		fputc('[', file);
		pr(file, types, 0, car(node), 0);
		fputs(", ", file);
		pr(file, types, 0, cdr(node), 0);
		fputs("]", file);
	        break;

	      case COMPUTE:
	        fputs("COMPUTE ", file);
		pr(file, types, 0, car(node), 0);
		fputc('\n', file);
		break;
	      
	      case NEXT:
		fputs("next(", file);
		pr(file, types, 0, car(node), 0);
		fputc(')', file);
		break;

	      case NUMBER:
		fprintf(file, "%d", (int)(long) car(node));
		break;
	      
	      case TRANSASSIGNMENT:
		fputs("  next(", file);
		pr(file, types, indent, car(node), 0);
		fputs(") :=", file);
		if(cdr(node) -> tag != CASE) fputc(' ', file);
		pr(file, types, 2, cdr(node), 0);
		fputs(";\n", file);
		break;

	      case TWODOTS:
		pr(file, types, indent, car(node), outer);
		fputs("..", file);
		pr(file, types, indent, cdr(node), outer);
		break;

	      case VAR:
		fputs("VAR\n", file);
		pr(file, types, indent, car(node), 0);
		break;
	      
	      case INIT:
	      case TRANS:
	      case INVAR:
	      case SPEC:
	      case FAIRNESS:
		fputs(op(node -> tag), file);
		pr_toplevel_conjunction(file, 1, car(node), 0);
		fputc('\n', file);
		break;
	      
	      default:
		fprintf(stderr,
		  "*** pr(%s) not implemented\n",
		  tag2macro(node -> tag));
		assert(0);
		exit(1);
		break;
	    }
	}
    }
}

/*------------------------------------------------------------------------*/

void print(FILE * file, Node * node)
{
  pr(file, 0, 0, node, 0);
}

/*------------------------------------------------------------------------*/

void print_typped(FILE * file, Assoc * types, Node * node)
{
  pr(file, types, 0, node, 0);
}

/*------------------------------------------------------------------------*/
/* Just for debugging purposes.
 */
void printnl(Node* node)
{ 
  pr(stdout, 0, 0, node, 0);
  fputc('\n', stdout);
}

/*------------------------------------------------------------------------*/

void print_lhs_of_assignment(FILE * file, Node * node)
{
  switch(node -> tag)
    {
      case TRANSASSIGNMENT:
        fputs("next(", file);
	print(file, car(node));
	fputc(')', file);
	break;

      case DEFINEASSIGNMENT:
      case INVARASSIGNMENT:
	print(file, car(node));
	break;

      case INITASSIGNMENT:
        fputs("init(", file);
	print(file, car(node));
	fputc(')', file);
	break;
      
      default:
        assert(0);
	break;
    }
}

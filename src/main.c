/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/

#include "assign.h"
#include "assoc.h"
#include "check.h"
#include "deter.h"
#include "encode.h"
#include "flatten.h"
#include "macros.h"
#include "node.h"
#include "pp.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <strings.h>

/*------------------------------------------------------------------------*/

static char * id = "$Id: main.c,v 1.4 2000-07-26 15:44:28 biere Exp $";

/*------------------------------------------------------------------------*/

extern int yyparse(void);
extern Node * yyparse_result;
extern const char * yyin_name;
extern FILE * yyin;
extern int mangle_identifiers;

/*------------------------------------------------------------------------*/

#ifdef YYDEBUG
extern int yydebug;
#endif

/*------------------------------------------------------------------------*/
/* Global flags.
 */

int verbose = 0;		                         /* verbose level */
int enable_nnf = 1;		     /* generat NNF during simplification */

/* This specifies the maximal number of bits that an oracle may have and
 * still is quantified out on-the-fly.  For more details see `deter.c'.
 */
#define default_max_size_quantified_oracle 5
unsigned max_size_quantified_oracle = default_max_size_quantified_oracle;

/* The `default_simplification_level' is reported in the `usage message.
 * There you will also find an explanation for the various simplification
 * levels.
 */
#define default_simplification_level 2
unsigned simplification_level = default_simplification_level;

/*------------------------------------------------------------------------*/

enum Mode
{ 
  PRETTY_PRINT,
  DETERMINIZE,
  FLATTEN,
  CHECK,
  ENCODE,
  EXTRACT_ASSIGNMENTS,
  EXTRACT_MACROS
};

/*------------------------------------------------------------------------*/

typedef enum Mode Mode;

/*------------------------------------------------------------------------*/

static Mode mode = EXTRACT_MACROS;

/*------------------------------------------------------------------------*/

static void print_version(void)
{
  printf(
    "smvflatten version " VERSION "\n"
    "(C)opyright 2000 by Armin Biere\n"
    "%s\n", id);
}

/*------------------------------------------------------------------------*/

static void usage(void)
{
  printf(
"(C)opyright 2000 by Armin Biere.  All rights reserved.\n"
"Do not copy without permission of the author.\n"
"\n"
"usage:  smvflatten <options> <file>\n"
"\n"
"  where options is a list of the following options\n"
"\n"
"    -h           print this summary\n"
"    --version    print version on stdout\n"
"    -v[0-9]      set verbose level\n"
"\n"
"    -p[p]        stop after parsing                   (phase 0)\n"
"    -f[t]        stop after flattening of hirarchy    (phase 1)\n"
"    -d[et]       stop after determinization           (phase 2)\n"
"    -c[heck]     stop after semantic checking         (phase 3)\n"
"    -e[nc]       stop after boolean encoding          (phase 4)\n"
"    -a[ssign]    stop after extraction of assignments (phase 5)\n"
"\n"
"    (default is to stop after extraction of macros, which is phase 6)\n"
"\n"
"    -q[0-9]     number of bits an oracle may have and still is quantified\n"
"                out during determinization (default %u)\n"
"\n"
"    -m[angle]    mangle identifiers, i.e. flattening and encoding generates\n"
"                 identifiers that may contain the following characters:\n"
"\n"
"                     '.'    '@'    '['    ']'\n"
"\n"
"                 If mangling is enabled those are replaced by:\n"
"\n"
"                    '_o_'  '_a_'  '_L_'  '_R_'\n"
"\n"
"                 In addition '_' is replaced by '___'.  The result is now\n"
"                 again a legal SMV program.\n"  
"\n"
"    -no-nnf      disable building NNF during simplification\n"
"\n"
"    -simp[0-5]   simplification level during boolean encoding (default %d):\n"
"\n"
"        -simp0   no simplification\n"
"        -simp1   local simplifications\n"
"        -simp2   plus local factorization\n"
"        -simp3   plus merging and factorization of cases in CASE statements\n"
"        -simp4   plus removal of (negated) duplicates\n"
"        -simp5   plus global subsumption\n"
#ifdef YYDEBUG
"\n"
"    -yd          switch on parser debugging\n"
#endif
"\n",
  default_max_size_quantified_oracle,
  default_simplification_level
);
}

/*------------------------------------------------------------------------*/

static Node * after_parsing(void)
{
  return yyparse_result;
}

/*------------------------------------------------------------------------*/

static Node * after_flattening(void)
{
  Node * tmp, * res;

  tmp = after_parsing();
  res = flatten(tmp);
  delete(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * after_determinization(void)
{
  Node * res, * tmp;

  tmp = after_flattening();
  res = determinize(tmp);
  delete(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * after_check(void)
{
  Assoc * assoc;
  Node * res;

  res = after_determinization();
  assoc = check(res);

  forall_dst_in_Assoc(assoc, (void(*)(void*)) &delete);
  delete_Assoc(assoc);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * after_encode(Assoc ** assoc_ptr)
{
  Node * res, * tmp;

  tmp = after_determinization();
  *assoc_ptr = check(tmp);
  res = encode(*assoc_ptr, tmp);
  delete(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * after_extract_assignments(Assoc ** assoc_ptr)
{
  Node * res, * tmp;

  tmp = after_encode(assoc_ptr);
  res = extract_assignments(tmp);
  delete(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

static Node * after_extract_macros(Assoc ** assoc_ptr)
{
  Node * res, * tmp;

  tmp = after_extract_assignments(assoc_ptr);
  res = extract_macros(tmp);
  delete(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

int main(int argc, char ** argv)
{
  const char * in_name;
  Assoc * types;
  Node * tmp;
  FILE * in;
  int i;

  in = 0;
  in_name = 0;

# ifdef YYDEBUG
  yydebug = 0;
# endif

  for(i = 1; i < argc; i++)
    {
           if(strcmp("-v0", argv[i]) == 0) verbose = 0;
      else if(strcmp("-v1", argv[i]) == 0) verbose = 1;
      else if(strcmp("-v2", argv[i]) == 0) verbose = 2;
      else if(strcmp("-v3", argv[i]) == 0) verbose = 3;
      else if(strcmp("-v4", argv[i]) == 0) verbose = 4;
      else if(strcmp("-v5", argv[i]) == 0) verbose = 5;
      else if(strcmp("-v6", argv[i]) == 0) verbose = 6;
      else if(strcmp("-v7", argv[i]) == 0) verbose = 7;
      else if(strcmp("-v8", argv[i]) == 0) verbose = 8;
      else if(strcmp("-v9", argv[i]) == 0) verbose = 9;
      else
      if(argv[i][0] == '-' &&
         argv[i][1] == 'q' && 
	 '0' <= argv[i][2] && argv[i][2] <= '9' &&
	 !argv[i][3])
	{
	  max_size_quantified_oracle = argv[i][2] - '0';
	}
      else
      if(strcmp(argv[i], "-h") == 0)
        {
	  usage();
	  exit(0);
	}
      else
      if(strcmp(argv[i], "-m") == 0 || strcmp(argv[i], "-mangle") == 0)
        {
	  mangle_identifiers = 1;
	}
      else
      if(strcmp(argv[i], "-p") == 0 || strcmp(argv[i], "-pp") == 0)
        {
	  mode = PRETTY_PRINT;
	}
      else
      if(strcmp(argv[i], "-f") == 0 || strcmp(argv[i], "-ft") == 0)
        {
	  mode = FLATTEN;
	}
      else
      if(strcmp(argv[i], "-d") == 0 || strcmp(argv[i], "-det") == 0)
        {
	  mode = DETERMINIZE;
	}
      else
      if(strcmp(argv[i], "-c") == 0 || strcmp(argv[i], "-check") == 0)
        {
	  mode = CHECK;
	}
      else
      if(strcmp(argv[i], "-e") == 0 || strcmp(argv[i], "-enc") == 0)
        {
	  mode = ENCODE;
	}
      else
      if(strcmp(argv[i], "-a") == 0 || strcmp(argv[i], "-assign") == 0)
        {
	  mode = EXTRACT_ASSIGNMENTS;
	}
      else
      if(strcmp(argv[i], "--version") == 0)
        {
	  print_version();
	  exit(0);
	}
      else
      if(strcmp(argv[i], "-simp0") == 0)
        {
	  simplification_level = 0;
	}
      else
      if(strcmp(argv[i], "-simp1") == 0)
        {
	  simplification_level = 1;
	}
      else
      if(strcmp(argv[i], "-simp2") == 0)
        {
	  simplification_level = 2;
	}
      else
      if(strcmp(argv[i], "-simp3") == 0)
        {
	  simplification_level = 3;
	}
      else
      if(strcmp(argv[i], "-simp4") == 0)
        {
	  simplification_level = 4;
	}
      else
      if(strcmp(argv[i], "-simp5") == 0)
        {
	  simplification_level = 5;
	}
      else
      if(strcmp(argv[i], "-no-nnf") == 0)
        {
	  enable_nnf = 0;
	}
# ifdef YYDEBUG
      else
      if(strcmp(argv[i], "-yd") == 0) yydebug = 1;
# endif
      else
      if(argv[i][0] == '-')
        {
	  fprintf(stderr,
	    "*** smvflatten: unknown command line option '%s' (try '-h')\n",
	    argv[i]);
	  exit(1);
	}
      else
      if(in)
        {
	  fprintf(stderr, "*** smvflatten: can not open two files\n");
	  exit(1);
	}
      else
        {
	  in_name = argv[i];
	  in = fopen(in_name, "r");
	  if(!in)
	    {
	      fprintf(stderr,
	        "*** smvflatten: can not read '%s'\n", in_name);
	      exit(1);
	    }
	}
    }

  if(in)
    {
      yyin = in;
      yyin_name = in_name;
    }
  else
    {
      yyin = stdin;
      yyin_name = "<stdin>";
    }

  init_Node();

  if(verbose) fputs("-- [verbose] phase 0: parsing ...\n", stderr);
  yyparse();
  if(verbose) fputs("-- [verbose] end of phase 0: parsed.\n", stderr);
  if(in) fclose(in);

  types = 0;

  switch(mode)
    {
      case PRETTY_PRINT:
	tmp = after_parsing();
	break;
      
      case FLATTEN:
        tmp = after_flattening();
	break;
      
      case DETERMINIZE:
        tmp = after_determinization();
        break;

      case CHECK:
        tmp = after_check();
	break;
      
      case ENCODE:
        tmp = after_encode(&types);
	break;
      
      case EXTRACT_ASSIGNMENTS:
        tmp = after_extract_assignments(&types);
	break;

      case EXTRACT_MACROS:
        tmp = after_extract_macros(&types);
	break;

      default:
        tmp = 0;
        break;
    }
  
  if(tmp)
    {
      if(types) print_typped(stdout, types, tmp);
      else print(stdout, tmp);

      delete(tmp);
    }
  
  if(types)
    {
      forall_src_in_Assoc(types, (void(*)(void*)) &delete);
      forall_dst_in_Assoc(types, (void(*)(void*)) &delete);
      delete_Assoc(types);
    }

  exit_Node();

  exit(0);
  return 0;
}

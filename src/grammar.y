/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/
%{
#include "node.h"

#include <assert.h>
#include <stdio.h>
#include <stdarg.h>

extern int yylineno;
extern int verbose;
extern char yytext[];

/*------------------------------------------------------------------------*/

/*
#define YYSTYPE Node *
*/

int yyerror(const char * fmt, ...);
char * yyin_name = 0;

static int contains_same_constant_twice(Node * node);

/*------------------------------------------------------------------------*/

Node * yyparse_result = 0;

/*------------------------------------------------------------------------*/
%}

%union {
  Node * node;
};

%token A ACCESS AF AG AND ARRAY ASSIGN AT ATOM AU AX BOOLEAN CASE COLON COMPUTE
%token DECL DEFINE DEFINEASSIGNMENT DIVIDE DOT E EF EG ENUM EQDEF EQUAL ESAC EU
%token EX FAIRNESS GE GT IFF IMPLIES INIT INITASSIGNMENT INSTANCE INVAR
%token INVARASSIGNMENT ISA LE LIST LT MAX MIN MINU MINUS MOD MODULE NEXT NOT
%token NOTEQUAL NUMBER OF OR PLUS PROCESS SETIN SETNOTIN SMALLINIT SPEC TIMES
%token TRANS TRANSASSIGNMENT TWODOTS UMINUS UNION UNTIL VAR

%type <node> A ACCESS AF AG AND ARRAY ASSIGN AT ATOM AU AX BOOLEAN CASE
%type <node> COLON COMPUTE DECL DEFINE DEFINEASSIGNMENT DIVIDE DOT E EF EG
%type <node> ENUM EQDEF EQUAL ESAC EU EX FAIRNESS GE GT IFF IMPLIES INIT
%type <node> INITASSIGNMENT INSTANCE INVAR INVARASSIGNMENT ISA LE LIST LT
%type <node> MAX MIN MINU MINUS MOD MODULE NEXT NOT NOTEQUAL NUMBER OF OR
%type <node> PLUS PROCESS SETIN SETNOTIN SMALLINIT SPEC TIMES TRANS
%type <node> TRANSASSIGNMENT TWODOTS UMINUS UNION UNTIL VAR

%type <node> access ands args arithmetic_unary assignment assignments basic
%type <node> case cases compute constant constants decl decls definition
%type <node> definitions difference division enum equals expr ges gts iff
%type <node> implications les logical_unary lts mods module modules notequals
%type <node> ors params port product range section sections setins setnotins
%type <node> start sum type unary_difference unary_division unary_equals
%type <node> unary_ges unary_gts unary_les unary_lts unary_mods
%type <node> unary_notequals unary_product unary_setins unary_setnotins
%type <node> unary_sum unary_unions unions variable

%%

start
:
/* epsilon */
{
  yyerror("no module found");
}
|
modules
{
  yyparse_result = $1;
}
;

modules
:
module
{
  $$ = cons($1, 0);
}
|
module modules 
{
  $$ = cons($1, $2);
}
;

module
:
port sections
{
  $$ = new(MODULE, copy(car($1)), $2);
  delete($1);
}
;

port
:
MODULE ATOM
{
  if(verbose >= 2)
    fprintf(
      stderr,
      "-- [verbose]   parsing MODULE %s/0\n",
      (char*) car($2));

  $$ = new(MODULE, cons($2, 0), 0);
}
|
MODULE ATOM '(' params ')'
{
  if(verbose >= 2)
    fprintf(
      stderr,
      "-- [verbose]   parsing MODULE %s/%u\n",
      (char*) car($2),
      length($4));

  $$ = new(MODULE, cons($2, $4), 0);
}
;

params
:
ATOM
{
  $$ = cons($1, 0);
}
|
ATOM ',' params
{
  $$ = cons($1, $3);
}
;

sections
:
/* epsilon */
{
  $$ = 0;
}
|
section sections
{
  $$ = cons($1, $2);
}
;

section
:
VAR decls
{
  $$ = new(VAR, $2, 0);
}
|
INIT expr
{
  $$ = new(INIT, $2, 0);
}
|
TRANS expr
{
  $$ = new(TRANS, $2, 0);
}
|
INVAR expr
{
  $$ = new(INVAR, $2, 0);
}
|
FAIRNESS expr
{
  $$ = new(FAIRNESS, $2, 0);
}
|
SPEC expr
{
  $$ = new(SPEC, $2, 0);
}
|
COMPUTE compute
{
  $$ = new(COMPUTE, $2, 0);
}
|
ISA ATOM
{
  $$ = new(ISA, $2, 0);
}
|
ASSIGN assignments
{
  $$ = new(ASSIGN, $2, 0);
}
|
DEFINE definitions
{
  $$ = new(DEFINE, $2, 0);
}
;

decls
:
/* epsilon */
{
  $$ = 0;
}
|
decl decls
{
  $$ = cons($1, $2);
}
;

decl
:
ATOM ':' type ';'
{
  $$ = new(DECL, $1, $3);
}
;

type
:
BOOLEAN
{
  $$ = new(BOOLEAN, 0, 0);
}
|
ARRAY NUMBER TWODOTS NUMBER OF type
{
  if(((int)car($2)) >= ((int)car($4))) yyerror("non valid range");
  $$ = new(ARRAY, new(TWODOTS, $2, $4), $6);
}
|
ATOM
{
  $$ = new(INSTANCE, cons($1, 0), 0);
}
|
PROCESS ATOM
{
  $$ = new(PROCESS, new(INSTANCE, cons($2, 0), 0), 0);
}
|
ATOM '(' args ')' 
{
  $$ = new(INSTANCE, cons($1, $3), 0);
}
|
PROCESS ATOM '(' args ')' 
{
  $$ = new(PROCESS, new(INSTANCE, cons($2, $4), 0), 0);
}
|
enum
|
range
;


enum
:
'{' constants '}'
{
  if(contains_same_constant_twice($2))
    yyerror("same constant occurs twice in enumeration");

  $$ = new(ENUM, $2, 0);
}
;

range
:
NUMBER TWODOTS NUMBER
{
  if(((int)car($1)) >= ((int)car($3))) yyerror("non valid range");
  $$ = new(TWODOTS, $1, $3);
}
;

constants
:
constant
{
  $$ = cons($1, 0);
}
|
constant ',' constants
{
  $$ = cons($1, $3);
}
;

constant
:
ATOM
|
NUMBER
;

args
:
expr
{
  $$ = cons($1, 0);
}
|
expr ',' args
{
  $$ = cons($1, $3);
}
;

compute
:
MIN '[' expr ',' expr ']'
{
  $$ = new(MIN, $3, $5);
}
|
MAX '[' expr ',' expr ']'
{
  $$ = new(MAX, $3, $5);
}
;

assignments
:
/* epsilon */
{
  $$ = 0;
}
|
assignment assignments
{
  $$ = cons($1, $2);
}
;

assignment
:
SMALLINIT '(' variable ')' EQDEF expr ';'
{
  $$ = new(INITASSIGNMENT, $3, $6);
}
|
NEXT '(' variable ')' EQDEF expr ';'
{
  $$ = new(TRANSASSIGNMENT, $3, $6);
}
|
variable EQDEF expr ';'
{
  $$ = new(INVARASSIGNMENT, $1, $3);
}
;

definitions
:
/* epsilon */
{
  $$ = 0;
}
|
definition definitions
{
  $$ = cons($1, $2);
}
;

definition
:
variable EQDEF expr ';'
{
  $$ = new(DEFINEASSIGNMENT, $1, $3);
}
;

expr
:
implications
;

implications
:
iff
|
iff IMPLIES implications
{
  $$ = new(IMPLIES, $1, $3);
}
;

iff
:
ors
|
iff IFF ors
{
  $$ = new(IFF, $1, $3);
}
;

ors
:
ands
|
ors OR ands
{
  $$ = new(OR, $1, $3);
}
;

ands
:
logical_unary
|
ands AND logical_unary
{
  $$ = new(AND, $1, $3);
}
;

logical_unary
:
equals
|
NOT logical_unary
{
  $$ = new(NOT, $2, 0);
}
|
EX logical_unary
{
  $$ = new(EX, $2, 0);
}
|
AX logical_unary
{
  $$ = new(AX, $2, 0);
}
|
EF logical_unary
{
  $$ = new(EF, $2, 0);
}
|
AF logical_unary
{
  $$ = new(AF, $2, 0);
}
|
EG logical_unary
{
  $$ = new(EG, $2, 0);
}
|
AG logical_unary
{
  $$ = new(AG, $2, 0);
}
|
A '[' expr UNTIL expr ']'
{
  $$ = new(AU, $3, $5);
}
|
E '[' expr UNTIL expr ']'
{
  $$ = new(EU, $3, $5);
}
;

unary_equals
:
equals
|
NOT unary_equals
{
  $$ = new(NOT, $2, 0);
}
;

equals
:
notequals
|
notequals EQUAL unary_equals
{
  $$ = new(EQUAL, $1, $3);
}
;

unary_notequals
:
notequals
|
NOT unary_notequals
{
  $$ = new(NOT, $2, 0);
}
;

notequals
:
lts
|
lts NOTEQUAL unary_notequals
{
  $$ = new (NOTEQUAL, $1, $3);
}
;

unary_lts
:
lts
|
NOT unary_lts
{
  $$ = new(NOT, $2, 0);
}
;

lts
:
gts
|
gts LT unary_lts
{
  $$ = new(LT, $1, $3);
}
;

unary_gts
:
gts
|
NOT unary_gts
{
  $$ = new(NOT, $2, 0);
}
;

gts
:
les
|
les GT unary_gts
{
  $$ = new(GT, $1, $3);
}
;

unary_les
:
les
|
NOT unary_les
{
  $$ = new(NOT, $2, 0);
}
;

les
:
ges
|
ges LE unary_les
{
  $$ = new(LE, $1, $3);
}
;

unary_ges
:
ges
|
NOT unary_ges
{
  $$ = new(NOT, $2, 0);
}
;

ges
:
unions
|
unions GE unary_ges
{ 
  $$ = new(GE, $1, $3);
}
;

unary_unions
:
unions
|
NOT unary_unions
{
  $$ = new(NOT, $2, 0);
}
;

unions
:
setins
|
setins UNION unary_unions
{
  $$ = new(UNION, $1, $3);
}
;

unary_setins
:
setins
|
NOT unary_setins
{
  $$ = new(NOT, $2, 0);
}
;

setins
:
setnotins
|
setnotins SETIN unary_setins
{
  $$ = new(SETIN, $1, $3);
}
;

unary_setnotins
:
setnotins
|
NOT unary_setnotins
{
  $$ = new(NOT, $2, 0);
}
;

setnotins
:
mods
|
mods SETNOTIN unary_setnotins
{
  $$ = new(SETNOTIN, $1, $3);
}
;

unary_mods
:
mods
|
NOT unary_mods
{
  $$ = new(NOT, $2, 0);
}
;

mods
:
sum
|
sum MOD unary_mods
{
  $$ = new(MOD, $1, $3);
}
;

unary_sum
:
sum
|
NOT unary_sum
{
  $$ = new(NOT, $2, 0);
}
;

sum
:
difference
|
difference PLUS unary_sum
{
  $$ = new(PLUS, $1, $3);
}
;

unary_difference
:
product
|
NOT unary_difference
{
  $$ = new(NOT, $2, 0);
}
;

difference
:
product
|
difference MINUS unary_difference
{
  $$ = new(MINUS, $1, $3);
}
;

unary_product
:
product
|
NOT unary_product
{
  $$ = new(NOT, $2, 0);
}
;

product
:
division
|
division TIMES unary_product
{
  $$ = new(TIMES, $1, $3);
}
;

unary_division
:
arithmetic_unary
|
NOT unary_division
{
  $$ = new(NOT, $2, 0);
}
;

division
:
arithmetic_unary
|
division DIVIDE unary_division
{
  $$ = new(DIVIDE, $1, $3);
}
;

arithmetic_unary
:
basic
|
MINUS arithmetic_unary
{
  $$ = new(UMINUS, $2, 0);
}
;

basic
:
variable
|
NUMBER
|
'(' expr ')'
{
  $$ = $2;
}
|
range
|
NEXT '(' expr ')'
{
  $$ = new(NEXT, $3, 0);
}
|
enum
|
CASE cases ESAC
{
  $$ = new(CASE, $2, 0);
}
;

variable
:
ATOM access
{
  if($2) $$ = new(ACCESS, $1, $2);
  else $$ = $1;
}
;

access
:
/* epsilon */
{
  $$ = 0;
}
|
'[' NUMBER ']' access
{
  $$ = new(ACCESS, $2, $4);
}
|
'.' ATOM access
{
  $$ = new(ACCESS, $2, $3);
}
;

cases
:
case
{
  $$ = cons($1, 0);
}
|
case cases
{
  $$ = cons($1, $2);
}
;

case
:
expr ':' expr ';'
{
  $$ = new(COLON, $1, $3);
}
;

%%

static int contains_same_constant_twice(Node * node)
{
  Node * p, * q;
  int res;

  assert(node);
  assert(node -> tag == LIST);

  for(res = 0, p = node; !res && p; p = cdr(p))
    {
      for(q = cdr(p); !res && q; q = cdr(q))
        {
	  res = (car(p) == car(q));
	}
    }
  
  return res;
}

/*------------------------------------------------------------------------*/

int yyerror(const char * fmt, ...)
{
  va_list ap;

  fprintf(stderr, "%s:%d: ", yyin_name ? yyin_name : "<stdin>", yylineno);
  if(yytext[0]) fprintf(stderr, "at '%s': ", yytext);

  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);

  fputc('\n', stderr);
  fflush(stderr);

  exit(1);
  return(1);
}

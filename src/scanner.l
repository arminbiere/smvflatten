/*------------------------------------------------------------------------*/
/* Copyright 1999-2000 Armin Biere.
 *
 * All rights reserved.
 *
 * Do not copy without permission of the author.
 */
/*------------------------------------------------------------------------*/
%{
#if 0
#define YYSTYPE Node *		/* needed in y.tab.h !!!! */
#endif

#include "node.h"
#include "y.tab.h"

#include <stdio.h>

extern YYSTYPE yylval;
extern int yylineno;
%}
%%
[ \n\t]                 ;
""			;
"--".*\n                ;
"#".*\n                 sscanf(yytext,"# %d",&yylineno);
"MODULE"                return MODULE;
"DEFINE"                return DEFINE;
"VAR"                   return VAR;
"INIT"                  return INIT;
"TRANS"                 return TRANS;
"INVAR"                 return INVAR;
"ISA"			return ISA;
"SPEC"                  return SPEC;
"FAIRNESS"		return FAIRNESS;
"ASSIGN"                return ASSIGN;
"process"		return PROCESS;
"array"                 return ARRAY;
"of"                    return OF;
"boolean"               return BOOLEAN;
"EX"                    return EX;
"AX"                    return AX;
"EF"                    return EF;
"AF"                    return AF;
"EG"                    return EG;
"AG"                    return AG;
"E"                     return E;
"A"                     return A;
"U"                     return UNTIL;
"COMPUTE"		return COMPUTE;
"MIN"                   return MIN;
"MAX"                   return MAX;
"("                     return '(';
")"                     return ')';
"["                     return '[';
"]"                     return ']';
"{"                     return '{';
"}"                     return '}';
"FALSE"                 {
			  yylval.node = number(0);
			  return NUMBER;
                        }
"TRUE"                  {
			  yylval.node = number(1);
			  return NUMBER;
                        }
"case"                  return CASE;
"esac"                  return ESAC;
":="                    return EQDEF;
"+"                     return PLUS;
"-"                     return MINUS;
"*"                     return TIMES;
"/"                     return DIVIDE;
"mod"                   return MOD;
"="                     return EQUAL;
"!="                    return NOTEQUAL;
"<="                    return LE;
">="                    return GE;
"<"                     return LT;
">"                     return GT;
"next"                  return NEXT;
"init"                  return SMALLINIT;
"union"                 return UNION;
"in"                    return SETIN;
"notin"                 return SETNOTIN;
".."                    return TWODOTS;
"."                     return '.';
"->"                    return IMPLIES;
"<->"                   return IFF;
"|"                     return OR;
"&"                     return AND;
"!"                     return NOT;


[A-Za-z_][A-Za-z0-9_\$#-]*	{ yylval.node = atom(yytext); return ATOM; }

-?[0-9]+                  	{
				  int i;
				  sscanf(yytext,"%d",&i);
				  yylval.node = number(i);
				  return NUMBER;
				}

","                     return ',';
":"                     return ':';
";"                     return ';';
%%

int yywrap(void) { return 1; }

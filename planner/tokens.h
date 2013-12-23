/* A Bison parser, made by GNU Bison 2.5.  */

/* Bison interface for Yacc-like parsers in C
   
      Copyright (C) 1984, 1989-1990, 2000-2011 Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     LEFTPAR = 258,
     RIGHTPAR = 259,
     NAME = 260,
     TWODOTS = 261,
     HYPHEN = 262,
     EITHER = 263,
     DEFINE = 264,
     DOMAIN = 265,
     REQUIREMENTS = 266,
     CONSTANTS = 267,
     PREDICATES = 268,
     QUESTION = 269,
     STRIPS = 270,
     EQUALITY = 271,
     CONDITIONAL = 272,
     DOM_AXIOMS = 273,
     DISJUNCTIVE = 274,
     ADL = 275,
     E_PRECONDITIONS = 276,
     U_PRECONDITIONS = 277,
     AND = 278,
     NOT = 279,
     FORALL = 280,
     WHEN = 281,
     EQUAL = 282,
     ACTION = 283,
     PARAMETERS = 284,
     PRECONDITION = 285,
     EFFECT = 286,
     PROBLEM = 287,
     INIT = 288,
     GOAL = 289,
     LENGTH = 290,
     SITUATION = 291,
     OBJECTS = 292,
     SERIAL = 293,
     PARALLEL = 294,
     INTEGER = 295,
     TYPING = 296,
     TYPES = 297
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif

extern YYSTYPE yylval;



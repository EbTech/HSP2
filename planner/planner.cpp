/*
**
** Universidad Simon Bolivar, 1999, 2000 (c)
** Blai Bonet and Hector Geffner. 1999, 2000.
**
** Contributors: Hector L. Palacios
**
** Credits: code for h2max derived from Patrik Haslum's code.
**
** 2.0 revision log:
**
**      2/26/00 state bits packing, hsp and hspr fusion.
**      2/27/00 direct parsing of pddl files (i.e. no more C compilation, etc)
**      2/29/00 new flags "-m" for spec. restricted init. set of mutexs (default: all-pairs)
**      2/29/00 improved space management for mutexes.
**      2/29/00 Alpha version of the scheduler. New flag "-S <sched>". (its parsing not yet).
**      3/01/00 Static atoms removal. New flag "-s" for doing it.
**      3/03/00 Patch on mutex-compilation regarding staticAtoms.
**      3/04/00 Dynamic bucketTableSize.
**      3/04/00 Update printPath procedure for easier automatic extraction of plans.
**      3/04/00 Recode from scratch  heuristic computation. Now is more clean and better performance (?).
**      3/04/00 H^2_max heuristic added. H^2-plus is still pending.
**      3/05/00 Speedup of H^2-max. Improved space management for pair costs.
**      3/08/00 Use of h2max instead of mutexes, set static atoms removal as default.
**      3/08/00 Flags "-m" and "-s" removed.
**      3/10/00 Modify insertNodeIntoBucket to allow tie breaking strategies.
**      3/10/00 Clean of parameters usage and include schedule parsing:
**                  A schedule is of the form: <option1>:<option2>:<option3>:...
**                  where each <option> is of the form [<direction>,<heuristic>,<time>] in which
**                  <direction> is either "forward" or "backward", <heuristic> is one of "h1plus",
**                  "h1max", "h2plus", "h2max", "h1eplus", or "h1emax", and <time> is the number of msecs to run the option.
**      3/10/00 AIPS00 competition output format.
**      3/13/00 Change pair's cost representation after some profiling.
**      3/17/00 Fix error when instantiating operators: always allocate non-null prec, add, del lists.
**      3/17/00 Fix some errors messages.
**      3/22/00 Fix error in computation of h2max.
**      3/25/00 PriorityQueue implementation for h2plus.
**      3/25/00 Playing around with first versions of h2plus.
**      3/30/00 Cleanup parser
**      3/30/00 Added typing support to parser
**      4/??/00 Added simple-ADL suuport.
**      4/21/00 Change strcmp to strcasecmp so we don't need to do the patch over lexer
**      4/21/00 Start final distribution of HSP2
**
**
** Portability:
**
**      - I'm using gcc's lvalue trigraphs.
**
**
** Comments:
**
**      - lines marked with xxxx should be changed for more efficiency.
**
**/

#include <string>
#include <vector>
#include <algorithm>
#include <random>

extern "C"
{

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <csignal>
#include <ctime>
#include <climits>
#include <cassert>
#include <cstdbool>
#include <sys/types.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <strings.h>
#include <ulimit.h>
#include <unistd.h>
#include <fcntl.h>

#include "parser.h"
#include "planner.h"

using std::string;
using std::vector;
using std::min;
using std::max;



/*********************************************************
**********************************************************
**
** Global Variables
**
**/

/* for parsing */
char *              problemFile;
char *              domainFile;
int                 precPlusCost, precMaxCost;
char *              _low_yyfile;
int                 _low_requirements = 0;
char *              _low_problemName = nullptr;
char *              _low_domainName = nullptr;
char **             _low_schemaName;
char **             _low_objectName;
char **             _low_predicateName;
int                 _low_numberPredicates;
schema_t *          _low_schemaTable[MAXSCHEMA];
int                 _low_initialAtoms[ATOMSPERPACK*MAXATOMPACKS];
int                 _low_goalAtoms[ATOMSPERPACK*MAXATOMPACKS];
int                 _low_copyGoalAtoms[ATOMSPERPACK*MAXATOMPACKS];

/* fundamental global variables */
int                 numberAtomPacks;
int                 numberAtoms =  0;
int                 numberSchema = 0;
int                 numberOperators = 0;
int                 numberHOperators = 0;
int                 numberRelevantAtoms = 0;
int                 globalInitialized = 0;

/* for variables and domain instantiation */
int **              values;
int **              vars;

/* for operator info extraction */
int                 operatorPrec[1024];
int                 operatorPrecSize;
int                 operatorAdd[1024];
int                 operatorAddSize;
int                 operatorDel[1024];
int                 operatorDelSize;

/* for relevant atoms identification */
int *               parents[ATOMSPERPACK*MAXATOMPACKS];
int                 parentsSize[ATOMSPERPACK*MAXATOMPACKS];
atom_t              relevantAtom[MAXATOMPACKS];

/* for adl suboperators */
suboperator_t *     _low_suboperators;
int                 _low_groundingOperators;
int                 _low_negatedAtom[ATOMSPERPACK*MAXATOMPACKS];

/* for E-graphs */
string               StatisticsOut;
string               EGraphIn;
string               EGraphOut;
vector<experience_t> experience;
vector<atom_t*>      eNode;
vector<vector<cost_t> > eDist;
FILE* statsFile;



/*********************************************************
**********************************************************
**
** Static Variables
**
**/

/* atom hash table */
static iatom_t *    atomHashTable[ATOMHASHSIZE];
static iatom_t *    atomHashPool = nullptr;
static int          atomHashClaimSize = 0;

/* node hash table */
static node_t *     nodeHashTable[NODEHASHSIZE];
static int          nodeHashDiameter[NODEHASHSIZE];
static unsigned *   nodeHashValues;
static int          nodeHashNumElem = 0;

/* for mutexes */
static int *        _mutex;
static mutex_t *    mutexList = nullptr;
static mutexSet_t * mutexSet;
static mutexSet_t * mutexSetList = nullptr;
static int          numberMutexes = 0;

/* static atoms */
static int          numberStaticAtoms;
static atom_t       staticAtom[MAXATOMPACKS];
static int          staticAtomsList[ATOMSPERPACK*MAXATOMPACKS+1];

/* operator info */
static int          operatorTableSize = 0;
static operator_t * operatorTable = nullptr;
static int          HOperatorTableSize = 0;
static operator_t * HOperatorTable = nullptr;
static int *        validOperators;
static int **       invPrecTable;
static int *        invPrecTableSize;
static int **       invAddTable;
static int *        invAddTableSize;
static int **       invDelTable;
static int *        invDelTableSize;
static int **       notAdmissible;
static int *        notAdmissibleSize;
static int *        operatorsWithNoPrec = nullptr;
static int          operatorsWithNoPrecSize = 0;
static int *        HOperatorsWithNoPrec = nullptr;
static int          HOperatorsWithNoPrecSize = 0;
static int **       HInvPrecTable;
static int *        HInvPrecTableSize;
static int **       HInvAddTable;
static int *        HInvAddTableSize;
static int **       HSubTable;
static int *        HSubTableSize;

/* for node pool management */
static int          pageSize;
static char *       nodePool = nullptr;
static int          currentNodePool = -1;
static int          nodePoolClaimSize = 0;
static int *        nodePoolSize;
static char *       nodePoolUsed;
static int          nodePoolTableSize = 0;
static char **      nodePoolTable;

/* for Best-First Search */
static node_t *     headOPEN = nullptr;
static node_t *     tailOPEN = nullptr;
static node_t *     CLOSE = nullptr;
static node_t **    firstNodeInBucket = nullptr;
static node_t **    lastNodeInBucket = nullptr;
static int          bucketTableSize = 0;
static int          minBucket;
static int          maxBucket;
static int          nodesInOPEN = 0;
static int          nodesInCLOSE = 0;
static int          needRethreading = 0;

/* true initial state */
static atom_t       staticInitialState[MAXATOMPACKS];
static atom_t       staticGoalState[MAXATOMPACKS];

/* problem data */
static int          expandedNodes;
static int          generatedNodes;

/* for reachability analysis */
static atom_t       dummyAtom[MAXATOMPACKS];
static atom_t       reachableAtom[MAXATOMPACKS];

/* states workareas */
static atom_t       staticState[MAXATOMPACKS];

/* heuristics */
static int          H2Computed = 0;
static cost_t       H1Cost[ATOMSPERPACK*MAXATOMPACKS];
static cost_t       backwardH1Cost[ATOMSPERPACK*MAXATOMPACKS];
static cost_t       H1ECost[ATOMSPERPACK*MAXATOMPACKS];
static cost_t       backwardH1ECost[ATOMSPERPACK*MAXATOMPACKS];
static cost_t **    H2Cost;                            /* O(n^2) so we allocate it at runtime */

/* some global parameters */
static int          verbose;
static float        heuristicWeight;
static float        experienceWeight;
static int          searchAlgorithm;
static int          searchHeuristic;
static int          searchDirection;
static int          mutexesAllPairs;
static int          staticCompilation;
static char *       searchAlgorithmName[] = { "bfs", "gbfs" };
static char *       searchDirectionName[] = { "forward", "backward" };
static char *       searchHeuristicName[] = { "h1plus", "h1max", "h2plus", "h2max", "h2maxp", "h1eplus", "h1emax" };

/* schedules */
static long         nodeMemoryUsed;
static long         memoryConstraint;
static int          timeExpired;
static int          memoryExpired;
static schedule_t * globalSchedule = nullptr;
static char *       scheduleString = nullptr;

/* procedure registration stack */
static procRegister_t *procStackTop = nullptr;

/* random number generator */
std::random_device randomDevice;
//std::mt19937_64 rng(randomDevice());
std::mt19937_64 rng;



/*********************************************************
**********************************************************
**
** Function Prototypes
**
**/

void                newMutex( int, int, mutex_t ** );
void                delMutex( mutex_t * );
void                newMutexSet( int );

void                identifyGoalParents( int * );
void                printNode( FILE *, char *, node_t * );
void                resizeBucketTable( int min_size );
void                removeNodeFromOPEN( node_t * );
node_t *            removeLastFromOPEN( node_t * );
node_t *            removeNodeFromCLOSE( void  );

node_t *            BFS( schedule_t * );
node_t *            GBFS( schedule_t * );

void                generateHOperators( void );
char *              operatorName( int *, int );
char *              readAtomName( int );
iatom_t *           readAtomByNumber( int );
void                orderAtomList( int *, int );
void                printState( FILE *, atom_t * );
void                registerEntry( char * );
int                 registerExit( void );
void                flushAllRegisters( void );

void                notYetImplemented( schedule_t * );
void                _fatal( int, char *, char *, int );
void                printStatistics( void );
void                setTimer( unsigned long );

int                 stateCmp( atom_t *state1, atom_t *state2 );

/* state bits packing */
int asserted(atom_t* s, int b)
{
  return s[b/ATOMSPERPACK].pack & (1<<(b%ATOMSPERPACK));
}
void set(atom_t* s, int b)
{
  s[b/ATOMSPERPACK].pack |= (1<<(b%ATOMSPERPACK));
}
void clear(atom_t* s, int b)
{
  s[b/ATOMSPERPACK].pack &= ~(1<<(b%ATOMSPERPACK));
}

/*********************************************************
**********************************************************
**
** Operator Instantiation
**
**/

void
buildParameterList( int *parameters, int schema, int *ip,
                    void (*insertOperator)( int *, int ),
                    int (*testOperatorPrecondition)( int *, int ) )
{
  int *jp;
  
  if( *ip != 0 )
    {
      for( int* vp = values[numberSchema * (*ip - 1) + schema]; *vp != 0; ++vp )
        {
#if 0 /* instantiate objects with restrictions on equality */
          if( !(_low_requirements & REQ_EQUALITY) )
            {
              for( jp = &parameters[1]; jp < &parameters[MAXPARAMETERS]; ++jp )
                if( (*jp > 0) && (*jp == *vp) )
                  break;
            }
          else
            jp = &parameters[MAXPARAMETERS];

          if( jp == &parameters[MAXPARAMETERS] )
            {
              parameters[*ip] = *vp;
              if( (*testOperatorPrecondition)( parameters, schema ) )
                buildParameterList( parameters, schema, ip + 1, insertOperator, testOperatorPrecondition );
            }
#else
          parameters[*ip] = *vp;
          if( (*testOperatorPrecondition)( parameters, schema ) )
            buildParameterList( parameters, schema, ip + 1, insertOperator, testOperatorPrecondition );
#endif
        }
      parameters[*ip] = 0;
    }
  else
    {
      if( (*testOperatorPrecondition)( parameters, schema ) )
        {
          /* insert delimiting marker */
          for( jp = parameters; *jp > 0; ++jp );
          *jp = -1;

          /* insert operator */
          (*insertOperator)( parameters, schema );
        }
    }
}


void
instantiateOperators( void (*insertOperator)( int *, int ),
                      int (*testOperatorPrecondition)( int *, int ) )
{
  static int parameters[MAXPARAMETERS];

  for( int schema = 0; schema < numberSchema; ++schema )
    {
      memset( parameters, 0, MAXPARAMETERS * sizeof( int ) );
      parameters[0] = schema + 1;
      buildParameterList( parameters, schema, vars[schema], insertOperator, testOperatorPrecondition );
    }
}



/*********************************************************
**********************************************************
**
** Reachability Analysis
**
**/

void
removeDuplicates( int *list, int *size )
{
  for( int* p = list; *p != 0; ++p ) {
    for( int* q = p+1; *q != 0; ++q ) {
      if( *p == *q ) {
        int* last = &list[*size-1];
        *q = *last;
        *last = 0;
        --*size;
      }
    }
  }
}

int
testOperatorPrecondition( int *parameters, int schema )
{
  extern int evaluateFormula( void *, atom_t *, int *, int );

  int rv = evaluateFormula( _low_schemaTable[schema]->prec, reachableAtom, parameters, 0 );
  return( rv );
}


void
insertOperator( int *parameters, int schema )
{
  int *add, *del, *last_add, *last_del;
  extern int  applyOperatorSchema( schema_t *, atom_t *, atom_t *, int * );
  extern void instantiateConditionalEffects( int, schema_t *, int * );

  if( _low_groundingOperators == 0 )
    {
      applyOperatorSchema( _low_schemaTable[schema], reachableAtom, reachableAtom, parameters );
    }
  else
    {
      if( applyOperatorSchema( _low_schemaTable[schema], reachableAtom, staticState, parameters ) )
        {
          /* resize operatorTable */
          if( numberOperators == operatorTableSize )
            {
              operatorTableSize = (operatorTableSize == 0 ? 16 : INCRATE * operatorTableSize);
              operatorTable =
                (operator_t*)realloc( operatorTable, operatorTableSize * sizeof( operator_t ) );
              if( !operatorTable )
                fatal( noMoreMemory );
            }

          /* remove duplicates */
          removeDuplicates(operatorPrec,&operatorPrecSize);
          removeDuplicates(operatorAdd,&operatorAddSize);
          removeDuplicates(operatorDel,&operatorDelSize);

          /* remove atoms that appear at the same time in the add and del lists */
          last_add = &operatorAdd[operatorAddSize-1];
          last_del = &operatorDel[operatorDelSize-1];
          for( add = operatorAdd; *add != 0; ++add ) {
            for( del = operatorDel; *del != 0; ++del ) {
              if( *add == *del ) {
                *add = *last_add;
                *del = *last_del;
                *last_add-- = 0;
                *last_del-- = 0;
                --operatorAddSize;
                --operatorDelSize;
                --add;
                break;
              }
            }
          }

          /* space allocation for precondition, add, del lists */
          operatorTable[numberOperators].precSize = operatorPrecSize;
          operatorTable[numberOperators].addSize = operatorAddSize;
          operatorTable[numberOperators].delSize = operatorDelSize;
          operatorTable[numberOperators].prec = (int*)calloc( operatorPrecSize + 1, sizeof( int ) );
          operatorTable[numberOperators].add = (int*)calloc( operatorAddSize + 1, sizeof( int ) );
          operatorTable[numberOperators].del = (int*)calloc( operatorDelSize + 1, sizeof( int ) );
          if( !operatorTable[numberOperators].prec || !operatorTable[numberOperators].add ||
              !operatorTable[numberOperators].del )
            fatal( noMoreMemory );

          /* order Prec, Add, and Del lists */
          orderAtomList( operatorPrec, operatorPrecSize );
          orderAtomList( operatorAdd, operatorAddSize );
          orderAtomList( operatorDel, operatorDelSize );

          /* fill it */
          memcpy( operatorTable[numberOperators].prec, operatorPrec, (operatorPrecSize+1) * sizeof( int ) );
          memcpy( operatorTable[numberOperators].add, operatorAdd, (operatorAddSize+1) * sizeof( int ) );
          memcpy( operatorTable[numberOperators].del, operatorDel, (operatorDelSize+1) * sizeof( int ) );
          operatorTable[numberOperators].name = strdup( operatorName( parameters, schema ) );
          operatorTable[numberOperators].valid = 1;

          /* fill operatorsWithNoPrec table */
          if( operatorPrecSize == 0 )
            {
              ++operatorsWithNoPrecSize;
              operatorsWithNoPrec =
                (int*)realloc( operatorsWithNoPrec, operatorsWithNoPrecSize * sizeof( int ) );
              operatorsWithNoPrec[operatorsWithNoPrecSize-1] = numberOperators;
            }

          /* generate suboperators */
          _low_suboperators = nullptr;
          instantiateConditionalEffects( numberOperators, _low_schemaTable[schema], parameters );
          operatorTable[numberOperators].suboperators = _low_suboperators;

          /* next operator */
          ++numberOperators;
        }
    }
}


void
reachabilityAnalysis( atom_t *state )
{
  /* basic initialization */
  _low_groundingOperators = 0;
  memset( _low_negatedAtom, 0, MAXATOMPACKS * ATOMSPERPACK * sizeof( int ) );

  /* initialize costs with given state */
  memcpy( reachableAtom, state, MAXATOMPACKS * sizeof( atom_t ) );
  memcpy( dummyAtom, state, MAXATOMPACKS * sizeof( atom_t ) );

  /* computation of reachable atoms */
  for ( int number = 1; number != 0; )
    {
      instantiateOperators( &insertOperator, &testOperatorPrecondition );
      number = memcmp( dummyAtom, reachableAtom, MAXATOMPACKS * sizeof( atom_t ) );
      memcpy( dummyAtom, reachableAtom, MAXATOMPACKS * sizeof( atom_t ) );
    }

  /* print reachable atoms */
  if( verbose > 7 )
    {
      for( size_t i = 1; i < SIZE_ATOMS; ++i )
        if( asserted( reachableAtom, i ) )
          fprintf( stderr, "atom %s is reachable from initial state\n", readAtomByNumber( i )->name );
    }
}



/*********************************************************
**********************************************************
**
** Heuristics
**
**/

void
H1SetCost( cost_t *cost, int* set )
{
  cost->max = 0;
  cost->plus = 0;
  for( int* p = set; *p != 0; ++p )
    {
      cost->max = max( H1Cost[*p].max, cost->max );
      cost->plus = PLUSSUM( H1Cost[*p].plus, cost->plus );
    }
}


void
H1Setup( atom_t *state )
{
  int change;
  unsigned long minCostMax, minCostPlus;
  cost_t tmpCost;

  /* initial costs */
  for( size_t p = 1; p < SIZE_ATOMS; ++p )
    if( asserted( state, p ) )
      {
        H1Cost[p].max = 0;
        H1Cost[p].plus = 0;
      }
    else
      {
        H1Cost[p].max = INT_MAX;
        H1Cost[p].plus = INT_MAX;
      }

  /* use dynamic programming for computing the remaining costs */
  change = 1;
  while( change )
    {
      /* clean state */
      change = 0;

      /* single full backup for { p } */
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        {
          minCostMax = INT_MAX;
          minCostPlus = INT_MAX;
          if( !(_low_requirements & REQ_ADL) )
            {
              for( int* op = invAddTable[p]; (op != nullptr) && (*op != 0); ++op )
                {
                  H1SetCost( &tmpCost, operatorTable[(*op)-1].prec );
                  minCostMax = min( minCostMax, tmpCost.max );
                  minCostPlus = min( minCostPlus, tmpCost.plus );
                }
            }
          else
            {
              for( int* op = HInvAddTable[p]; (op != nullptr) && (*op != 0); ++op )
                {
                  H1SetCost( &tmpCost, HOperatorTable[(*op)-1].prec );
                  minCostMax = min( minCostMax, tmpCost.max );
                  minCostPlus = min( minCostPlus, tmpCost.plus );
                }
            }
          minCostMax = PLUSSUM( minCostMax, 1 );
          minCostPlus = PLUSSUM( minCostPlus, 1 );

          /* update max cost */
          if( H1Cost[p].max > minCostMax )
            {
              change = 1;
              H1Cost[p].max = minCostMax;
            }

          /* update plus cost */
          if( H1Cost[p].plus > minCostPlus )
            {
              change = 1;
              H1Cost[p].plus = minCostPlus;
            }
          assert( H1Cost[p].plus != INT_MAX || H1Cost[p].max == INT_MAX );
        }
    }

  /* print costs */
  if( verbose > 7 )
    {
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        if( (H1Cost[p].plus < INT_MAX) || (verbose >= 10) )
          fprintf( stderr, "cost of %s is (%lu,%lu)\n", readAtomByNumber( p )->name,
                   H1Cost[p].plus, H1Cost[p].max );
    }
}


void
H2SetCost( cost_t *cost, int *set, int *extra )
{
  /* go over all pairs: compute max cost & build PQ with plus costs */
  cost->max = 0;
  cost->plus = 0;
  for( int* p = set; *p != 0; ++p )
    for( int* q = p; *q != 0; ++q )
      cost->max = max( PAIR( *p, *q ).max, cost->max );

  if( extra != nullptr )
    for( int* p = extra; *p != 0; ++p )
      for( int* q = p; *q != 0; ++q )
        cost->max = max( PAIR( *p, *q ).max, cost->max );
}


void
H2Setup( atom_t *state )
{
  int change, localChange;

  static int initialized = 0;
  static char *display;

  /* registry */
  registerEntry( "H2Setup()" );

  /* initialization */
  if( !initialized )
    {
      initialized = 1;
      H2Cost = (cost_t**)calloc( SIZE_ATOMS, sizeof( cost_t* ) );
      display = (char*)malloc( numberOperators * sizeof( char ) );
      if( !H2Cost || !display )
        fatal( noMoreMemory );

      for( size_t p = 1, q = SIZE_ATOMS; p < SIZE_ATOMS; ++p, --q )
        if( (H2Cost[p] = (cost_t*)calloc( q, sizeof( cost_t ) )) == nullptr )
          fatal( noMoreMemory );
    }

  /* initial pair's costs */
  memset( display, 0, numberOperators * sizeof( char ) );
  for( size_t p = 1; p < SIZE_ATOMS; ++p )
    for( size_t q = p; q < SIZE_ATOMS; ++q )
      if( asserted( state, p ) && asserted( state, q) )
        {
          PAIR( p, q ).max = 0;
          PAIR( p, q ).plus = 0;
        }
      else
        {
          PAIR( p, q ).max = INT_MAX;
          PAIR( p, q ).plus = INT_MAX;
        }

  /* initially, add all operators */
  for( size_t op = 0; op < numberOperators; ++op )
    display[op] = 1;

  /* use dynamic programming for computing the pair's costs */
  change = 1;
  while( change )
    {
      /* clean state */
      change = 0;

      /* outer loop over all operators. Inner loops over their Add/Del lists */
      for( size_t op = 0; op < numberOperators; ++op )
        if( (operatorTable[op].valid == 1) && (display[op] == 1) )
          {
            /* clean display */
            display[op] = 0;

            /* compute the H2 value of the preconditions, and check if we are going to
               do something useful.
            */
            cost_t precCost;
            H2SetCost( &precCost, operatorTable[op].prec, nullptr );
            unsigned long maxCost1 = PLUSSUM( precCost.max, 1 );
            if( maxCost1 == INT_MAX )
              continue;

            /* update for pairs { *a, *t } such that *t is in Add (this includes singleton { *a }) */
            for( int* a = operatorTable[op].add; *a != 0; ++a )
              {
                localChange = 0;
                for( int* t = a; *t != 0; ++t )
                  if( PAIR( *a, *t ).max > maxCost1 )
                    {
                      change = 1;
                      localChange = 1;
                      PAIR( *a, *t ).max = maxCost1;

                      for( int* op2 = invPrecTable[*t]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                        display[(*op2)-1] = 1;

                      /* if singleton updated, flag all operators */
                      if( *a == *t )
                        {
                          localChange = 0;
                          for( size_t p = 0; p < numberOperators; ++p )
                            display[p] = 1;
                        }
                    }

                /* set display */
                if( localChange == 1 )
                  {
                    localChange = 0;
                    for( int* op2 = invPrecTable[*a]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                      display[(*op2)-1] = 1;

                    /* also, add all operators with null preconditions */
                    for( size_t p = 0; p < operatorsWithNoPrecSize; ++p )
                      display[operatorsWithNoPrec[p]] = 1;
                  }
              }

            /* update for pairs { q, *a } such that q is not in Del/Add */
            for( int q = 1; q < SIZE_ATOMS; ++q )
              {
                /* precompute updated cost and check if we really need to do the update */
                localChange = 0;
                unsigned long maxCost2 = max( precCost.max, PAIR( q, q ).max );
                if( maxCost2 == INT_MAX )
                  continue;

                /* ok, check that q is not affected by the operator */
                int* t;
                for( t = operatorTable[op].del; (t != nullptr) && (*t != 0) && (*t != q); ++t);
                if( (t == nullptr) || (*t == 0) )
                  for( t = operatorTable[op].add; (t != nullptr) && (*t != 0) && (*t != q); ++t);
                if( (t != nullptr) && (*t == 0) )
                  {
                    /* finish computing of cost */
                    for( t = operatorTable[op].prec; *t != 0; ++t )
                      maxCost2 = max( PAIR( q, *t ).max, maxCost2 );
                    maxCost2 = PLUSSUM( maxCost2, 1 );
                    if( maxCost2 < INT_MAX )
                      {
                        /* update cost for { *a, q } */
                        for( int* a = operatorTable[op].add; *a != 0; ++a )
                          if( PAIR( *a, q ).max > maxCost2 )
                            {
                              change = 1;
                              localChange = 1;
                              PAIR( *a, q ).max = maxCost2;

                              assert( *a != q );
                              for( int* op2 = invPrecTable[*a]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                                display[(*op2)-1] = 1;
                            }
                      }
                  }

                /* set display */
                if( localChange == 1 )
                  {
                    localChange = 0;
                    for( int* op2 = invPrecTable[q]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                      display[(*op2)-1] = 1;

                    /* also, add all operators with null preconditions */
                    for( size_t p = 0; p < operatorsWithNoPrecSize; ++p )
                      display[operatorsWithNoPrec[p]] = 1;
                  }
              }
          }
    }

  /* print pair's costs */
  if( verbose > 7 )
    {
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        for( size_t q = p; q < SIZE_ATOMS; ++q )
          if( PAIR( p, q ).max < INT_MAX )
            {
              assert( PAIR( p, q ).max == PAIR( p, q ).max );
              fprintf( stderr, "cost of { %s, %s } is (%lu,%lu)\n", readAtomByNumber( p )->name,
                       readAtomByNumber( q )->name, PAIR( p, q ).plus, PAIR( p, q ).max );
            }
          else
            {
              fprintf( stderr, "cost of { %s, %s } is infinite\n", readAtomByNumber( p )->name,
                       readAtomByNumber( q )->name );
            }
    }

  /* set flag */
  H2Computed = 1;
  registerExit();
}


void
H1ESetCost( cost_t *cost, int* set )
{
  cost->max = 0;
  cost->plus = 0;
  for( int* p = set; *p != 0; ++p )
    {
      cost->max = max( H1ECost[*p].max, cost->max );
      cost->plus = PLUSSUM( H1ECost[*p].plus, cost->plus );
    }
}


void
H1ESetup( atom_t *state )
{
  int change;
  unsigned long minCostMax, minCostPlus;
  cost_t tmpCost;

  /* initial costs */
  for( size_t p = 1; p < SIZE_ATOMS; ++p )
    if( asserted( state, p ) )
      {
        H1ECost[p].max = 0;
        H1ECost[p].plus = 0;
      }
    else
      {
        H1ECost[p].max = INT_MAX;
        H1ECost[p].plus = INT_MAX;
      }

  /* use dynamic programming for computing the remaining costs */
  change = 1;
  while( change )
    {
      /* clean state */
      change = 0;

      /* single full backup for { p } */
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        {
          
          minCostMax = INT_MAX;
          minCostPlus = INT_MAX;
          if( !(_low_requirements & REQ_ADL) )
            {
              for( int* op = invAddTable[p]; (op != nullptr) && (*op != 0); ++op )
                {
                  /*int alpha = 10;
                  for (q = 0; q < experienceSize && alpha > 1; ++q)
                  {
                    if (asserted(experience[q].headState, p) && !strcmp(experience[q].opName, operatorTable[(*op)-1].name))
                      alpha = 1;
                  }*/
                  H1ESetCost( &tmpCost, operatorTable[(*op)-1].prec );
                  minCostMax = min( minCostMax, PLUSSUM(tmpCost.max, 1) );
                  minCostPlus = min( minCostPlus, PLUSSUM(tmpCost.plus, 1) );
                }
            }
          else
            {
              for( int* op = HInvAddTable[p]; (op != nullptr) && (*op != 0); ++op )
                {
                  /*int alpha = 10;
                  for (q = 0; q < experienceSize && alpha > 1; ++q)
                  {
                    if (asserted(experience[q].headState, p) && !strcmp(experience[q].opName, HOperatorTable[(*op)-1].name))
                      alpha = 1;
                  }*/
                  H1ESetCost( &tmpCost, HOperatorTable[(*op)-1].prec );
                  minCostMax = min( minCostMax, PLUSSUM(tmpCost.max, 1) );
                  minCostPlus = min( minCostPlus, PLUSSUM(tmpCost.plus, 1) );
                }
            }

          /* update max cost */
          if( H1ECost[p].max > minCostMax )
            {
              change = 1;
              H1ECost[p].max = minCostMax;
            }

          /* update plus cost */
          if( H1ECost[p].plus > minCostPlus )
            {
              change = 1;
              H1ECost[p].plus = minCostPlus;
            }
          assert( H1ECost[p].plus != INT_MAX || H1ECost[p].max == INT_MAX );
        }
    }

  /* print costs */
  if( verbose > 7 )
    {
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        if( (H1ECost[p].plus < INT_MAX) || (verbose >= 10) )
          fprintf( stderr, "cost of %s is (%lu,%lu)\n", readAtomByNumber( p )->name,
                   H1ECost[p].plus, H1ECost[p].max );
    }
}


void
ADLH2Setup( atom_t *state )
{
  int change, localChange;
  unsigned long maxCost1, maxCost2;
  cost_t precCost;

  static int initialized = 0;
  static char *display1, *display2;

  /* initialization */
  if( !initialized )
    {
      initialized = 1;
      H2Cost = (cost_t**)calloc( SIZE_ATOMS, sizeof( cost_t* ) );
      display1 = (char*)malloc( numberHOperators * sizeof( char ) );
      display2 = (char*)malloc( numberOperators * sizeof( char ) );
      if( !H2Cost || !display1 || !display2 )
        fatal( noMoreMemory );

      for( size_t p = 1, q = SIZE_ATOMS; p < SIZE_ATOMS; ++p, --q )
        if( (H2Cost[p] = (cost_t*)malloc( q * sizeof( cost_t ) )) == nullptr )
          fatal( noMoreMemory );
    }

  /* initial pair's costs */
  memset( display1, 0, numberHOperators * sizeof( char ) );
  memset( display2, 0, numberHOperators * sizeof( char ) );
  for( size_t p = 1; p < SIZE_ATOMS; ++p )
    for( size_t q = p; q < SIZE_ATOMS; ++q )
      if( asserted( state, p ) && asserted( state, q ) )
        PAIR( p, q ).max = 0;
      else
        PAIR( p, q ).max = INT_MAX;

  /* initially, add all operators */
  for( size_t op = 0; op < numberHOperators; ++op )
    display1[op] = 1;
  for( size_t op = 0; op < numberOperators; ++op )
    display2[op] = 1;

  /* use dynamic programming for computing the pair's costs */
  change = 1;
  while( change )
    {
      /* clean state */
      change = 0;

      /* outer loop over all operators. Inner loops over their Add/Del lists */
      for( size_t op = 0; op < numberHOperators; ++op )
        if( (HOperatorTable[op].valid == 1) && (display1[op] == 1) )
          {
            /* clean display */
            display1[op] = 0;

            /* compute the H2 value of the preconditions, and check if we are going to
               do something useful.
            */
            H2SetCost( &precCost, HOperatorTable[op].prec, nullptr );
            maxCost1 = PLUSSUM( precCost.max, 1 );
            if( maxCost1 == INT_MAX )
              continue;

            /* update for pairs { *a, *t } such that *t is in Add (this includes singleton { *a }) */
            for( int* a = HOperatorTable[op].add; *a != 0; ++a )
            {
              localChange = 0;
              for( int* t = a; *t != 0; ++t )
                if( PAIR( *a, *t ).max > maxCost1 )
                {
                  change = 1;
                  localChange = 1;
                  PAIR( *a, *t ).max = maxCost1;

                  for( int* op2 = HInvPrecTable[*t]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                  {
                    display1[(*op2)-1] = 1;
                    display2[HOperatorTable[(*op2)-1].father] = 1;
                  }

                  /* if singleton updated, flag all operators */
                  if( *a == *t )
                  {
                    localChange = 0;
                    for( size_t p = 0; p < numberHOperators; ++p )
                      display1[p] = 1;
                    for( size_t p = 0; p < numberOperators; ++p )
                      display2[p] = 1;
                  }
                }

              /* set display */
              if( localChange == 1 )
              {
                localChange = 0;
                for( int* op2 = HInvPrecTable[*a]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                  {
                    display1[(*op2)-1] = 1;
                    display2[HOperatorTable[(*op2)-1].father] = 1;
                  }

                /* also, add all operators with null preconditions */
                for( size_t p = 0; p < HOperatorsWithNoPrecSize; ++p )
                  display1[HOperatorsWithNoPrec[p]] = 1;
                for( size_t p = 0; p < operatorsWithNoPrecSize; ++p )
                  display2[operatorsWithNoPrec[p]] = 1;
              }
            }

            /* update for pairs { q, *a } such that q is not in Del/Add */
            for( int q = 1; q < SIZE_ATOMS; ++q )
            {
              /* precompute updated cost and check if we really need to do the update */
              localChange = 0;
              maxCost2 = max( precCost.max, PAIR( q, q ).max );
              if( maxCost2 == INT_MAX )
                continue;

              /* ok, check that q is not affected by the operator */
              int* t;
              for( t = HOperatorTable[op].del; (t != nullptr) && (*t != 0) && (*t != q); ++t);
              if( (t == nullptr) || (*t == 0) )
                for( t = HOperatorTable[op].add; (t != nullptr) && (*t != 0) && (*t != q); ++t);
              if( (t != nullptr) && (*t == 0) )
              {
                /* finish computing of cost */
                for( t = HOperatorTable[op].prec; *t != 0; ++t )
                  maxCost2 = max( PAIR( q, *t ).max, maxCost2 );
                maxCost2 = PLUSSUM( maxCost2, 1 );
                if( maxCost2 < INT_MAX )
                {
                  /* update cost for { *a, q } */
                  for( int* a = HOperatorTable[op].add; *a != 0; ++a )
                    if( PAIR( *a, q ).max > maxCost2 )
                    {
                      change = 1;
                      localChange = 1;
                      PAIR( *a, q ).max = maxCost2;
                      assert( *a != q );
                      for( int* op2 = HInvPrecTable[*a]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                      {
                        display1[(*op2)-1] = 1;
                        display2[HOperatorTable[(*op2)-1].father] = 1;
                      }
                    }
                }
              }

              /* set display */
              if( localChange == 1 )
              {
                localChange = 0;
                for( int* op2 = HInvPrecTable[q]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                {
                  display1[(*op2)-1] = 1;
                  display2[HOperatorTable[(*op2)-1].father] = 1;
                }

                /* also, add all operators with null preconditions */
                for( size_t p = 0; p < HOperatorsWithNoPrecSize; ++p )
                  display1[HOperatorsWithNoPrec[p]] = 1;
                for( size_t p = 0; p < operatorsWithNoPrecSize; ++p )
                  display2[operatorsWithNoPrec[p]] = 1;
              }
            }
          }

      /* now, loop over all operators for the 'parallel' action term */
      for( size_t op = 0; op < numberOperators; ++op )
        if( (operatorTable[op].valid == 1) && (display2[op] == 1) )
          {
            int *s1, *s2, *e1, *e2;

            display2[op] = 0;
            for( s1 = HSubTable[op]; (s1 != nullptr) && (*s1 != 0); ++s1 )
              for( s2 = s1 + 1; *s2 != 0; ++s2 )
                {
                  /* check if consistent and relevant */
                  for( e1 = HOperatorTable[(*s1)-1].add; (e1 != nullptr) && (*e1 != 0); ++e1 )
                    {
                      for( e2 = HOperatorTable[(*s2)-1].del; (e2!=nullptr) && (*e2!=0) && (*e2!=*e1); ++e2 );
                      if( (e1 != nullptr) && (*e2 != 0) )
                        break;
                    }
                  if( (e1 != nullptr) && (*e1 != 0) )
                    continue;

                  for( e1 = HOperatorTable[(*s2)-1].add; (e1 != nullptr) && (*e1 != 0); ++e1 )
                    {
                      for( e2 = HOperatorTable[(*s1)-1].del; (e2!=nullptr) && (*e2!=0) && (*e2!=*e1); ++e2 );
                      if( (e1 != nullptr) && (*e2 != 0) )
                        break;
                    }
                  if( (e1 != nullptr) && (*e1 != 0) )
                    continue;

                  /* precompute cost */
                  H2SetCost( &precCost, HOperatorTable[(*s1)-1].prec, HOperatorTable[(*s2)-1].prec );
                  maxCost1 = PLUSSUM( precCost.max, 1 );
                  if( maxCost1 == INT_MAX )
                    continue;

                  /* update costs */
                  for( int* a = HOperatorTable[(*s1)-1].add; *a != 0; ++a )
                    {
                      localChange = 0;
                      for( int* t = HOperatorTable[(*s2)-1].add; *t != 0; ++t )
                        if( PAIR( *a, *t ).max > maxCost1 )
                          {
                            change = 1;
                            localChange = 1;
                            PAIR( *a, *t ).max = maxCost1;
                            for( int* op2 = HInvPrecTable[*t]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                              {
                                display1[(*op2)-1] = 1;
                                display2[HOperatorTable[(*op2)-1].father] = 1;
                              }

                            /* if singleton updated, flag all operators */
                            if( *a == *t )
                              {
                                localChange = 0;
                                for( size_t p = 0; p < numberHOperators; ++p )
                                  display1[p] = 1;
                                for( size_t p = 0; p < numberOperators; ++p )
                                  display2[p] = 1;
                              }
                          }

                      /* set display */
                      if( localChange == 1 )
                        {
                          localChange = 0;
                          for( int* op2 = HInvPrecTable[*a]; (op2 != nullptr) && (*op2 != 0); ++op2 )
                            {
                              display1[(*op2)-1] = 1;
                              display2[HOperatorTable[(*op2)-1].father] = 1;
                            }

                          /* also, add all operators with null preconditions */
                          for( size_t p = 0; p < HOperatorsWithNoPrecSize; ++p )
                            display1[HOperatorsWithNoPrec[p]] = 1;
                          for( size_t p = 0; p < operatorsWithNoPrecSize; ++p )
                            display2[operatorsWithNoPrec[p]] = 1;
                        }
                    }
                }
          }
    }

  /* print pair's costs */
  if( verbose > 7 )
    {
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        for( size_t q = p; q < SIZE_ATOMS; ++q )
          if( PAIR( p, q ).max < INT_MAX )
            {
              assert( PAIR( p, q ).max == PAIR( p, q ).max );
              fprintf( stderr, "cost of { %s, %s } is (%lu,%lu)\n", readAtomByNumber( p )->name,
                       readAtomByNumber( q )->name, PAIR( p, q ).plus, PAIR( p, q ).max );
            }
          else
            {
              fprintf( stderr, "cost of { %s, %s } is infinite\n", readAtomByNumber( p )->name,
                       readAtomByNumber( q )->name );
            }
    }

  /* set flag */
  H2Computed = 1;
}


void
runtimeH2Cost( cost_t *cost, int* set )
{
  /* go over all pairs: compute max cost & build PQ with plus costs */
  cost->max = 0;
  cost->plus = 0;
  for( int* p = set; *p != 0; ++p )
    for( int* q = p; *q != 0; ++q )
      cost->max = max( PAIR( *p, *q ).max, cost->max );
}


void
H2Heuristics( cost_t *cost, atom_t *state )
{
  static int atomSet[ATOMSPERPACK*MAXATOMPACKS+1];

  if( !(_low_requirements & REQ_ADL) )
    {
      /* build set of atoms */
      int* s = atomSet;
      for( size_t i = 1; i < SIZE_ATOMS; ++i )
        if( asserted( state, i ) )
          *s++ = i;
      *s = 0;

      /* call H2SetCost over the set */
      runtimeH2Cost( cost, atomSet );
    }
  else
    {
      runtimeH2Cost( cost, _low_goalAtoms );
    }
}


void
heuristics( node_t *node )
{
  cost_t tmpCost;

  /* initialization */
  node->h1_plus = 0;
  node->h2_plus = 0;
  node->h1_max = 0;
  node->h2_max = 0;
  node->h1e_plus = INT_MAX;
  node->h1e_max = INT_MAX;
  node->valid = 1;

  if( searchDirection == FORWARD )
    {
      /* need recompute heuristic cost from scratch */
      H1Setup( node->state );
      H1ESetup( node->state );

      /* add/max the costs for atoms in goal */
      for( int* g = _low_goalAtoms; *g != 0; ++g )
        if( H1Cost[*g].plus == INT_MAX )
          {
            node->h1_plus = -1;
            node->h1_max = -1;
            node->h2_max = -1;
            node->valid = 0;
            return;
          }
        else
          {
            node->h1_plus = PLUSSUM( node->h1_plus, H1Cost[*g].plus );
            node->h1_max = max( node->h1_max, H1Cost[*g].max );
          }
      
      node->h1e_plus *= experienceWeight;
      node->h1e_max *= experienceWeight;
      
      for ( size_t i = 0; i < eNode.size(); ++i )
      if ( eDist[i][0].plus < node->h1e_plus || eDist[i][0].max < node->h1e_max )
        {
          cost_t saDist;
          saDist.plus = saDist.max = 0;
          for( size_t p = 1; p < SIZE_ATOMS; ++p )
          if( asserted( eNode[i], p ) )
            { 
              if( H1ECost[p].plus == INT_MAX )
                {
                  saDist.plus = INT_MAX;
                  saDist.max = INT_MAX;
                  break;
                }
              else
                {
                  saDist.plus = PLUSSUM( saDist.plus, H1ECost[p].plus );
                  saDist.max = max( saDist.max, H1ECost[p].max );
                }
            }
          if (saDist.plus != INT_MAX)
          {
            node->h1e_plus = min(node->h1e_plus, (unsigned long) experienceWeight*saDist.plus + eDist[i][0].plus);
            node->h1e_max = min(node->h1e_max, (unsigned long) experienceWeight*saDist.max + eDist[i][0].max);
          }
        }
      
      // TODO remove debug code
      /*fprintf( stdout, "GENERATE node with h=%d:\t", node->h1e_max );
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        if( asserted( node->state, p ) )
        {
          fprintf( stdout, "%s ", readAtomName(p) );
        }
      fprintf( stdout, "\n" );*/

      /* H2 heuristics are too expensice for forward search */
      if( (_low_requirements & REQ_ADL) && (searchHeuristic == H2MAX) )
        {
          ADLH2Setup( node->state );
          H2Heuristics( &tmpCost, node->state );
          node->h2_plus = tmpCost.plus;
          node->h2_max = tmpCost.max;
          assert( node->h2_max >= node->h1_max );
          /*
            assert( !(node->h1_plus == 0) || (node->h2_max == 0) );
          */
        }
    }
  else
    {
      /* add/max the costs for atoms in node */
      for( size_t i = 1; i < SIZE_ATOMS; ++i )
        if( asserted( node->state, i ) )
          {
            if( backwardH1Cost[i].plus == INT_MAX )
              {
                node->h1_plus = -1;
                node->h1_max = -1;
                node->h1e_plus = -1;
                node->h1e_max = -1;
                node->valid = 0;
                return;
              }
            else
              {
                node->h1_plus = PLUSSUM( node->h1_plus, backwardH1Cost[i].plus );
                node->h1_max = max( node->h1_max, backwardH1Cost[i].max );
                node->h1e_plus = PLUSSUM( node->h1e_plus, backwardH1ECost[i].plus );
                node->h1e_max = max( node->h1e_max, backwardH1ECost[i].max );
              }
          }

      /* H2 heuristics */
      if( H2Computed == 1 )
        {
          H2Heuristics( &tmpCost, node->state );
          node->h2_plus = tmpCost.plus;
          node->h2_max = tmpCost.max;
          assert( node->h2_max >= node->h1_max );
          assert( !(node->h1_plus == 0) || (node->h2_max == 0) );
        }
    }

  /* use H2 to update valid bit */
  node->valid = node->valid && (node->h2_max < INT_MAX);
}



/*********************************************************
**********************************************************
**
** Atoms and Operators names
**
**/

char *
operatorName( int *parameters, int schema )
{
  int *ip;
  static char name[128];

  name[0] = '(';
  name[1] = '\0';
  strcat( name, _low_schemaName[schema] );
  for( ip = &parameters[1]; *ip != -1; ++ip )
    {
      strcat( name, " " );
      strcat( name, _low_objectName[*ip - 1] );
    }
  strcat( name, ")" );
  return( name );
}


char *
atomName( int *parameters )
{
  static char name[1024];

  if( parameters[0] <= _low_numberPredicates )
    {
      name[0] = '(';
      name[1] = '\0';
      strcat( name, _low_predicateName[parameters[0] - 1] );
      for( int* ip = &parameters[1]; *ip != -1; ++ip )
        {
          strcat( name, " " );
          strcat( name, _low_objectName[*ip - 1] );
        }
      strcat( name, ")" );
    }
  else
    {
      name[0] = '\0';
      strcat( name, "(NOT-" );
      strcat( name, _low_predicateName[parameters[0] - (_low_numberPredicates + 1) - 1] );
      for( int* ip = &parameters[1]; *ip != -1; ++ip )
        {
          strcat( name, " " );
          strcat( name, _low_objectName[*ip - 1] );
        }
      strcat( name, ")" );
    }
  return( name );
}


int
atomCmp( const void *a1, const void *a2 )
{
  return( (*(int*)a1) - (*(int*)a2) );
}


void
orderAtomList( int *atomList, int size )
{
  qsort( atomList, size, sizeof( int ), &atomCmp );
}



/*********************************************************
**********************************************************
**
** Atom Hash
**
**/

unsigned
atomHashFunction( int *parameters )
{
  unsigned index = 0;
  for( int* ip = parameters; *ip != -1; ++ip )
    index += *ip;
  return( index < ATOMHASHSIZE ? index : index % ATOMHASHSIZE );
}


iatom_t *
insertIntoAtomHash( int *parameters )
{
  static int currentAtom = 0;

  if( numberAtoms == ATOMSPERPACK * MAXATOMPACKS - 1 )
    fatal( maxAtoms );

  unsigned index = atomHashFunction( parameters );
  if( currentAtom >= atomHashClaimSize )
    {
      atomHashClaimSize = (atomHashClaimSize == 0 ? 1024 : INCRATE * atomHashClaimSize);
      atomHashPool = (iatom_t*)malloc( atomHashClaimSize * sizeof( iatom_t ) );
      if( !atomHashPool )
        fatal( noMoreMemory );
      currentAtom = 0;
    }
  iatom_t* iatom = &atomHashPool[currentAtom++];
  memcpy( iatom->parameters, parameters, MAXPARAMETERS * sizeof( int ) );
  strcpy( iatom->name, atomName( parameters ) );
  iatom->idx = ++numberAtoms;
  iatom->next = atomHashTable[index];
  atomHashTable[index] = iatom;
  return( iatom );
}


iatom_t *
readAtomHash( int *parameters )
{
  for( iatom_t* iatom = atomHashTable[atomHashFunction( parameters )]; iatom != nullptr; iatom = iatom->next )
    {
      int *ip, *jp;
      for( ip = parameters, jp = iatom->parameters; (*ip != -1) && (*ip == *jp); ++ip, ++jp);
      if( (*ip == -1) && (*jp == -1) )
        return( iatom );
    }

  /* if not present, insert it right now! */
  return( insertIntoAtomHash( parameters ) );
}


iatom_t *
readAtomByNumber( int index )
{
  iatom_t *iatom = nullptr;
  size_t i;
  for( i = 0; i < ATOMHASHSIZE; ++i )
    {
      for( iatom = atomHashTable[i]; (iatom != nullptr) && (iatom->idx != index); iatom = iatom->next );
      if( iatom != nullptr )
        break;
    }
  assert( i != ATOMHASHSIZE );
  return( iatom );
}


char *
readAtomName( int index )
{
  return( atomName( readAtomByNumber( index )->parameters ) );
}


int
positiveAtom( int index )
{
  return( readAtomByNumber( index )->parameters[0] <= _low_numberPredicates );
}



/*********************************************************
**********************************************************
**
** Nodes
**
**/

void
initializeMemoryMgmt( void )
{
  pageSize = getpagesize();
  /* pageSize = sysconf( _SC_PAGESIZE ); */
}


node_t *
getNode( void )
{
  char **newNodePoolTable;
  int *newNodePoolSize;
  char *newNodePoolUsed;

  /* check if we have enough pool areas */
  if( currentNodePool + 1 >= nodePoolTableSize )
  {
    int oldSize = nodePoolTableSize;
    nodePoolTableSize = (nodePoolTableSize == 0 ? 1024 : INCRATE * nodePoolTableSize);
    newNodePoolTable = (char**)realloc( nodePoolTable, nodePoolTableSize * sizeof( char* ) );
    newNodePoolSize = (int*)realloc( nodePoolSize, nodePoolTableSize * sizeof( int ) );
    newNodePoolUsed = (char*)realloc( nodePoolUsed, nodePoolTableSize * sizeof( char ) );
    if( !newNodePoolTable || !newNodePoolSize || !newNodePoolUsed )
      fatal( noMoreMemory );

    /* prepare new pool areas */
    nodePoolTable = newNodePoolTable;
    nodePoolSize = newNodePoolSize;
    nodePoolUsed = newNodePoolUsed;
    memset( &nodePoolUsed[oldSize], 0, (nodePoolTableSize - oldSize) * sizeof( char ) );
  }

  /* check if we have enough space in pool area */
  if( (nodePool == nullptr) ||
      (nodePool == nodePoolTable[currentNodePool] + nodePoolSize[currentNodePool]) )
  {
    /* get new pool area */
    ++currentNodePool;
    if( nodePoolUsed[currentNodePool] == 0 )
    {
      nodePoolClaimSize = (nodePoolClaimSize == 0 ? 1024 : (int) (INCRATE * nodePoolClaimSize));
      nodePoolSize[currentNodePool] = nodePoolClaimSize * NODESIZE;
      fprintf( stderr, "HEAPMGMT: allocating memory for %d nodes (%d bytes)... ",
                nodePoolClaimSize, nodePoolSize[currentNodePool] );
      fflush( stderr );
      nodePoolTable[currentNodePool] = (char*)malloc( nodePoolSize[currentNodePool] );
      if( !nodePoolTable[currentNodePool] )
        fatal( noMoreMemory );
      else
      {
        fprintf( stderr, "done!\n" );
        nodePoolUsed[currentNodePool] = 1;
      }
    }
    nodePool = &nodePoolTable[currentNodePool][0];
  }
    
  /* claim node from current pool */
  node_t* result = (node_t*) nodePool;
  result->state = (atom_t*) ((char*)result + sizeof( node_t ));
  nodePool += NODESIZE;
  
  /* update memory usage & check constraint */
  nodeMemoryUsed += NODESIZE;
  if( (memoryConstraint > 0) && ((nodeMemoryUsed) / MEGABYTE >= memoryConstraint) )
    memoryExpired = 1;
  
  /* return */
  return( result );
}


void
freeLastNodes( int number )
{
  nodePool -= number * NODESIZE;
}


void
freeAllSpace( void )
{
  nodeMemoryUsed = 0;
  currentNodePool = -1;
  nodePool = nullptr;
}



/*********************************************************
**********************************************************
**
** Node Hash
**
**/

/*int
stateDiff( atom_t *state1, atom_t *state2 )
{
  int diff = 0;

  assert( globalInitialized );
  for( atom_t *lp1 = state1, *lp2 = state2; (lp1 < &state1[SIZE_PACKS]); ++lp1, ++lp2 )
  for( int i = 1; i < SIZE_ATOMS; ++i )
    if( asserted( state1, i ) != asserted( state2, i ) )
      ++diff;
  return diff;
}*/


int
stateCmp( atom_t *state1, atom_t *state2 )
{
  assert( globalInitialized );
  atom_t *lp1, *lp2;
  for( lp1 = state1, lp2 = state2; (lp1 < &state1[SIZE_PACKS]) && (lp1->pack == lp2->pack); ++lp1, ++lp2 );
  return( !(lp1 == &state1[SIZE_PACKS]) );
}


unsigned
nodeHashFunction( atom_t *state )
{
  int i;
  unsigned val, *hp;

  /* xxxx: the ideal thing to do here is to loop MAXATOMPACKS times instead of SIZE_ATOMS */
  assert( globalInitialized );
  for( i = 1, hp = nodeHashValues, val = 0; i < SIZE_ATOMS; ++i, ++hp )
    val += (asserted( state, i ) ? *hp : 0);
  return( val % NODEHASHSIZE );
}


node_t *
readNodeHash( atom_t *state )
{
  unsigned index = nodeHashFunction( state );
  for( node_t* node = nodeHashTable[index]; node != nullptr; node = node->hashNext )
    if( !stateCmp( state, node->state ) )
      return( node );
  return( nullptr );
}


void
insertIntoNodeHash( node_t *node )
{
  unsigned index = nodeHashFunction( node->state );
  node->hashNext = nodeHashTable[index];
  node->hashPrev = nullptr;
  nodeHashTable[index] = node;
  if( node->hashNext != nullptr )
    node->hashNext->hashPrev = node;
  ++nodeHashNumElem;
  ++(nodeHashDiameter[index]);
}


void
removeNodeFromHash( node_t *node )
{
  unsigned index = nodeHashFunction( node->state );
  if( nodeHashTable[index] == node )
    {
      assert( node->hashPrev == nullptr );
      nodeHashTable[index] = node->hashNext;
    }
  else
    {
      assert( node->hashPrev != nullptr );
      node->hashPrev->hashNext = node->hashNext;
    }

  if( node->hashNext != nullptr )
    node->hashNext->hashPrev = node->hashPrev;
}


void
cleanNodeHash( void )
{
  freeAllSpace();
  memset( nodeHashDiameter, 0, NODEHASHSIZE * sizeof( int ) );
  memset( nodeHashTable, 0, NODEHASHSIZE * sizeof( node_t* ) );
}


void
nodeHashStatistics( void )
{
  int n = 0;
  int sum = 0;
  int diameter = 0;
  for( int index = 0; index < NODEHASHSIZE; ++index )
    {
      diameter = max( diameter, nodeHashDiameter[index] );
      sum += nodeHashDiameter[index];
      n += (nodeHashDiameter[index] > 0);
    }
  
  // TODO: change stdout back to stderr
  fprintf( stdout, "NODEHASH: nodes in hash table = %d\n", nodeHashNumElem );
  fprintf( stdout, "NODEHASH: diameter of hash table = %d\n", diameter );
  fprintf( stdout, "NODEHASH: average diameter of hash table = %f\n", (float)sum/(float)n );
}



/*********************************************************
**********************************************************
**
** Node Expansion: Common
**
**/

int
nodeBucket( node_t *node )
{
  int result = 0;

  switch( searchHeuristic )
    {
    case H1PLUS: /* f(n) = g(n) + W*h1_plus(n) */
      result = node->cost + (int)(heuristicWeight * node->h1_plus);
      break;
    case H1MAX: /* f(n) = g(n) + W*h1_max(n) */
      result = node->cost + (int)(heuristicWeight * node->h1_max);
      break;
    case H2PLUS: /* f(n) = g(n) + W*h2_plus(n) */
      result = node->cost + (int)(heuristicWeight * node->h2_plus);
      break;
    case H2MAX: /* f(n) = g(n) + W*h2_max(n) */
      result = node->cost + (int)(heuristicWeight * node->h2_max);
      break;
    case H1EPLUS: /* f(n) = g(n) + W*h1e_plus(n) */
      result = node->cost + (int)(heuristicWeight * node->h1e_plus);
      break;
    case H1EMAX: /* f(n) = g(n) + W*h1e_max(n) */
      result = node->cost + (int)(heuristicWeight * node->h1e_max);
      break;
    }
  return( result );
}


void
setInitialOPEN( node_t *node )
{
  int bucket = nodeBucket( node );
  if( bucket >= bucketTableSize )
    resizeBucketTable(bucket);

  minBucket = maxBucket = bucket;
  node->bucket = bucket;
  node->bucketNext = nullptr;
  node->bucketPrev = nullptr;
  firstNodeInBucket[bucket] = node;
  lastNodeInBucket[bucket] = node;
  headOPEN = node;
  tailOPEN = node;
  ++nodesInOPEN;
}


node_t *
getFirstOPEN( void )
{
  return( headOPEN );
}


void
removeNodeFromOPEN( node_t *node )
{
  int bucket = node->bucket;
  assert( nodesInOPEN > 0 );
  --nodesInOPEN;

  /* link update */
  if( node->bucketPrev != nullptr )
    node->bucketPrev->bucketNext = node->bucketNext;
  if( node->bucketNext != nullptr )
    node->bucketNext->bucketPrev = node->bucketPrev;

  /* bucket update */
  if( node == firstNodeInBucket[bucket] )
    {
      if( lastNodeInBucket[bucket] != node )
        {
          assert( node->bucketNext != nullptr );
          assert( lastNodeInBucket[bucket] != nullptr );
          firstNodeInBucket[bucket] = node->bucketNext;
        }
      else
        {
          firstNodeInBucket[bucket] = nullptr;
          lastNodeInBucket[bucket] = nullptr;
          needRethreading = 1;
        }
    }
  else if( node == lastNodeInBucket[bucket] )
    {
      assert( node->bucketPrev != nullptr );
      lastNodeInBucket[bucket] = node->bucketPrev;
    }

  /* OPEN update */
  if( node == headOPEN )
    {
      headOPEN = node->bucketNext;
      if( headOPEN != nullptr )
        {
          minBucket = headOPEN->bucket;
        }
      else
        {
          //minBucket = bucketTableSize;
          //maxBucket = 0;
          minBucket = INT_MIN;
          maxBucket = INT_MAX;
          assert( needRethreading == 1 );
        }
    }
  if( node == tailOPEN )
    {
      tailOPEN = node->bucketPrev;
      if( tailOPEN != nullptr )
        {
          maxBucket = tailOPEN->bucket;
        }
      else
        {
          //minBucket = bucketTableSize;
          //maxBucket = 0;
          minBucket = INT_MIN;
          maxBucket = INT_MAX;
          assert( needRethreading == 1 );
        }
    }

  /* CLOSE update */
  node->open = 0;
  node->bucketNext = CLOSE;
  if( CLOSE != nullptr )
    CLOSE->bucketPrev = node;
  CLOSE = node;
  ++nodesInCLOSE;
}


#if 0
node_t *
removeLastFromOPEN( node_t *father )
{
  int bucket;
  node_t *node;

  for( node = tailOPEN; (node != nullptr) && (node->father == father); node = node->bucketPrev );
  if( node == nullptr )
    return( nullptr );
  else
    bucket = node->bucket;

  /* link update */
  if( node->bucketPrev != nullptr )
    node->bucketPrev->bucketNext = node->bucketNext;
  if( node->bucketNext != nullptr )
    node->bucketNext->bucketPrev = node->bucketPrev;

  /* bucket update */
  if( node == firstNodeInBucket[bucket] )
    {
      if( lastNodeInBucket[bucket] != node )
        firstNodeInBucket[bucket] = node->bucketNext;
      else
        {
          firstNodeInBucket[bucket] = nullptr;
          lastNodeInBucket[bucket] = nullptr;
        }
    }
  else if( node == lastNodeInBucket[bucket] )
    {
      assert( node->bucketPrev != nullptr );
      lastNodeInBucket[bucket] = node->bucketPrev;
    }

  /* OPEN update */
  if( node == headOPEN )
    {
      headOPEN = node->bucketNext;
      if( headOPEN != nullptr )
        minBucket = headOPEN->bucket;
      else
        {
          //minBucket = bucketTableSize;
          //maxBucket = 0;
          assert( 0 );
        }
    }
  if( node == tailOPEN )
    {
      tailOPEN = node->bucketPrev;
      if( tailOPEN != nullptr )
        maxBucket = tailOPEN->bucket;
      else
        {
          //minBucket = bucketTableSize;
          //maxBucket = 0;
          assert( 0 );
        }
    }

  /* hash update */
  removeNodeFromHash( node );

  /* return */
  return( node );
}
#endif


node_t *
removeNodeFromCLOSE( void )
{
  --nodesInCLOSE;
  node_t* node = CLOSE;

  /* CLOSE update */
  CLOSE = CLOSE->bucketNext;
  if( CLOSE != nullptr )
    CLOSE->bucketPrev = nullptr;

  /* hash update */
  removeNodeFromHash( node );

  /* return */
  return( node );
}


void
resizeBucketTable( int min_size )
{
  node_t **new_table = 0;
  int new_size = bucketTableSize == 0 ? MINBUCKETTABLESIZE : bucketTableSize<<1;
  while( min_size >= new_size ) new_size = new_size<<1;

  new_table = (node_t**)malloc(new_size*sizeof(node_t*));
  if( !new_table ) fatal(noMoreMemory);
  memset(new_table,0,new_size*sizeof(node_t*));
  memcpy(new_table,firstNodeInBucket,bucketTableSize*sizeof(node_t*));
  free(firstNodeInBucket);
  firstNodeInBucket = new_table;

  new_table = (node_t**)malloc(new_size*sizeof(node_t*));
  if( !new_table ) fatal(noMoreMemory);
  memset(new_table,0,new_size*sizeof(node_t*));
  memcpy(new_table,lastNodeInBucket,bucketTableSize*sizeof(node_t*));
  free(lastNodeInBucket);
  lastNodeInBucket = new_table;

  bucketTableSize = new_size;
  fprintf( stderr, "GENERAL: new number of buckets = %d\n", bucketTableSize );
}

void
insertNodeIntoBucket( node_t *node, int bucket )
{
  node_t* n;

  if( bucket >= bucketTableSize )
    resizeBucketTable(bucket);

  /* look for proper place of insertion */
  for( n = firstNodeInBucket[bucket]; n != lastNodeInBucket[bucket]; n = n->bucketNext ) // TODO wtf?! heuristic mismatches!
    if( ((searchHeuristic == H1PLUS || searchHeuristic == H1EPLUS) && (node->h2_max <= n->h2_max)) ||
        ((searchHeuristic == H1MAX || searchHeuristic == H1EMAX) && (node->h1_plus <= n->h1_plus)) ||
        ((searchHeuristic == H2MAX) && (node->h1_plus <= n->h1_plus)) )
      break;

  /* check if rethreading is needed */
  if( firstNodeInBucket[bucket] == nullptr ) {
    needRethreading = 1;
    if( (bucket < minBucket) || (bucket > maxBucket) ) {
      minBucket = INT_MIN;
      maxBucket = INT_MAX;
    }
  }

  /* insert node before n */
  ++nodesInOPEN;
  node->bucket = bucket;
  node->bucketNext = n;
  node->bucketPrev = nullptr;
  if( n == firstNodeInBucket[bucket] )
    {
      if( n == nullptr )
        lastNodeInBucket[bucket] = node;
      else
        n->bucketPrev = node;
      firstNodeInBucket[bucket] = node;
    }
  else
    {
      assert( n != nullptr );
      node->bucketPrev = n->bucketPrev;
      n->bucketPrev->bucketNext = node;
      n->bucketPrev = node;
    }
}


void
nodeOrdering( node_t **buffer, int size )
{
  int bucket;
  node_t *invalidNodes, *lastNodeInPrevBucket;

  /* bucket sorting */
  invalidNodes = nullptr;
  for( size_t i = 0; i < size; ++i )
    if( buffer[i]->valid == 1 )
      {
        /* registry used buckets */
        bucket = nodeBucket( buffer[i] );
        if( minBucket != -1 ) minBucket = min( minBucket, bucket );
        if( maxBucket != -1 ) maxBucket = max( maxBucket, bucket );
        insertNodeIntoBucket( buffer[i], bucket );
      }
    else
      {
        buffer[i]->bucketNext = invalidNodes;
        invalidNodes = buffer[i];
      }

  /* bucket threading */
  if( needRethreading == 1 )
    {
      int lowerLimit = minBucket == INT_MIN ? 0 : minBucket;
      int upperLimit = maxBucket == INT_MAX ? bucketTableSize : 1 + maxBucket;
      minBucket = INT_MAX;
      maxBucket = INT_MIN;
      for( bucket = lowerLimit, lastNodeInPrevBucket = nullptr; bucket < upperLimit; ++bucket )
        {
          if( firstNodeInBucket[bucket] != nullptr )
            {
              if( lastNodeInPrevBucket != nullptr )
                {
                  lastNodeInPrevBucket->bucketNext = firstNodeInBucket[bucket];
                  firstNodeInBucket[bucket]->bucketPrev = lastNodeInPrevBucket;
                }
              lastNodeInPrevBucket = lastNodeInBucket[bucket];
              minBucket = bucket < minBucket ? bucket : minBucket;
              maxBucket = bucket > maxBucket ? bucket : maxBucket;
            }
        }
    }

  /* compute new openList head and tail */
  headOPEN = minBucket == INT_MAX ? 0 : firstNodeInBucket[minBucket];
  tailOPEN = maxBucket == INT_MIN ? 0 : lastNodeInBucket[maxBucket];
  assert( (nodesInOPEN == 0) || (headOPEN != nullptr) );
}


void
cleanLists( void )
{
  headOPEN = nullptr;
  tailOPEN = nullptr;
  CLOSE = nullptr;
  memset( firstNodeInBucket, 0, bucketTableSize * sizeof( node_t* ) );
  memset( lastNodeInBucket, 0, bucketTableSize * sizeof( node_t* ) );
}


void
printLists( void )
{
  fprintf( stderr, "OPEN LIST =" );
  for( node_t* node = headOPEN; node != nullptr; node = node->bucketNext )
    fprintf( stderr, " %p", node );
  fprintf( stderr, "\n" );
  fprintf( stderr, "CLOSE LIST =" );
  for( node_t* node = CLOSE; node != nullptr; node = node->bucketNext )
    fprintf( stderr, " %p", node );
  fprintf( stderr, "\n" );
}



/*********************************************************
**********************************************************
**
** Node Expansion: particulars
**
**/

void
randomWalk( atom_t* state, int steps )
{
  
  atom_t prevState[MAXATOMPACKS];
  while (steps--)
  {
    vector<int> ops;
    int* p;
    for( int* alpha = validOperators; *alpha != -1; ++alpha )
    {
      /* preconditions */
      for( p = operatorTable[*alpha].prec; (*p != 0) && asserted( state, *p ); ++p );
      if( *p == 0 )
        ops.push_back(*alpha);
    }
    if (ops.empty())
      break;
    std::uniform_int_distribution<int> dist(0, ops.size()-1);
    int op = ops[dist(rng)];
    memcpy( prevState, state, SIZE_PACKS * sizeof( atom_t ) );
    
    /* operators effects */
    for( int* a = operatorTable[op].add; *a != 0; ++a )
      set( state, *a );
    for( int* d = operatorTable[op].del; *d != 0; ++d )
      clear( state, *d );
    /* suboperators effects */
    for( suboperator_t* sub = operatorTable[op].suboperators; sub != nullptr; sub = sub->next )
    {
      for( p = sub->prec; (*p != 0) && asserted( prevState, *p ); ++p );
      if( *p == 0 )
      {
        for( int* a = sub->add; *a != 0; ++a )
          set( state, *a );
        for( int* d = sub->del; *d != 0; ++d )
          clear( state, *d );
      }
    }
  }
}

int
forwardNodeExpansion( node_t *node, node_t ***result )
{
  static int initialized = 0;
  static node_t **buffer;

  /* initialization */
  if( !initialized )
    {
      initialized = 1;
      buffer = (node_t**)malloc( numberOperators * sizeof( node_t* ) );
      if( !buffer )
        fatal( noMoreMemory );
    }
  // TODO remove debug code
  /*fprintf( stdout, "EXPAND node with h=%d:\t", node->h1e_max );
  for( size_t i = 1; i < SIZE_ATOMS; ++i )
    if( asserted( node->state, i ) )
    {
      fprintf( stdout, "%s ", readAtomName(i) );
    }
  fprintf( stdout, "\n" );*/

  /* update problem data */
  ++expandedNodes;

  /* get some initial space */
  int child = 0;
  buffer[child] = getNode();

  /* node expansion */
  for( int* alpha = validOperators; *alpha != -1; ++alpha )
    {
      /* preconditions */
      int* p;
      for( p = operatorTable[*alpha].prec; (*p != 0) && asserted( node->state, *p ); ++p );
      if( *p == 0 )
        {
          /* state progression */
          memcpy( buffer[child]->state, node->state, SIZE_PACKS * sizeof( atom_t ) );

          /* operators effects */
          for( int* a = operatorTable[*alpha].add; *a != 0; ++a )
            set( buffer[child]->state, *a );
          for( int* d = operatorTable[*alpha].del; *d != 0; ++d )
            clear( buffer[child]->state, *d );

          /* suboperators effects */
          for( suboperator_t* sub = operatorTable[*alpha].suboperators; sub != nullptr; sub = sub->next )
            {
              for( p = sub->prec; (*p != 0) && asserted( node->state, *p ); ++p );
              if( *p == 0 )
                {
                  for( int* a = sub->add; *a != 0; ++a )
                    set( buffer[child]->state, *a );
                  for( int* d = sub->del; *d != 0; ++d )
                    clear( buffer[child]->state, *d );
                }
            }

          /* get cached node */
          node_t* tmp = readNodeHash( buffer[child]->state );
          if( (tmp == nullptr) ||
              (node->cost + 1 < tmp->cost) )
            {
              ++generatedNodes;

              /* check for tmp in OPEN */
              if( tmp != nullptr )
                {
                  if( verbose >= 6 )
                    {
                      if( tmp->open == 0 )
                        fprintf( stderr, "NODE-EXPANSION: reopening node %p\n", tmp );
                      else
                        fprintf( stderr, "NODE-EXPANSION: updating OPEN node %p\n", tmp );
                    }

                  /* child node heuristic information */
                  buffer[child]->valid = 1;
                  buffer[child]->h1_plus = tmp->h1_plus;
                  buffer[child]->h1_max = tmp->h1_max;
                  buffer[child]->h2_plus = tmp->h2_plus;
                  buffer[child]->h2_max = tmp->h2_max;
                  buffer[child]->h1e_plus = tmp->h1e_plus;
                  buffer[child]->h1e_max = tmp->h1e_max;

                  /* remove old node from hash and open list */
                  removeNodeFromHash( tmp );
                  if( tmp->open == 1 )
                    {
                      assert( nodesInOPEN > 0 );
                      removeNodeFromOPEN( tmp );
                    }
                }
              else
                {
                  heuristics( buffer[child] );
                }

              /* set node data */
              buffer[child]->operatorId = *alpha;
              buffer[child]->father = node;
              buffer[child]->cost = node->cost + 1;
              buffer[child]->open = 1;

              /* node caching and node space allocation */
              if( buffer[child]->valid == 1 )
                {
                  insertIntoNodeHash( buffer[child] );
                  buffer[++child] = getNode();
                }
            }
        }
    }

  /* free resources and return */
  freeLastNodes( 1 );
  *result = buffer;
  return( child );
}


int
backwardNodeExpansion( node_t *node, node_t ***result )
{
  
#if defined(USE_MUTEX)
  mutex_t *mutex;
  mutexSet_t *set;
#endif

  static int initialized = 0;
  static char *operatorDisplay;
  static node_t **buffer;

  /* initialization */
  if( !initialized )
    {
      initialized = 1;
      buffer = (node_t**)malloc( numberOperators * sizeof( node_t* ) );
      operatorDisplay = (char*)malloc( numberOperators * sizeof( char ) );
      if( !buffer || !operatorDisplay )
        fatal( noMoreMemory );
    }

  /* update problem data */
  ++expandedNodes;

  /* get applicable operators using admissibility information */
  for( size_t i = 0; i < numberOperators; ++i )
    operatorDisplay[i] = 1;

  /* check admissibility */
  for( size_t atom = 1; atom < SIZE_ATOMS; ++atom )
    if( asserted( node->state, atom ) )
      for( int* p = notAdmissible[atom]; (p != nullptr) && (*p != 0); operatorDisplay[*p++] = 0 );

  /* get some initial space */
  int child = 0;
  buffer[child] = getNode();

  /* node expansion */
  for( int* alpha = validOperators; *alpha != -1; ++alpha )
    if( operatorDisplay[*alpha] == 1 )
      {
        /* preconditions: S must has some add but no del */
        int *a, *d;
        for( a = operatorTable[*alpha].add; (*a != 0) && !asserted(node->state,*a); ++a );
        for( d = operatorTable[*alpha].del; (*d != 0) && !asserted(node->state,*d); ++d );
        if( (*a != 0) && (*d == 0) )
          {
            /* state regression */
#if defined(USE_MUTEX)
            memcpy( staticState, node->state, SIZE_PACKS * sizeof( atom_t ) );
#endif
            memcpy( buffer[child]->state, node->state, SIZE_PACKS * sizeof( atom_t ) );

            for( a = operatorTable[*alpha].add; *a != 0; ++a )
              {
#if defined(USE_MUTEX)
                set( staticState, *a );
#endif
                clear( buffer[child]->state, *a );
              }
            for( int* p = operatorTable[*alpha].prec; *p != 0; ++p )
              {
#if defined(USE_MUTEX)
                set( staticState, *p );
#endif
                set( buffer[child]->state, *p );
              }
#if defined(USE_MUTEX)
            for( d = operatorTable[*alpha].del; *d != 0; ++d )
              clear( staticState, *d );
#endif

            /* check if valid-bit before mutex check (less expensive) */
            heuristics( buffer[child] );
            if( buffer[child]->valid == 0 )
              continue;

#if defined(USE_MUTEX)
            /* check mutexes in the regressed and projected states */
            for( set = mutexSetList; set != nullptr; set = set->next )
              if( asserted( staticState, set->x ) || asserted( buffer[child]->state, set->x ) )
                {
                  for( mutex = set->set; mutex != nullptr; mutex = mutex->next )
                    if( (asserted( staticState, mutex->x ) && asserted( staticState, mutex->y )) ||
                        (asserted( buffer[child]->state, mutex->x ) && asserted( buffer[child]->state, mutex->y )) )
                      break;
                  if( mutex != nullptr )
                    break;
                }
            if( set != nullptr )
              continue;
#endif

            /* get cached node */
            node_t* tmp = readNodeHash( buffer[child]->state );
            if( (tmp == nullptr) ||
                (node->cost + 1 < tmp->cost) )
              {
                /* statistics */
                ++generatedNodes;

                /* check for tmp in OPEN */
                if( tmp != nullptr )
                  {
                    if( verbose >= 6 )
                      {
                        if( tmp->open == 0 )
                          fprintf( stderr, "NODE-EXPANSION: reopening node %p\n", tmp );
                        else
                          fprintf( stderr, "NODE-EXPANSION: updating OPEN node %p\n", tmp );
                      }

                    /* remove old node from hash and open list */
                    removeNodeFromHash( tmp );
                    if( tmp->open == 1 )
                      {
                        assert( nodesInOPEN > 0 );
                        removeNodeFromOPEN( tmp );
                      }
                  }

                /* set node data */
                buffer[child]->operatorId = *alpha;
                buffer[child]->father = node;
                buffer[child]->cost = node->cost + 1;
                buffer[child]->open = 1;

                /* node caching and node space allocation */
                if( buffer[child]->valid == 1 )
                  {
                    insertIntoNodeHash( buffer[child] );
                    buffer[++child] = getNode();
                  }
              }
          }
      }

  /* free resources and return */
  freeLastNodes( 1 );
  *result = buffer;
  return( child );
}



/*********************************************************
**********************************************************
**
** Static Atoms Compilation
**
**/

void
staticAtomCompilation( void )
{
  /* register entry */
  registerEntry( "staticAtomCompilation( void )" );
  
  int res;
  int* p = staticAtomsList;
  numberStaticAtoms = 0;
  memset( staticAtom, 0, MAXATOMPACKS * sizeof( atom_t ) );
  for( size_t i = 1; i < SIZE_ATOMS; ++i )
    {
      res = 1;
      for( size_t j = 0; (j < numberOperators) && (res == 1); ++j )
        if( operatorTable[j].valid == 1 )
          {
            int* a;
            if( asserted( staticInitialState, i ) )
              {
                for( a = operatorTable[j].del; (*a != 0) && (*a != i); ++a );
                res = res && (*a == 0);
                for( suboperator_t* sub = operatorTable[j].suboperators; (sub != nullptr) && (res == 1); sub = sub->next )
                  {
                    for( a = sub->del; (*a != 0) && (*a != i); ++a );
                    res = res && (*a == 0);
                  }
              }
            else
              {
                for( a = operatorTable[j].add; (*a != 0) && (*a != i); ++a );
                res = res && (*a == 0);
                for( suboperator_t* sub = operatorTable[j].suboperators; (sub != nullptr) && (res == 1); sub = sub->next )
                  {
                    for( a = sub->add; (*a != 0) && (*a != i); ++a );
                    res = res && (*a == 0);
                  }
              }
          }

      if( res == 1 )
        {
          *p++ = i;
          set( staticAtom, i );
          ++numberStaticAtoms;
          if( verbose >= 5 )
            fprintf( stderr, "static %s\n", readAtomName( i ) );
        }
    }
  *p = 0;

  /* register exit */
  registerExit();
}



/*********************************************************
**********************************************************
**
** Operator Compilation
**
**/

void
operatorCompilation( void )
{
  /* register entry */
  registerEntry( "operatorCompilation()" );

  /* initialization */
  memset( relevantAtom, 0, MAXATOMPACKS * sizeof( atom_t ) );
  memset( parents, 0, ATOMSPERPACK * MAXATOMPACKS * sizeof( int* ) );
  memset( parentsSize, 0, ATOMSPERPACK * MAXATOMPACKS * sizeof( int ) );
  memcpy( staticState, staticInitialState, MAXATOMPACKS * sizeof( atom_t ) );

  /* reachability analysis and goal cone */
  reachabilityAnalysis( staticInitialState );
  identifyGoalParents( _low_goalAtoms );

  /* complete initialState with negated atoms */
  if( _low_requirements & REQ_ADL )
    {
      if( verbose >= 5 )
        fprintf( stderr, "completing initial state with: " );
      int* a;
      for( a = _low_initialAtoms; *a != 0; ++a );
      for( size_t i = 1; i < SIZE_ATOMS; ++i )
        if( positiveAtom( i ) && !asserted( staticInitialState, i ) && (_low_negatedAtom[i] != 0 ) )
          {
            if( verbose >= 5 )
              fprintf( stderr, "%s ", readAtomName( _low_negatedAtom[i] ) );
            set( staticInitialState, _low_negatedAtom[i] );
            set( reachableAtom, _low_negatedAtom[i] );
            *a++ = _low_negatedAtom[i];
          }
      *a = 0;
      if( verbose >= 5 )
        fprintf( stderr, "\n" );
    }

  /* generate ground instances of actions */
  numberOperators = 0;
  _low_groundingOperators = 1;
  instantiateOperators( &insertOperator, &testOperatorPrecondition );

  /* compute static atoms & move them to the tail of state */
  staticAtomCompilation();
  printf( "OPERATOR: number of atoms = %d\n", numberAtoms );
  printf( "OPERATOR: number of static atoms = %d\n", numberStaticAtoms );
  if( staticCompilation == 1 ) {
    int first_static, last_non_static;
    static int permutation[ATOMSPERPACK*MAXATOMPACKS];
    for( size_t i = 0; i < ATOMSPERPACK*MAXATOMPACKS; ++i )
      permutation[i] = i;

    /* permute atoms so that static appear last */
    /* position pointers */
    for( first_static = 1; (first_static <= numberAtoms) && !asserted(staticAtom,first_static); ++first_static );
    for( last_non_static = numberAtoms; (last_non_static >= 0) && asserted(staticAtom,last_non_static); --last_non_static );
    assert(first_static != last_non_static);

    while( first_static < last_non_static ) {
      /* swap atoms  */
      permutation[first_static] = last_non_static;
      permutation[last_non_static] = first_static;
      --last_non_static;
      ++first_static;

      /* re-position pointers */
      while( (first_static <= numberAtoms) && !asserted(staticAtom,first_static) )
        ++first_static;
      while( (last_non_static >= 0) && asserted(staticAtom,last_non_static) )
        --last_non_static;
      assert(first_static != last_non_static);
    }


    /* update operators wrt to new partition */
    for( size_t i = 0; i < numberOperators; ++i ) {
      if( operatorTable[i].valid == 1 ) {
        /* precondition list */
        int *p, *a;
        for( p = operatorTable[i].prec, a = p; *p != 0; ++p ) {
          if( asserted(staticAtom,*p) )
            --operatorTable[i].precSize;
          else
            *a++ = permutation[*p];
        }
        *a = 0;

        /* add list */
        for( p = operatorTable[i].add, a = p; *p != 0; ++p ) {
          if( asserted(staticAtom,*p) ) {
            assert(asserted(staticInitialState,*p));
            --operatorTable[i].addSize;
          }
          else
            *a++ = permutation[*p];
        }
        *a = 0;

        /* delete list */
        for( p = operatorTable[i].del, a = p; *p != 0; ++p ) {
          if( asserted(staticAtom,*p) ) {
            assert(!asserted(staticInitialState,*p));
            --operatorTable[i].delSize;
          } else
            *a++ = permutation[*p];
        }
        *a = 0;

        /* suboperators */
        suboperator_t* subPrev = nullptr;
        for( suboperator_t *subNext, *sub = operatorTable[i].suboperators; sub != nullptr; sub = subNext ) {
          subNext = sub->next;

          /* If prec has a false static atom, remove the whole suboperator */
          for( p = sub->prec, a = p; *p != 0; ++p ) {
            if( asserted(staticAtom,*p) ) {
              if( !asserted(staticInitialState,*p) ) break;
              --sub->precSize;
            } else
              *a++ = permutation[*p];
          }
          *a = 0;

          if( *p != 0 ) {
            /* free resources and re-link */
            free(sub->prec);
            free(sub->add);
            free(sub->del);
            free(sub);
            if( subPrev == nullptr )
              operatorTable[i].suboperators = subNext;
            else
              subPrev->next = subNext;
          } else {
            subPrev = sub;

            /* add list */
            for( p = sub->add, a = p; *p != 0; ++p ) {
              if( asserted(staticAtom,*p) ) {
                assert(asserted(staticInitialState,*p));
                --sub->addSize;
              } else
                *a++ = permutation[*p];
            }
            *a = 0;

            /* delete list */
            for( p = sub->del; *p != 0; ++p ) {
              if( asserted(staticAtom,*p) ) {
                assert(!asserted(staticInitialState,*p));
                --sub->addSize;
              } else
                *a++ = permutation[*p];
            }
            *a = 0;
          }
        }
      }
    }

    /* update initial state */
    memset(staticInitialState,0,MAXATOMPACKS*sizeof(atom_t));
    for( int* p = _low_initialAtoms; *p != 0; ++p )
      set(staticInitialState,permutation[*p]);

    /* update goal state */
    memset(staticGoalState,0,MAXATOMPACKS*sizeof(atom_t));
    for( int* p = _low_goalAtoms; *p != 0; ++p ) {
      if( !asserted(staticAtom,*p) ) {
        set(staticGoalState,permutation[*p]);
      }
    }

    /* update goal atoms */
    {
      int *p, *a;
      for( p = _low_goalAtoms, a = p; *p != 0; ++p ) {
        if( !asserted(staticAtom,*p) ) {
          *a++ = permutation[*p];
        }
      }
      *a = 0;
    }
    

    /* update relevant, reachable and static atoms */
    memcpy(dummyAtom,relevantAtom,MAXATOMPACKS*sizeof(atom_t));
    memset(relevantAtom,0,MAXATOMPACKS*sizeof(atom_t));
    for( size_t i = 1; i < SIZE_ATOMS; ++i ) {
      if( asserted(dummyAtom,i) )
        set(relevantAtom,permutation[i]);
    }

    memcpy(dummyAtom,reachableAtom,MAXATOMPACKS*sizeof(atom_t));
    memset(reachableAtom,0,MAXATOMPACKS*sizeof(atom_t));
    for( size_t i = 1; i < SIZE_ATOMS; ++i ) {
      if( asserted(dummyAtom,i) )
        set(reachableAtom,permutation[i]);
    }

    memcpy(dummyAtom,staticAtom,MAXATOMPACKS*sizeof(atom_t));
    memset(staticAtom,0,MAXATOMPACKS*sizeof(atom_t));
    for( size_t i = 1; i < SIZE_ATOMS; ++i ) {
      if( asserted(dummyAtom,i) )
        set(staticAtom,permutation[i]);
    }

    /* update atom hash */
    for( size_t i = 0; i < ATOMHASHSIZE; ++i ) {
      for( iatom_t* entry = atomHashTable[i]; entry != nullptr; entry = entry->next )
        entry->idx = permutation[entry->idx];
    }

    /* update low level */
    for( int* p = _low_initialAtoms; *p != 0; ++p )
      *p = permutation[*p];
    for( int* p = _low_copyGoalAtoms; *p != 0; ++p )
      *p = permutation[*p];

    /* shrink state. After this everything should be ok */
    numberAtoms -= numberStaticAtoms;
  }

  /* generate H operators (only for ADL) */
  if( _low_requirements & REQ_ADL )
    generateHOperators();

  /* space allocation */
  invPrecTableSize = (int*)calloc( SIZE_ATOMS, sizeof( int ) );
  invPrecTable = (int**)calloc( SIZE_ATOMS, sizeof( int* ) );
  invAddTableSize = (int*)calloc( SIZE_ATOMS, sizeof( int ) );
  invAddTable = (int**)calloc( SIZE_ATOMS, sizeof( int* ) );
  invDelTableSize = (int*)calloc( SIZE_ATOMS, sizeof( int ) );
  invDelTable = (int**)calloc( SIZE_ATOMS, sizeof( int* ) );
  if( !invPrecTableSize || !invAddTableSize || !invDelTableSize ||
      !invPrecTable || !invAddTable || !invDelTable )
    fatal( noMoreMemory );
  if( _low_requirements & REQ_ADL )
    {
      HInvPrecTableSize = (int*)calloc( SIZE_ATOMS, sizeof( int ) );
      HInvPrecTable = (int**)calloc( SIZE_ATOMS, sizeof( int* ) );
      HInvAddTableSize = (int*)calloc( SIZE_ATOMS, sizeof( int ) );
      HInvAddTable = (int**)calloc( SIZE_ATOMS, sizeof( int* ) );
      if( !HInvPrecTableSize || !HInvPrecTable || !HInvAddTableSize || !HInvAddTable )
        fatal( noMoreMemory );
    }

  /* inverse table fill */
  for( size_t i = 0; i < numberOperators; ++i )
    if( operatorTable[i].valid == 1 )
      {
        /* inverse table for preconditions */
        for( int* p = operatorTable[i].prec; *p != 0; ++p )
          {
            int j, k = invPrecTableSize[*p];
            int* t = invPrecTable[*p];
            for( j = 0; (j < k) && (*(t+j) != 0) && (*(t+j) != i + 1); ++j );
            if( (j == k) || (*(t+j) == 0) )
              {
                if( j + 1 >= k )
                  {
                    invPrecTableSize[*p] =
                      (invPrecTableSize[*p] == 0 ? 16 : (int)(INCRATE * invPrecTableSize[*p]));
                    invPrecTable[*p] =
                      (int*)realloc( invPrecTable[*p], invPrecTableSize[*p] * sizeof( int ) );
                    if( !invPrecTable[*p] )
                      fatal( noMoreMemory );
                    t = invPrecTable[*p];
                  }
                *(t+j) = i + 1;
                *(t+j+1) = 0;
              }
          }

        /* inverse table for add */
        for( int* a = operatorTable[i].add; *a != 0; ++a )
          {
            int j, k = invAddTableSize[*a];
            int* t = invAddTable[*a];
            for( j = 0; (j < k) && (*(t+j) != 0) && (*(t+j) != i + 1); ++j );
            if( (j == k) || (*(t+j) == 0) )
              {
                if( j + 1 >= k )
                  {
                    invAddTableSize[*a] =
                      (invAddTableSize[*a] == 0 ? 16 : (int)(INCRATE * invAddTableSize[*a]));
                    invAddTable[*a] =
                      (int*)realloc( invAddTable[*a], invAddTableSize[*a] * sizeof( int ) );
                    if( !invAddTable[*a] )
                      fatal( noMoreMemory );
                    t = invAddTable[*a];
                  }
                *(t+j) = i + 1;
                *(t+j+1) = 0;
              }
          }

        /* inverse table for del */
        for( int* d = operatorTable[i].del; *d != 0; ++d )
          {
            int j, k = invDelTableSize[*d];
            int* t = invDelTable[*d];
            for( j = 0; (j < k) && (*(t+j) != 0) && (*(t+j) != i + 1); ++j );
            if( (j == k) || (*(t+j) == 0) )
              {
                if( j + 1 >= k )
                  {
                    invDelTableSize[*d] =
                      (invDelTableSize[*d] == 0 ? 16 : (int)(INCRATE * invDelTableSize[*d]));
                    invDelTable[*d] =
                      (int*)realloc( invDelTable[*d], invDelTableSize[*d] * sizeof( int ) );
                    if( !invDelTable[*d] )
                      fatal( noMoreMemory );
                    t = invDelTable[*d];
                  }
                *(t+j) = i + 1;
                *(t+j+1) = 0;
              }
          }
      }

  /* H inverse table fill */
  for( size_t i = 0; i < numberHOperators; ++i )
    if( HOperatorTable[i].valid == 1 )
      {
        /* inverse table for preconditions */
        for( int* p = HOperatorTable[i].prec; *p != 0; ++p )
          {
            int j, k = HInvPrecTableSize[*p];
            int* t = HInvPrecTable[*p];
            for( j = 0; (j < k) && (*(t+j) != 0) && (*(t+j) != i + 1); ++j );
            if( (j == k) || (*(t+j) == 0) )
              {
                if( j + 1 >= k )
                  {
                    HInvPrecTableSize[*p] =
                      (HInvPrecTableSize[*p] == 0 ? 16 : (int)(INCRATE * HInvPrecTableSize[*p]));
                    HInvPrecTable[*p] =
                      (int*)realloc( HInvPrecTable[*p], HInvPrecTableSize[*p] * sizeof( int ) );
                    if( !HInvPrecTable[*p] )
                      fatal( noMoreMemory );
                    t = HInvPrecTable[*p];
                  }
                *(t+j) = i + 1;
                *(t+j+1) = 0;
              }
          }

        /* inverse table for add */
        for( int* a = HOperatorTable[i].add; *a != 0; ++a )
          {
            int j, k = HInvAddTableSize[*a];
            int* t = HInvAddTable[*a];
            for( j = 0; (j < k) && (*(t+j) != 0) && (*(t+j) != i + 1); ++j );
            if( (j == k) || (*(t+j) == 0) )
              {
                if( j + 1 >= k )
                  {
                    HInvAddTableSize[*a] =
                      (HInvAddTableSize[*a] == 0 ? 16 : (int)(INCRATE * HInvAddTableSize[*a]));
                    HInvAddTable[*a] =
                      (int*)realloc( HInvAddTable[*a], HInvAddTableSize[*a] * sizeof( int ) );
                    if( !HInvAddTable[*a] )
                      fatal( noMoreMemory );
                    t = HInvAddTable[*a];
                  }
                *(t+j) = i + 1;
                *(t+j+1) = 0;
              }
          }
      }

  /* register exit */
  registerExit();
}


/*
** Compute the admissibility information; i.e., for each atom x, the operator
** alpha is not admissible wrt x (alpha \in notAdmissible[x]) if and only if
** exists a precondition p of alpha such that MUTEX(p,x) and neither x or p
** belongs to add of alpha (i.e., alpha does not remove x or p).
*/
void
admissibleOperatorCompilation( void )
{
  /* register entry */
  registerEntry( "admissibleOperatorCompilation()" );

  /* space allocation */
  notAdmissible = (int**)calloc( SIZE_ATOMS, sizeof( int* ) );
  notAdmissibleSize = (int*)calloc( SIZE_ATOMS, sizeof( int ) );
  if( !notAdmissible || !notAdmissibleSize )
    fatal( noMoreMemory );

  /* compilation */
  for( int x = 1; x < SIZE_ATOMS; ++x )
    {
      int last = 0;
      for( size_t op = 0; op < numberOperators; ++op )
        if( operatorTable[op].valid == 1 )
          {
            int exists = 0;
            for( int* p = operatorTable[op].prec; (*p != 0) && (exists == 0); ++p )
#if !defined(USE_MUTEX)
              if( PAIR( x, *p ).max == INT_MAX )
#else
              if( MUTEX( x, *p ) )
#endif
                {
                  int* a;
                  for( a = operatorTable[op].add; (*a != 0) && (*a != x) && (*a != *p); ++a );
                  exists = (*a == 0);
                }

            if( exists == 1 )
              {
                if( last + 1 >= notAdmissibleSize[x] )
                  {
                    notAdmissibleSize[x] = (notAdmissibleSize[x] == 0 ? 16 : (int)(INCRATE * notAdmissibleSize[x]));
                    notAdmissible[x] = (int*)realloc( notAdmissible[x], notAdmissibleSize[x] * sizeof( int ) );
                    if( !notAdmissible[x] )
                      fatal( noMoreMemory );
                  }
                notAdmissible[x][last++] = op;
                notAdmissible[x][last] = 0;
              }
          }
    }

  /* register exit */
  registerExit();
}


void
addParents( int atom, int *parentList )
{
  for( int* ip = parentList; *ip != 0; ++ip )
    {
      int i, *jp;
      for( jp = parents[atom], i = 0; (jp != 0) && (*jp != 0); ++jp, ++i )
        if( *ip == *jp )
          break;

      if( (jp == 0) || (*jp == 0) )
        {
          if( i > parentsSize[atom] - 2 )
            {
              parentsSize[atom] = (parentsSize[atom] == 0 ? 4 : INCRATE * parentsSize[atom]);
              if( !(parents[atom] = (int*)realloc( parents[atom], parentsSize[atom] * sizeof( int ) )) )
                fatal( noMoreMemory );
            }
          parents[atom][i] = *ip;
          parents[atom][i+1] = 0;
        }
    }
}


void
identifyGoalParents( int *atoms )
{
  if( atoms != nullptr )
    for( int* ip = atoms; *ip != 0; ++ip )
      if( !asserted( relevantAtom, *ip ) )
        {
          ++numberRelevantAtoms;
          set( relevantAtom, *ip );
          identifyGoalParents( parents[*ip] );
        }
}



/*********************************************************
**********************************************************
**
** H Operators
**
**/

void
generateHOperators( void )
{
  /* space allocation */
  HSubTableSize = (int*)calloc( numberOperators, sizeof( int ) );
  HSubTable = (int**)calloc( numberOperators, sizeof( int* ) );
  if( !HSubTableSize || !HSubTable )
    fatal( noMoreMemory );

  /* go! */
  for( size_t op = 0; op < numberOperators; ++op )
    {
      /* resize HOperatorTable */
      if( numberHOperators == HOperatorTableSize )
        {
          HOperatorTableSize = (HOperatorTableSize == 0 ? 16 : INCRATE * HOperatorTableSize);
          HOperatorTable =
            (operator_t*)realloc( HOperatorTable, HOperatorTableSize * sizeof( operator_t ) );
          if( !HOperatorTable )
            fatal( noMoreMemory );
        }

      /* this is a copy of father */
      HOperatorTable[numberHOperators].prec = operatorTable[op].prec;
      HOperatorTable[numberHOperators].add = operatorTable[op].add;
      HOperatorTable[numberHOperators].del = operatorTable[op].del;
      HOperatorTable[numberHOperators].father = op;
      HOperatorTable[numberHOperators].valid = 1;

      /* fill operatorsWithNoPrec table */
      if( operatorTable[op].precSize == 0 )
        {
          ++HOperatorsWithNoPrecSize;
          HOperatorsWithNoPrec =
            (int*)realloc( HOperatorsWithNoPrec, HOperatorsWithNoPrecSize * sizeof( int ) );
          HOperatorsWithNoPrec[HOperatorsWithNoPrecSize-1] = numberHOperators;
        }

      /* next H operator */
      ++numberHOperators;

      /* now, the suboperators */
      for( suboperator_t* sub = operatorTable[op].suboperators; sub != nullptr; sub = sub->next )
        {
          /* resize HOperatorTable */
          if( numberHOperators == HOperatorTableSize )
            {
              HOperatorTableSize = (HOperatorTableSize == 0 ? 16 : INCRATE * HOperatorTableSize);
              HOperatorTable =
                (operator_t*)realloc( HOperatorTable, HOperatorTableSize * sizeof( operator_t ) );
              if( !HOperatorTable )
                fatal( noMoreMemory );
            }

          /* simple fields */
          HOperatorTable[numberHOperators].father = op;
          HOperatorTable[numberHOperators].valid = 1;

          /* space allocation for precondition, add, del lists */
          int psize = operatorTable[op].precSize + sub->precSize;
          int asize = operatorTable[op].addSize + sub->addSize;
          int dsize = operatorTable[op].delSize + sub->delSize;
          HOperatorTable[numberHOperators].prec = (int*)calloc( psize + 1, sizeof( int ) );
          HOperatorTable[numberHOperators].add = (int*)calloc( asize + 1, sizeof( int ) );
          HOperatorTable[numberHOperators].del = (int*)calloc( dsize + 1, sizeof( int ) );
          if( !HOperatorTable[numberHOperators].prec || !HOperatorTable[numberHOperators].add ||
              !HOperatorTable[numberHOperators].del )
            fatal( noMoreMemory );

          /* fill it */
          memcpy( HOperatorTable[numberHOperators].prec, operatorTable[op].prec,
                  operatorTable[op].precSize * sizeof( int ) );
          memcpy( &HOperatorTable[numberHOperators].prec[operatorTable[op].precSize], sub->prec,
                  (sub->precSize + 1) * sizeof( int ) );
          memcpy( HOperatorTable[numberHOperators].add, operatorTable[op].add,
                  operatorTable[op].addSize * sizeof( int ) );
          memcpy( &HOperatorTable[numberHOperators].add[operatorTable[op].addSize], sub->add,
                  (sub->addSize + 1) * sizeof( int ) );
          memcpy( HOperatorTable[numberHOperators].del, operatorTable[op].del,
                  operatorTable[op].delSize * sizeof( int ) );
          memcpy( &HOperatorTable[numberHOperators].del[operatorTable[op].delSize], sub->del,
                  (sub->delSize + 1) * sizeof( int ) );
          HOperatorTable[numberHOperators].valid = 1;

          /* order Prec, Add, and Del lists */
          orderAtomList( HOperatorTable[numberHOperators].prec, psize );
          orderAtomList( HOperatorTable[numberHOperators].add, asize );
          orderAtomList( HOperatorTable[numberHOperators].del, dsize );

          /* fill operatorsWithNoPrec table */
          if( psize == 0 )
            {
              ++HOperatorsWithNoPrecSize;
              HOperatorsWithNoPrec =
                (int*)realloc( HOperatorsWithNoPrec, HOperatorsWithNoPrecSize * sizeof( int ) );
              HOperatorsWithNoPrec[HOperatorsWithNoPrecSize-1] = numberHOperators;
            }

          /* fill HSub table */
          int j, k = HSubTableSize[op];
          int *s = HSubTable[op];
          for( j = 0; (j < k) && (*(s+j) != 0) && (*(s+j) != numberHOperators + 1); ++j );
          if( (j == k) || (*(s+j) == 0) )
            {
              if( j + 1 >= k )
                {
                  HSubTableSize[op] = (HSubTableSize[op] == 0 ? 16 : (int)(INCRATE * HSubTableSize[op]));
                  HSubTable[op] = (int*)realloc( HSubTable[op], HSubTableSize[op] * sizeof( int ) );
                  if( !HSubTable[op] )
                    fatal( noMoreMemory );
                  s = HSubTable[op];
                }
              *(s+j) = numberHOperators + 1;
              *(s+j+1) = 0;
            }

          /* next H operator */
          ++numberHOperators;
        }
    }
}



/*********************************************************
**********************************************************
**
** Mutex Compilation
**
**/

void
mutexCompilation( void )
{
  /* register entry */
  registerEntry( "mutexCompilation()" );

  /* space allocation */
  _mutex = (int*)calloc( (((numberAtoms+1)*numberAtoms) >> 1), sizeof( int ) );
  mutexSet = (mutexSet_t*)calloc( SIZE_ATOMS, sizeof( mutexSet_t ) );
  if( !_mutex || !mutexSet )
    fatal( noMoreMemory );

  if( mutexesAllPairs )
    {
      /* bootstrap mutex set. Another method: add all pairs <p,q> of atoms.
       */
      for( int i = 1; i < SIZE_ATOMS; ++i )
        for( int j = 1; j < i; ++j )
          {
            /* if the staticCompilation flag is set, then all static atoms
               were removed. In other case, don't consider them when building
               the mutexes.
            */
            if( ((staticCompilation == 1) ||
                 (!asserted( staticAtom, i ) && !asserted( staticAtom, j ))) &&
                (!asserted( staticInitialState, i ) || !asserted( staticInitialState, j )) )
              newMutex( i, j, &mutexList );
          }
    }
  else
    {
      /* bootstrap mutex set. Briefly, add those <p,q> such that exists an operator
         op with p in ADD(op) and q in DEL(op). After this, protect each initial
         mutex <p,q> with a mutexes <p,r> (correspondngly <q,r>) for r in PREC(op')
         where op' is an operator with q in ADD(op') (correspondingly p).
      */
      for( size_t i = 0; i < numberOperators; ++i )
        if( operatorTable[i].valid == 1 )
          {
            /* I have no checked the proper use of staticAtom detection for
               this part, so don't use that information.
            */
            for( int* a = operatorTable[i].add; *a != 0; ++a )
              for( int* d = operatorTable[i].del; *d != 0; ++d )
                if( !asserted( staticInitialState, *a ) || !asserted( staticInitialState, *d ) )
                  newMutex( *a, *d, &mutexList );
          }

      /* go over all mutex <p,q> and "protect" them */
      mutex_t* tmpList = nullptr;
      for( mutex_t* mutex = mutexList; mutex != nullptr; mutex = mutex->next )
        {
          /* add protection using operators op with p in ADD(op) */
          if( invAddTable[mutex->x] != nullptr )
            for( int* op = invAddTable[mutex->x]; *op != 0; ++op )
              for( int* p = operatorTable[(*op)-1].prec; *p != 0; ++p )
                if( !MUTEX( mutex->y, *p ) &&
                    (!asserted( staticInitialState, mutex->y ) || !asserted( staticInitialState, *p )) )
                  newMutex( mutex->y, *p, &tmpList );

          /* add protection using operators op with q in ADD(op) */
          if( invAddTable[mutex->y] != nullptr )
            for( int* op = invAddTable[mutex->y]; *op != 0; ++op )
              for( int* p = operatorTable[(*op)-1].prec; *p != 0; ++p )
                if( !MUTEX( mutex->x, *p ) &&
                    (!asserted( staticInitialState, mutex->x ) || !asserted( staticInitialState, *p )) )
                  newMutex( mutex->x, *p, &tmpList );
        }

      /* fusion the initial mutex set with "protectors" */
      if( tmpList != nullptr )
        {
          mutex_t* mutex;
          for( mutex = tmpList; mutex->next != nullptr; mutex = mutex->next );
          mutex->next = mutexList;
          mutexList = tmpList;
        }
    }

  /* refinement: delete mutexes (p,q) that don't satisfiy one of the three conditions.
     First condition was already tested in the mutex set bootstrap, so check only
     for second, and third condition.
  */
  int change;
  do {
    change = 0;
    for( mutex_t *tmpMutex, *tmpList = nullptr, *mutex = mutexList; mutex != nullptr; mutex = tmpMutex )
      {
        mutex_t* tmpMutex = mutex->next;
        int deleteCondition = 0;

        /* second condition: exists an operator op st p \in ADD(op) and
           q \not\in DEL(op) and (q \in ADD(op) or for all r \in PREC(op),
           (r,q) is not a mutex).
        */
        if( (deleteCondition == 0) && (invAddTable[mutex->x] != nullptr) )
          {
            /* look for a witness */
            int* op;
            for( op = invAddTable[mutex->x]; *op != 0; ++op )
              {
                int *d, *a, *p;
                /* q \not\in DEL(op) */
                for( d = operatorTable[(*op)-1].del; (*d != 0) && (*d != mutex->y); ++d );
                if( *d != 0 )
                  continue;
                /* claim: q is not in DEL(op) */

                /* q \in ADD(op) */
                for( a = operatorTable[(*op)-1].add; (*a != 0) && (*a != mutex->y); ++a );
                if( *a != 0 )
                  break;
                /* claim: q is not in ADD(op) */

                /* for all r \in PREC(op), (r,q) is not a mutex */
                for( p = operatorTable[(*op)-1].prec; *p != 0; ++p )
                  if( MUTEX( *p, mutex->y ) )
                    break;
                if( *p == 0 )
                  break;
                /* claim: for some r \in PREC(op), (r,q) is a mutex */
              }

            /* delete mutex */
            if( *op != 0 )
              deleteCondition = 2;
          }

        /* third condition: exists an operator op st q \in ADD(op) and
           p \not\in DEL(op) and (p \in ADD(op) or for all r \in PREC(op),
           (r,p) is not a mutex).
        */
        if( (deleteCondition == 0) && (invAddTable[mutex->y] != nullptr) )
          {
            /* look for a witness */
            int* op;
            for( op = invAddTable[mutex->y]; *op != 0; ++op )
              {
                int *d, *a, *p;
                /* p \not\in DEL(op) */
                for( d = operatorTable[(*op)-1].del; (*d != 0) && (*d != mutex->x); ++d );
                if( *d != 0 )
                  continue;
                /* claim: p is not in DEL(op) */

                /* p \in ADD(op) */
                for( a = operatorTable[(*op)-1].add; (*a != 0) && (*a != mutex->x); ++a );
                if( *a != 0 )
                  break;
                /* claim: p is not in ADD(op) */

                /* for all r \in PREC(op), (r,p) is not a mutex */
                for( p = operatorTable[(*op)-1].prec; *p != 0; ++p )
                  if( MUTEX( *p, mutex->x ) )
                    break;
                if( *p == 0 )
                  break;
                /* claim: for some r \in PREC(op), (r,p) is a mutex */
              }

            /* delete mutex */
            if( *op != 0 )
              deleteCondition = 3;
          }

        /* delete mutex */
        if( deleteCondition > 0 )
          {
            delMutex( mutex );
            change = 1;
          }
      }
  } while( change == 1 );

  /* print mutexes */
  if( verbose >= 5 )
    for( mutex_t* mutex = mutexList; mutex != nullptr; mutex = mutex->next )
      {
        fprintf( stderr, "mutex <%s,", readAtomName( mutex->x ) );
        fprintf( stderr, "%s>\n", readAtomName( mutex->y ) );
      }

  /* print total number of mutexes */
  fprintf( stderr, "MUTEXES: number detected mutexes = %d\n", numberMutexes );

  /* register exit */
  registerExit();
}


void
mutexSetCompilation( void )
{
  /* register entry */
  registerEntry( "mutexSetCompilation()" );

  /* mutexSet creation */
  for( size_t i = 1; i < SIZE_ATOMS; ++i )
    if( mutexSet[i].size > 0 )
      newMutexSet( i );

  /* mutexSet fill */
  for( mutex_t *tm, *m = mutexList; m != nullptr; m = tm )
    {
      tm = m->next;
      delMutex( m );
      ++mutexSet[m->x].size;
      if( (mutexSet[m->x].size > mutexSet[m->y].size) ||
          ((mutexSet[m->x].size == mutexSet[m->y].size) && (m->x > m->y)) )
        {
          m->next = mutexSet[m->x].set;
          mutexSet[m->x].set = m;
        }
      else
        {
          m->next = mutexSet[m->y].set;
          mutexSet[m->y].set = m;
        }
    }

  /* calculation of set sizes */
  for( mutexSet_t* s = mutexSetList; s != nullptr; s = s->next )
    {
      s->size = 0;
      for( mutex_t* m = s->set; m != nullptr; ++s->size, m = m->next );
    }
  assert( mutexList == nullptr );

  /* register exit */
  registerExit();
}


void
newMutex( int x, int y, mutex_t **mutexList )
{
  mutex_t *mutex;

  if( MUTEX( x, y ) == 0 )
    {
      if( !(mutex = (mutex_t*)malloc( sizeof( mutex_t ) )) )
        fatal( noMoreMemory );
      mutex->x = x;
      mutex->y = y;
      mutex->prev = nullptr;
      mutex->next = *mutexList;
      if( *mutexList != nullptr )
        (*mutexList)->prev = mutex;
      (*mutexList) = mutex;
      MUTEX( x, y ) = 1;

      ++mutexSet[x].size;
      ++numberMutexes;
    }
}


void
delMutex( mutex_t *mutex )
{
  if( mutex->prev != nullptr )
    mutex->prev->next = mutex->next;
  else
    mutexList = mutex->next;

  if( mutex->next != nullptr )
    mutex->next->prev = mutex->prev;

  MUTEX( mutex->x, mutex->y ) = 0;

  --mutexSet[mutex->x].size;
  --numberMutexes;
}


void
newMutexSet( int x )
{
  mutexSet_t *set, *prev;

  mutexSet[x].x = x;
  mutexSet[x].set = nullptr;
  mutexSet[x].next = nullptr;
  for( set = mutexSetList, prev = nullptr; (set != nullptr) && (set->size > mutexSet[x].size);
       prev = set, set = set->next );
  if( set == nullptr )
    {
      if( prev == nullptr )
        mutexSetList = &mutexSet[x];
      else
        prev->next = &mutexSet[x];
    }
  else
    {
      if( prev == nullptr )
        {
          mutexSet[x].next = mutexSetList;
          mutexSetList = &mutexSet[x];
        }
      else
        {
          prev->next = &mutexSet[x];
          mutexSet[x].next = set;
        }
    }
}



/*********************************************************
**********************************************************
**
** Main Initialization
**
**/

void
initialize( void )
{
  extern void generateVarsAndValues( void );

  /* register entry */
  registerEntry( "initialize()" );

  /* atomHashTable initialization */
  memset( atomHashTable, 0, ATOMHASHSIZE * sizeof( iatom_t* ) );

  /* check dimensionality */
  if( numberSchema >= MAXSCHEMA )
    fatal( maxSchema );

  /* initialState and goalState identification */
  generateVarsAndValues();

  /* initial state */
  for( int* a = _low_initialAtoms; *a != 0; ++a )
    set( staticInitialState, *a );

  /* goal state */
  int* p = _low_copyGoalAtoms;
  for( int* a = _low_goalAtoms; *a != 0; ++a )
  {
    set( staticGoalState, *a );
    *p++ = *a;
  }
  *p = 0;
  
  /* operator instantiation */
  operatorCompilation();

  /* generate valid operators list */
  validOperators = (int*)malloc( (numberOperators + 1) * sizeof( int ) );
  if( !validOperators )
    fatal( noMoreMemory );
  int* op = validOperators;
  for( size_t i = 0; i < numberOperators; *op++ = i++ );
  *op = -1;
  
  // TODO hack random number initialization
  if (statsFile != nullptr)
    fprintf(statsFile, ", ");
  int seed = 123456789;
  for (char* c = problemFile; *c != 0; ++c)
    seed *= 7, seed += *c;
  rng = std::mt19937_64(seed);
  /* TODO make random walks configurable: randomly move start and goal */
  if (EGraphOut == "Test/trash.eg")
  {
    randomWalk(staticInitialState, 0);
    randomWalk(staticGoalState, 0);
    p = _low_initialAtoms;
    for (size_t at = 1; at < SIZE_ATOMS; ++at)
      if ( asserted( staticInitialState, at ) )
      {
        *p++ = at;
      }
    *p = 0;
    p = _low_goalAtoms;
    for (size_t at = 1; at < SIZE_ATOMS; ++at)
      if ( asserted( staticGoalState, at ) )
      {
        *p++ = at;
      }
    *p = 0;
    p = _low_copyGoalAtoms;
    for (size_t at = 1; at < SIZE_ATOMS; ++at)
      if ( asserted( staticGoalState, at ) )
      {
        *p++ = at;
      }
    *p = 0;
  }

  /* some general info */
  fprintf( stderr, "GENERAL: node size %d = %d (fixed) + %d (variable)\n",
           (int)NODESIZE, (int)sizeof(node_t), (int)NODESIZE-(int)sizeof(node_t) );
  fprintf( stderr, "GENERAL: number of relevant atoms = %d\n", numberAtoms );

  /* H1 initialization */
  H1Setup( staticInitialState );
  memcpy( backwardH1Cost, H1Cost, ATOMSPERPACK * MAXATOMPACKS * sizeof( cost_t ) );

  /* H1E initialization */
  H1ESetup( staticInitialState );
  memcpy( backwardH1ECost, H1ECost, ATOMSPERPACK * MAXATOMPACKS * sizeof( cost_t ) );

  /* more general info */
  fprintf( stderr, "GENERAL: number of operators = %d\n", numberOperators );
  if( _low_requirements & REQ_ADL )
    fprintf( stderr, "GENERAL: number of H operators = %d\n", numberHOperators );

  /* guess an upper bound for bucketTableSize and allocate memory for proper structures */
  int table_size = 0;
  for( size_t i = 1; i < SIZE_ATOMS; ++i )
    if( backwardH1Cost[i].plus < INT_MAX )
      table_size += backwardH1Cost[i].plus; // TODO egraph: backwardH1ECost?
  table_size = max( table_size, MINBUCKETTABLESIZE );
  resizeBucketTable(table_size);

  /* nodeHashTable initialization */
  if( !(nodeHashValues = (unsigned*)malloc( SIZE_ATOMS * sizeof( unsigned ) )) )
    fatal( noMoreMemory );
  for( size_t i = 0; i < SIZE_ATOMS; ++i )
    nodeHashValues[i] = lrand48() % NODEHASHSIZE;
  memset( nodeHashDiameter, 0, NODEHASHSIZE * sizeof( int ) );
  memset( nodeHashTable, 0, NODEHASHSIZE * sizeof( node_t* ) );

  /* successful initialization */
  globalInitialized = 1;

  /* register exit */
  registerExit();
}


void
backwardSearchInitialization( schedule_t *schedule )
{
  static int initialized = 0;

  if( (schedule->searchDirection == BACKWARD) && (initialized == 0) )
    {
      initialized = 1;

#if !defined(USE_MUTEX)
      /* H2 initialization */
      H2Setup( staticInitialState );

      /* further operator prunning */
      for( int *p, *q, *op = validOperators; *op != -1; ++op )
        {
          for( p = operatorTable[*op].prec; *p != 0; ++p )
            {
              for( q = p; *q != 0; ++q )
                if( PAIR( *p, *q ).max == INT_MAX )
                  {
                    operatorTable[*op].valid = 0;
                    if( verbose >= 3 )
                      fprintf( stderr, "invalidating operator %s (%d)\n", operatorTable[*op].name, *op );
                    break;
                  }
              if( *q != 0 )
                break;
            }

          /* need to remove it? */
          if( (p != nullptr) && (*p != 0) )
            for( p = op; *p != -1; ++p )
              *p = *(p+1);
        }
#endif

      /* these three procedures should be called in this order! */
#if defined(USE_MUTEX)
      mutexCompilation();
#endif
      admissibleOperatorCompilation();
#if defined(USE_MUTEX)
      mutexSetCompilation();
#endif
    }
}



/*********************************************************
**********************************************************
**
** Planning
**
**/

int
goalState( atom_t *state )
{
  int* g;
  for( g = _low_goalAtoms; *g != 0; ++g )
    if( !asserted( state, *g ) )
      break;
  return( *g == 0 );
}


int
checkSolution( node_t *node )
{
  if( searchDirection == FORWARD )
  {
    return( goalState( node->state ) );
  }
  else
  {
    /* set initial state */
    memcpy( staticState, staticInitialState, MAXATOMPACKS * sizeof( atom_t ) );

    /* apply operators */
    while( (node != nullptr) && (node->father != nullptr) )
    {
      int* atom;
      /* check preconditions */
      for( atom = operatorTable[node->operatorId].prec; (*atom != 0) && asserted( staticState, *atom ); ++atom );
      if( *atom != 0 )
      {
        /* fprintf( stderr, "****** TENTATIVE SOLUTION IS NOT **********\n" ); */
        return( 0 );
      }

      /* apply add-list */
      for( atom = operatorTable[node->operatorId].add; *atom != 0; ++atom )
        set( staticState, *atom );

      /* apply del-list */
      for( atom = operatorTable[node->operatorId].del; *atom != 0; ++atom )
        clear( staticState, *atom );

      /* next operator */
      node = node->father;
    }

    /* check goal state */
    return( goalState( staticState ) );
  }
}


int
checkProblem()
{
  // TODO egraph: check H1ECost

  /* check H1Costs for atoms in goal */
  for( int* p = _low_copyGoalAtoms; *p != 0; ++p ) {
    if( asserted(staticAtom,*p) ) {
      if( !asserted(staticInitialState,*p) ) {
        fprintf(stderr, "SOLUTION: goal atom %s is static but not in initial situation\n", readAtomName(*p));
        return(0);
      }
    } else {
      if( backwardH1Cost[*p].max == INT_MAX ) {
        fprintf(stderr, "SOLUTION: goal atom %s has infinite backward h1-cost\n", readAtomName(*p));
        return(0);
      }
    }
  }

  /* check H1Costs for atoms in goal */
  for( int* p = _low_goalAtoms; *p != 0; ++p ) {
    if( backwardH1Cost[*p].max == INT_MAX ) {
      fprintf(stderr, "SOLUTION: goal atom %s has infinite backward h1-cost\n", readAtomName(*p));
      return(0);
    }
  }

  /* check H2Costs for atoms in goal */
  if( H2Computed == 1 ) {
    for( int* p = _low_goalAtoms; *p != 0; ++p ) {
      for( int* q = p; *q != 0; ++q ) {
        if( PAIR(*p,*q).max == INT_MAX ) {
          fprintf(stderr, "SOLUTION: pair of goal atoms (%s,%s) has infinite h2-cost\n", readAtomName(*p), readAtomName(*q));
          return(0);
        }
      }
    }
  }

  /* problem is ok */
  return(1);
}


bool
readEGraph(string fileName)
{
  cost_t costInfty, costUnit;
  costInfty.plus = costInfty.max = INT_MAX / 2;
  costUnit.plus = costUnit.max = 1;
  for (auto& exper : experience)
  {
    free(exper.tailState);
    free(exper.headState);
  }
  experience.clear();
  eNode = { staticGoalState };
  
  // TODO remove debug code
  /*fprintf( stdout, "ALL ATOM NAMES\n" );
  for( size_t p = 1; p < SIZE_ATOMS; ++p )
  {
    fprintf( stdout, "%s ", readAtomName(p) );
  }
  fprintf( stdout, "\n" );*/
  
  FILE *file = fopen( fileName.c_str(), "r" );
  if (file == nullptr)
    {
      perror( "ERROR: could not read Egraph from file" );
      eDist = { { costUnit } };
      return false;
    }
  
  fprintf(stdout, "readEGraph:");
  vector<std::pair<int,int> > edges;
  char name[128];
  while (fgets(name, 128, file) != nullptr && name[0] != '\0')
  {
    name[strlen(name)-1] = '\0';
    fprintf(stdout, " %s", name);
    experience.push_back(experience_t());
    experience_t& exper = experience.back();
    strcpy(exper.opName, name);
    exper.tailState = (atom_t*) malloc( SIZE_PACKS * sizeof(atom_t) );
    exper.headState = (atom_t*) malloc( SIZE_PACKS * sizeof(atom_t) );
    
    /*for (size_t i = 0; i < SIZE_PACKS; ++i)
    {
      fscanf( file, " %u ", &exper.tailState[i].pack );
    }
    for (size_t i = 0; i < SIZE_PACKS; ++i)
    {
      fscanf( file, " %u ", &exper.headState[i].pack );
    }*/
    for (size_t i = 0; i < SIZE_PACKS; ++i)
      exper.tailState[i].pack = exper.headState[i].pack = 0;
    int atomsToRead;
    fscanf(file, " %u ", &atomsToRead);
    while (atomsToRead--)
    {
      fgets(name, 128, file);
      name[strlen(name)-1] = '\0';
      for (size_t p = 1; p < SIZE_ATOMS; ++p)
        if (!strcmp(name, readAtomName(p)))
          set(exper.tailState, p);
    }
    fscanf(file, " %u ", &atomsToRead);
    while (atomsToRead--)
    {
      fgets(name, 128, file);
      name[strlen(name)-1] = '\0';
      for (size_t p = 1; p < SIZE_ATOMS; ++p)
        if (!strcmp(name, readAtomName(p)))
          set(exper.headState, p);
    }
    
    int idxT, idxH;
    for (idxT = 0; idxT < eNode.size(); ++idxT)
      if (!stateCmp(eNode[idxT], exper.tailState))
        break;
    if (idxT == eNode.size())
      eNode.push_back(exper.tailState);
    for (idxH = 0; idxH < eNode.size(); ++idxH)
      if (!stateCmp(eNode[idxH], exper.headState))
        break;
    if (idxH == eNode.size())
      eNode.push_back(exper.headState);
    edges.push_back(std::make_pair(idxT, idxH));
  }
  fprintf(stdout, "\n");
  fclose( file );
  
  eDist = vector<vector<cost_t> >(eNode.size(), vector<cost_t>(eNode.size(), costInfty));
  for (auto& edge : edges)
    eDist[edge.first][edge.second] = costUnit;
  
  for (size_t i = 0; i < eNode.size(); ++i)
  {
    H1Setup( eNode[i] );
    
    for (size_t j = 0; j < eNode.size(); ++j)
    {
      cost_t dist;
      dist.plus = dist.max = 0;
      for (size_t p = 1; p < SIZE_ATOMS; ++p)
      if ( asserted( eNode[j], p ) )
        { 
          if( H1Cost[p].plus == INT_MAX )
          {
            dist.plus = INT_MAX;
            dist.max = INT_MAX;
            break;
          }
          else
          {
            dist.plus = PLUSSUM( dist.plus, H1Cost[p].plus );
            dist.max = max( dist.max, H1Cost[p].max );
          }
        }
      if (dist.plus != INT_MAX)
      {
        eDist[i][j].plus = min(eDist[i][j].plus, (unsigned long) experienceWeight*dist.plus);
        eDist[i][j].max = min(eDist[i][j].max, (unsigned long) experienceWeight*dist.max);
      }
    }
  }
  
  // Floyd-Warshall
  for (size_t k = 0; k < eNode.size(); ++k)
    for (size_t i = 0; i < eNode.size(); ++i)
      for (size_t j = 0; j < eNode.size(); ++j)
      {
        eDist[i][j].plus = min(eDist[i][j].plus, eDist[i][k].plus + eDist[k][j].plus);
        eDist[i][j].max = min(eDist[i][j].max, eDist[i][k].max + eDist[k][j].max);
      }
  // TODO remove debug code
  fprintf(statsFile, "EgSize= %u ", experience.size());
  /*for (size_t i = 0; i < eNode.size(); ++i)
  {
      fprintf( stdout, "%d'th distance to goal is %d:\t", i, eDist[i][0].max );
      for( size_t p = 1; p < SIZE_ATOMS; ++p )
        if( asserted( eNode[i], p ) )
        {
          fprintf( stdout, "%s ", readAtomName(p) );
        }
      fprintf( stdout, "\n" );
  }*/
  return true;
}


bool
printEGraph(string fileName, double proportion = 1)
{
  FILE *file = fopen( fileName.c_str(), "w" );
  if (file == nullptr)
  {
    perror( "ERROR: could not write EGraph to file" );
    return false;
  }
  
  // TODO remove debug code
  fprintf(statsFile, "ExpSize= %u ", experience.size());
  
  int n = experience.size();
  int k = std::round(n * proportion);
  for (auto& exper: experience)
  {
    std::uniform_int_distribution<int> dist(0, --n);
    if (dist(rng) < k) // TODO debug: randomly remember edges
    {
      --k;
      fprintf( file, "%s\n", exper.opName );
      /*for (size_t i = 0; i < SIZE_PACKS; ++i)
        fprintf( file, " %u", exper.tailState[i].pack );
      for (size_t i = 0; i < SIZE_PACKS; ++i)
        fprintf( file, " %u", exper.headState[i].pack );
      fprintf( file, "\n" );*/
      int atomsToPrint = 0;
      for (size_t p = 1; p < SIZE_ATOMS; ++p)
        if (asserted(exper.tailState, p))
          ++atomsToPrint;
      fprintf( file, "%u\n", atomsToPrint );
      for (size_t p = 1; p < SIZE_ATOMS; ++p)
        if (asserted(exper.tailState, p))
          fprintf( file, "%s\n", readAtomName(p) );
      atomsToPrint = 0;
      for (size_t p = 1; p < SIZE_ATOMS; ++p)
        if (asserted(exper.headState, p))
          ++atomsToPrint;
      fprintf( file, "%u\n", atomsToPrint );
      for (size_t p = 1; p < SIZE_ATOMS; ++p)
        if (asserted(exper.headState, p))
          fprintf( file, "%s\n", readAtomName(p) );
    }
  }
  fclose( file );
  return true;
}


void
printOperator( FILE *file, int alpha )
{
  fprintf( file, "operator %d \"%s\":\n", alpha, operatorTable[alpha].name );
  fprintf( file, "\tprec = " );
  for( int* p = operatorTable[alpha].prec; *p != 0; ++p )
    fprintf( file, "%s ", readAtomByNumber( *p )->name );
  fprintf( file, "\n\tadd = " );
  for( int* p = operatorTable[alpha].add; *p != 0; ++p )
    fprintf( file, "%s ", readAtomByNumber( *p )->name );
  fprintf( file, "\n\tdel = " );
  for( int* p = operatorTable[alpha].del; *p != 0; ++p )
    fprintf( file, "%s ", readAtomByNumber( *p )->name );
  fprintf( file, "\n" );
}


void
printState( FILE *file, atom_t *state )
{
  int i;

  fprintf( file, "====>" );
  for( size_t i = 1; i < SIZE_ATOMS; ++i )
    if( asserted( state, i ) )
      fprintf( file, " %s[%d]", readAtomName( i ), i );
  fprintf( file, "\n" );
}


void
printNode( FILE *file, char *prefix, node_t *node )
{
  fprintf( file, "%s: node %p (cost = %d, h1plus = %d, h1max = %d, h2plus = %d, h2max = %d, h1eplus = %d, h1emax = %d)\n",
           prefix, node, node->cost, node->h1_plus, node->h1_max, node->h2_plus, node->h2_max, node->h1e_plus, node->h1e_max );
  if( verbose >= 6 )
    {
      if( node->operatorId != -1 )
        fprintf( file, "operator = %s\n", operatorTable[node->operatorId].name );
      printState( file, node->state );
    }
}


void
printPath( FILE *file, node_t *node, char *prefix, char *suffix )
{
  if( searchDirection == FORWARD )
  {
    if( node->father != nullptr )
    {
      printPath( file, node->father, prefix, suffix );
      fprintf( file, "%s%s%s", prefix, operatorTable[node->operatorId].name, suffix );
    }
  }
  else
  {
    while( node != nullptr )
    {
      if( node->father != nullptr )
        fprintf( file, "%s%s%s", prefix, operatorTable[node->operatorId].name, suffix );
      node = node->father;
    }
  }
}


void
memorizePath( node_t *node )
{
  assert( node != nullptr );
  fprintf(stderr, "memorizePath ");
  if( searchDirection == FORWARD )
    {
      fprintf(stderr, "Forward:");
      while( node->father != nullptr )
      {
        experience.push_back(experience_t());
        experience_t& exper = experience.back();
        exper.tailState = (atom_t*) malloc( SIZE_PACKS * sizeof(atom_t) );
        exper.headState = (atom_t*) malloc( SIZE_PACKS * sizeof(atom_t) );
        for (size_t i = 0; i < SIZE_PACKS; ++i)
          exper.tailState[i].pack = node->father->state[i].pack;
        for (size_t i = 0; i < SIZE_PACKS; ++i)
          exper.headState[i].pack = node->state[i].pack;
        
        strcpy(exper.opName, operatorTable[node->operatorId].name);
        fprintf(stderr, " %d-%s", experience.size(), exper.opName);
        
        for (size_t i = 0; i+1 < experience.size(); ++i)
        if (!stateCmp(experience[i].tailState, exper.tailState)
          && !strcmp(experience[i].opName, exper.opName))
          {
            free(exper.tailState);
            free(exper.headState);
            experience.pop_back();
            break;
          }
        node = node->father;
      }
    }
  else
    {
      fprintf(stderr, "Backward:");
      while( node->father != nullptr )
      {
        // TODO egraph: backward edges memorize which endpoint?
        experience.push_back(experience_t());
        experience_t& exper = experience.back();
        exper.tailState = (atom_t*) malloc( SIZE_PACKS * sizeof(atom_t) );
        exper.headState = (atom_t*) malloc( SIZE_PACKS * sizeof(atom_t) );
        for (size_t i = 0; i < SIZE_PACKS; ++i)
          exper.tailState[i].pack = node->father->state[i].pack;
        for (size_t i = 0; i < SIZE_PACKS; ++i)
          exper.headState[i].pack = node->state[i].pack;
        
        strcpy(exper.opName, operatorTable[node->operatorId].name);
        fprintf(stderr, " %d-%s", experience.size(), exper.opName);
        
        for (size_t i = 0; i+1 < experience.size(); ++i)
        if (!stateCmp(experience[i].tailState, exper.tailState)
          && !strcmp(experience[i].opName, exper.opName))
          {
            free(exper.tailState);
            free(exper.headState);
            experience.pop_back();
            break;
          }
        node = node->father;
      }
    }
    fprintf(stderr, "\n");
}


void
printStatistics( void )
{
  /* print problem data & statistics */
  nodeHashStatistics(); // TODO: change stdout back to stderr
  fprintf( stdout, "STATISTICS: number expanded nodes = %d\n", expandedNodes );
  fprintf( stdout, "STATISTICS: number generated nodes = %d\n", generatedNodes );
  fprintf( stdout, "STATISTICS: average branching factor = %f\n", (float)generatedNodes / (float)expandedNodes );
  
  // TODO debug remove extra prints
  if (statsFile != nullptr)
  {
   if (EGraphIn == "Test/none.eg")
      fprintf( statsFile, "Gen= %d ", generatedNodes );
    else
      fprintf( statsFile, "Gen= %d\t%s\n", generatedNodes, problemFile );
  }
}


void
cleanStatistics( void )
{
  expandedNodes = 0;
  generatedNodes = 0;
}



/*********************************************************
**********************************************************
**
** Best-First Search
**
**/

node_t *
startBFS( schedule_t *schedule )
{
  /* register entry */
  registerEntry( "startBFS()" );

  /* cleaning */
  cleanStatistics();
  cleanNodeHash();
  cleanLists();

  /* initialization */
  node_t* node = getNode();
  memset( firstNodeInBucket, 0, bucketTableSize * sizeof( node_t* ) );
  memset( lastNodeInBucket, 0, bucketTableSize * sizeof( node_t* ) );
  node->operatorId = -1;
  node->father = nullptr;
  node->cost = 0;

  /* initial state setup */
  if( searchDirection == FORWARD )
    memcpy( node->state, staticInitialState, SIZE_PACKS * sizeof( atom_t ) );
  else
    memcpy( node->state, staticGoalState, SIZE_PACKS * sizeof( atom_t ) );

  /* insert initial node into hash/open */
  heuristics( node );
  insertIntoNodeHash( node );
  setInitialOPEN( node );
  if( verbose >= 2 )
    printState( stderr, node->state );

  /* search */
  node_t* result = BFS( schedule );

  /* register exit */
  registerExit();

  /* return */
  return( result );
}


node_t *
BFS( schedule_t *schedule )
{
  node_t **buffer;

  /* get first node */
  node_t* currentNode = getFirstOPEN();

  /* check for goal */
  if( (currentNode->h1_plus == 0) && checkSolution( currentNode ) )
    return( currentNode );

  /* initialize constraints */
  timeExpired = memoryExpired = 0;
  if( schedule->constraintType & TIME )
    setTimer( schedule->time );
  if( schedule->constraintType & MEMORY )
    memoryConstraint = schedule->memory;
  else
    memoryConstraint = -1;

  /* loop */
  while( currentNode != nullptr )
    {
      /* check constraints */
      if( timeExpired || memoryExpired )
        {
          fprintf( stderr, "CONSTRAINT: %s.\n", (timeExpired ? "time" : "memory") );
          return( nullptr );
        }

      /* basic assertion */
      assert( currentNode->valid == 1 );
      
      int children;
      /* expand situation */
      if( searchDirection == FORWARD )
        children = forwardNodeExpansion( currentNode, &buffer );
      else
        children = backwardNodeExpansion( currentNode, &buffer );

      /* print current node */
      if( verbose >= 5 )
        {
          printNode( stderr, "CURRENT NODE", currentNode );
          fprintf( stderr, "number children = %d\n", children );
          if( children == 0 )
            {
              fprintf( stderr, "action this state was %s\n", operatorTable[currentNode->operatorId].name );
              printState( stderr, currentNode->state );
            }
        }

      /* print child */
      if( verbose >= 6 )
        for( size_t i = 0; i < children; ++i )
          if( buffer[i]->valid == 1 )
            printNode( stderr, "child", buffer[i] );

      /* test for goal */
      for( size_t i = 0; i < children; ++i )
        if( (buffer[i]->valid == 1) && (buffer[i]->h1_plus == 0) && checkSolution( buffer[i] ) )
          return( buffer[i] );

      /* delete currentNode from OPEN */
      assert( nodesInOPEN > 0 );
      removeNodeFromOPEN( currentNode );

      /* insert children into OPEN */
      nodeOrdering( buffer, children );

      /* next node */
      currentNode = getFirstOPEN();
    }
  return( nullptr );
}



/*********************************************************
**********************************************************
**
** Greedy Best-First Search
**
**/

node_t *
startGBFS( schedule_t *schedule )
{
  /* register entry */
  registerEntry( "startGBFS()" );

  /* cleaning */
  cleanStatistics();
  cleanNodeHash();
  cleanLists();

  /* initialization */
  node_t* node = getNode();
  memset( firstNodeInBucket, 0, bucketTableSize * sizeof( node_t* ) );
  memset( lastNodeInBucket, 0, bucketTableSize * sizeof( node_t* ) );
  node->operatorId = -1;
  node->father = nullptr;
  node->cost = 0;

  /* initial state setup */
  if( searchDirection == FORWARD )
    memcpy( node->state, staticInitialState, SIZE_PACKS * sizeof( atom_t ) );
  else
    memcpy( node->state, staticGoalState, SIZE_PACKS * sizeof( atom_t ) );

  /* insert initial node into hash/open */
  heuristics( node );
  insertIntoNodeHash( node );
  setInitialOPEN( node );
  if( verbose >= 2 )
    printState( stderr, node->state );

  /* search */
  node_t* result = GBFS( schedule );

  /* register exit */
  registerExit();

  /* return */
  return( result );
}


node_t *
GBFS( schedule_t *schedule )
{
  node_t **buffer;

  /* get first node */
  node_t* currentNode = getFirstOPEN();

  /* check for goal */
  if( (currentNode->h1_plus == 0) && checkSolution( currentNode ) )
    return( currentNode );

  /* initialize constraints */
  timeExpired = memoryExpired = 0;
  if( schedule->constraintType & TIME )
    setTimer( schedule->time );
  if( schedule->constraintType & MEMORY )
    memoryConstraint = schedule->memory;
  else
    memoryConstraint = -1;

  /* loop */
  assert( nodesInOPEN > 0 );
  while( currentNode != nullptr )
    {
      assert( nodesInOPEN > 0 );
      /* check constraints */
      if( timeExpired || memoryExpired )
        {
          fprintf( stderr, "CONSTRAINT: %s.\n", (timeExpired ? "time" : "memory") );
          return( nullptr );
        }

      /* basic assertion */
      assert( currentNode->valid == 1 );
      
      int children;
      /* expand node */
      if( searchDirection == FORWARD )
        children = forwardNodeExpansion( currentNode, &buffer );
      else
        children = backwardNodeExpansion( currentNode, &buffer );

      /* print current node */
      if( verbose >= 5 )
        {
          printNode( stderr, "CURRENT NODE", currentNode );
          fprintf( stderr, "number children = %d\n", children );
          assert( nodesInOPEN > 0 );
        }

      /* print child */
      if( verbose >= 6 )
        for( size_t i = 0; i < children; ++i )
          if( buffer[i]->valid == 1 )
            printNode( stderr, "child", buffer[i] );

      /* test for goal */
      for( size_t i = 0; i < children; ++i )
        if( (buffer[i]->valid == 1) && (buffer[i]->h1_plus == 0) && checkSolution( buffer[i] ) )
          return( buffer[i] );

      /* delete currentNode from OPEN */
      assert( nodesInOPEN > 0 );
      removeNodeFromOPEN( currentNode );
      assert( nodesInOPEN >= 0 );

      /* insert children into OPEN */
      nodeOrdering( buffer, children );
      assert( nodesInOPEN > 0 );

      /* next node: first try a probe */
      node_t* nextNode = nullptr; // TODO egraph: why h1plus? This will not necessarily choose the best f-value
      for( size_t i = 0; i < children; ++i )
        if( (buffer[i]->valid == 1) &&
            ((nextNode == nullptr) ||
             (buffer[i]->h1_plus < nextNode->h1_plus) ||
             ((buffer[i]->h1_plus == nextNode->h1_plus) && (buffer[i]->h1_max < nextNode->h1_max))) )
          nextNode = buffer[i];

      if( (nextNode != nullptr) &&
          ((nextNode->h1_plus > currentNode->h1_plus) ||
           ((nextNode->h1_plus == currentNode->h1_plus) && (nextNode->h1_max >= currentNode->h1_max))) )
        nextNode = nullptr;

      /* next node: if nothing, select by BFS */
      if( nextNode == nullptr )
        currentNode = getFirstOPEN();
      else
        currentNode = nextNode;
      assert( currentNode->open == 1 );
    }
  return( nullptr );
}



/*********************************************************
**********************************************************
**
** Registration of Entry/Exit points
**
**/

void
registerEntry( char *procedure )
{
  procRegister_t* proc;

  if( !(proc = (procRegister_t*)malloc( sizeof( procRegister_t ) )) )
    fatal( noMoreMemory );
  proc->procedure = procedure;
  proc->next = procStackTop;
  procStackTop = proc;
}


int
registerExit( void )
{
  struct rusage r_usage;

  if( procStackTop != nullptr )
    {
      procRegister_t* proc = procStackTop;
      getrusage( RUSAGE_SELF, &r_usage );
      proc->diffTime = (float)r_usage.ru_utime.tv_sec + (float)r_usage.ru_stime.tv_sec +
        (float)r_usage.ru_utime.tv_usec / (float)1000000 + (float)r_usage.ru_stime.tv_usec / (float)1000000;
      // TODO: change stdout back to stderr
      fprintf( stdout, "REGISTER: %s took %f secs\n", proc->procedure, proc->diffTime );
      procStackTop = proc->next;
      free( proc );
      return( 1 );
    }
  else
    {
      return( 0 );
    }
}


float
currentElapsedTime( void )
{
  struct rusage r_usage;

  getrusage( RUSAGE_SELF, &r_usage );
  return( (float)r_usage.ru_utime.tv_sec + (float)r_usage.ru_stime.tv_sec +
          (float)r_usage.ru_utime.tv_usec / (float)1000000 + (float)r_usage.ru_stime.tv_usec / (float)1000000 );
}


void
flushAllRegisters( void )
{
  while( registerExit() );
}



/*********************************************************
**********************************************************
**
** Signals
**
**/

void
SIGHUPHandler( int sig )
{
  flushAllRegisters();
  exit( 1 );
}


void
timerExpirationHandler( int sig )
{
  timeExpired = 1;
}


void
setTimer( unsigned long msecs )
{
  static struct itimerval itv;

  /* clear global expirationTime flag */
  timeExpired = 0;

  /* set signal handler */
  signal( SIGVTALRM, &timerExpirationHandler );

  /* set it */
  itv.it_interval.tv_sec = 0;
  itv.it_interval.tv_usec = 0;
  itv.it_value.tv_sec = msecs/1000;
  itv.it_value.tv_usec = (msecs%1000)*1000;
  setitimer( ITIMER_VIRTUAL, &itv, nullptr );
}



/*********************************************************
**********************************************************
**
** Scheduler
**
**/

node_t *
scheduler( schedule_t *schedule )
{
  node_t* result = nullptr;
  while( (result == 0) && (schedule != nullptr) )
  {
    /* check implementation */
    if( (schedule->searchHeuristic == H2PLUS) ||
        ((schedule->searchHeuristic == H2MAX) && (schedule->searchDirection == FORWARD)) ||
        ((_low_requirements & REQ_ADL) && (schedule->searchDirection == BACKWARD)) )
      notYetImplemented( schedule );

    /* setup search parameters */
    searchAlgorithm = schedule->searchAlgorithm;
    searchDirection = schedule->searchDirection;
    searchHeuristic = schedule->searchHeuristic;

    /* additional initializations */
    backwardSearchInitialization( schedule );
    
    /* E-graph initialization */
    readEGraph(EGraphIn);

    /* weak check if problem has solution */
    if( checkProblem() == 0 )
    {
      fprintf( stderr, "SOLUTION: problem has no solution.\n" );
      break;
    }

    /* print current schedule */
    fprintf( stderr, "SCHEDULE: %s %s with %s and W = %.1f\n",
              searchDirectionName[searchDirection],
              searchAlgorithmName[searchAlgorithm],
              searchHeuristicName[searchHeuristic],
              heuristicWeight );
    if( schedule->constraintType != 0 )
      fprintf( stderr, "SCHEDULE: constraints are time = %ld (msecs) and memory = %ld (Mbytes).\n",
                (schedule->constraintType & TIME ? schedule->time : -1),
                (schedule->constraintType & MEMORY ? schedule->memory : -1) );
    else
      fprintf( stderr, "SCHEDULE: unconstrained.\n" );

    /* make the search */
    switch( searchAlgorithm )
    {
      case _GBFS:
        result = startGBFS( schedule );
        break;
      case _BFS:
        result = startBFS( schedule );
        break;
    }

    /* print search results and some statistics */
    if( result == nullptr )
    {
      fprintf( stderr, "SOLUTION: no solution found\n" );
      // TODO debug remove extra prints
      if (statsFile != nullptr )
          fprintf( statsFile, "!" );
    }
    else
    {
      fprintf( stderr, "SOLUTION: solution found (length = %d)\n", result->cost );
      if( verbose > 0 )
        printPath( stderr, result, "+  ", "\n" );
      memorizePath(result);
      printEGraph(EGraphOut);
      
      // TODO remove debug code
      fprintf(statsFile, "SolSize= %u ", result->cost);
    }
      
    printStatistics();

    /* next option */
    schedule = schedule->next;
  }
  return( result );
}


/*********************************************************
**********************************************************
**
** Parameter Reading
**
**/

int
readSymbolicParameter( char *s, char **table, int tableSize )
{
  /* lookup table */
  for( size_t i = 0; i < tableSize; ++i )
    if( !strcasecmp( s, table[i] ) )
      return( i );
  return( -1 );
}


void
parseSchedule( char *s )
{
  /* free resources */
  if( globalSchedule != nullptr )
    free( globalSchedule );

  /* go over all options */
  char* option = strtok( s, ":" );
  while( option != nullptr )
    {
      /* check option syntax */
      if( (option[0] != '[') || (option[strlen(option)-1] != ']') )
        fatal( optionSyntax );

      /* extract info */
      char* p = option + 1;
      char* direction = p;
      p = strchr( p, ',' );
      *p++ = '\0';
      char* heuristic = p;
      p = strchr( p, ',' );
      *p++ = '\0';
      char* time = p;
      p = strchr( p, ']' );
      *p++ = '\0';
      if( (direction == nullptr) || (heuristic == nullptr) || (time == nullptr) )
        fatal( optionSyntax );

      /* build schedule */
      schedule_t* schedule = (schedule_t*)malloc( sizeof( schedule_t ) );
      schedule->memory = 0;
      schedule->time = atoi( time );
      schedule->constraintType = (schedule->time <= 0 ? 0 : TIME);
      schedule->searchAlgorithm = _BFS;
      schedule->searchDirection = readSymbolicParameter( direction, searchDirectionName, numberDirections );
      schedule->searchHeuristic = readSymbolicParameter( heuristic, searchHeuristicName, numberHeuristics );
      schedule->next = nullptr;

      /* check parameters */
      if( (schedule->searchDirection == -1) || (schedule->searchHeuristic == -1) )
        fatal( searchParameter );

      /* insert schedule */
      schedule_t* sp;
      for( sp = globalSchedule; (sp != nullptr) && (sp->next != nullptr); sp = sp->next );
      if( sp == nullptr )
        globalSchedule = schedule;
      else
        sp->next = schedule;

      /* next option */
      option = strtok( nullptr, ":" );
    }
}



/*********************************************************
**********************************************************
**
** Main Section
**
**/

void
_fatal( int returnCode, char *s, char *file, int line )
{
  switch( returnCode )
    {
    case noMoreMemory:
      fprintf( stderr, "ERROR[%s:%d]: no more memory\n", file, line );
      break;
    case maxAtoms:
      fprintf( stderr, "ERROR: maximum atoms reached. Recompile\n" );
      break;
    case maxSchema:
      fprintf( stderr, "ERROR: maximum operator schemata reached. Recompile\n" );
      break;
    case noAlgorithm:
      fprintf( stderr, "ERROR: no search algorithm specified\n" );
      break;
    case optionSyntax:
      fprintf( stderr, "ERROR: schedule option. Format is [<direction>,<heuristic>,<time>]\n" );
      break;
    case searchParameter:
      fprintf( stderr, "ERROR: either bad search direction or heuristic.\n" );
      break;
    case noError:
      break;
    }
  fprintf( stderr, "ERROR: fatal error.\n" );
  printStatistics();
  flushAllRegisters();
  exit( returnCode );
}


void
usage( void )
{
  fprintf( stderr, "usage: hsp <flags>* [ <algorithm> | -S <schedule> ] <problem.pddl> <domain.pddl>\n" );
  fprintf( stderr, "where <flags> are among:\n" );
  fprintf( stderr, "   -v <level>\t\tVerbose level >= 0 (default is 1).\n" );
  fprintf( stderr, "   -w <weight>\t\tFloat to weight the heuristic component of the cost function.\n" );
  fprintf( stderr, "   -e <eweight>\t\tFloat to additionally weight non E-graph edges in the heuristic.\n" );
  fprintf( stderr, "   -f <fi> <fo>\t\tFile locations at which to retrieve and store the E-graph.\n" );
  fprintf( stderr, "<algorithm> is:\n" );
  fprintf( stderr, "   -a <algorithm>\tEither 'bfs' or 'gbfs'.\n" );
  fprintf( stderr, "   -d <direction>\tEither 'forward' or 'backward'.\n" );
  fprintf( stderr, "   -h <heuristic>\tOne of 'h1plus', 'h1max', 'h2plus', 'h2max', 'h1eplus', 'h1emax'.\n" );
  fprintf( stderr, "<schedule> is a colon separated <option> list where each option has\n" );
  fprintf( stderr, "form '[<direction>,<heuristic>,<msecs>]'. The options are performed\n" );
  fprintf( stderr, "sequentially until one finds a plan, or no more options are available\n" );
  fprintf( stderr, "(each option is attempted with the given time constraint).\n" );
  exit( -1 );
}


void
notYetImplemented( schedule_t *schedule )
{
  if( !(_low_requirements & REQ_ADL) )
    fprintf( stderr, "sorry, the option '[%s,%s]' is not yet supported.\n",
             searchDirectionName[schedule->searchDirection],
             searchHeuristicName[schedule->searchHeuristic] );
  else // TODO egraph?
    fprintf( stderr, "sorry, for simple-adl it is only supported 'forward' search with 'h1max' or 'h1plus'.\n" );
  exit( -1 );
}


void
parseArguments( int argc, char **argv )
{
  /* set some defaults */
  string progname = argv[0];
  verbose = 1;
  mutexesAllPairs = 1;

  /* set default schedule */
  staticCompilation = 1;
  heuristicWeight = 5.0;
  experienceWeight = 1.0;
  searchAlgorithm = _GBFS;
  searchDirection = BACKWARD;
  searchHeuristic = H1PLUS;
  EGraphIn = "EGraph.txt";
  EGraphOut = "EGraph.txt";
  StatisticsOut = "Test/Stats.txt";
  statsFile = fopen( StatisticsOut.c_str(), "a" ); // TODO close file

  /* parse options */
  while( argc > 1 && *(*++argv) == '-' )
    {
      switch( (*argv)[1] )
        {
        case 'a':
          searchAlgorithm = readSymbolicParameter( *++argv, searchAlgorithmName, numberAlgorithms );
          --argc;
          break;
        case 'd':
          searchDirection = readSymbolicParameter( *++argv, searchDirectionName, numberDirections );
          --argc;
          break;
        case 'h':
          searchHeuristic = readSymbolicParameter( *++argv, searchHeuristicName, numberHeuristics );
          --argc;
          break;
        case 'f': // specify filenames for E-graph
          EGraphIn = *++argv;
          EGraphOut = *++argv;
          argc -= 2;
          break;
        case 'v':
          verbose = atoi( *++argv );
          --argc;
          break;
        case 'w':
          heuristicWeight = atof( *++argv );
          --argc;
          break;
        case 'e':
          experienceWeight = atof( *++argv );
          --argc;
          break;
        case 'S':
          scheduleString = *++argv;
          parseSchedule( strdup( scheduleString ) );
          --argc;
          break;
        default:
          usage();
          break;
        }
      --argc;
    }
  if( (argc != 3) || (searchAlgorithm == -1) || (searchDirection == -1) || (searchHeuristic == -1) )
    {
      usage();
    }
  else
    {
      problemFile = *argv++;
      domainFile = *argv;
    }

  /* set default schedule if empty one (i.e. if no "-S" parameter) */
  if( globalSchedule == nullptr )
    {
      globalSchedule = (schedule_t*)malloc( sizeof( schedule_t ) );
      globalSchedule->constraintType = 0;
      globalSchedule->searchDirection = searchDirection;
      globalSchedule->searchAlgorithm = searchAlgorithm;
      globalSchedule->searchHeuristic = searchHeuristic;
      globalSchedule->next = nullptr;
    }

  /* print parameters */
  fprintf( stderr, "PROBLEM: solving problem: %s %s\n", problemFile, domainFile );
  if( scheduleString != nullptr )
    fprintf( stderr, "PARAMETERS: -S %s -w %f -v %d\n", scheduleString, heuristicWeight, verbose );
  else
    fprintf( stderr, "PARAMETERS: -a %s -d %s -h %s -w %f -v %d\n",
             searchAlgorithmName[searchAlgorithm], searchDirectionName[searchDirection],
             searchHeuristicName[searchHeuristic], heuristicWeight, verbose );
}


int
parseProblem( void )
{
  static char* files[2];
  extern int yyparse( void );
  extern int lineno;

  int rv = 0;
  files[0] = problemFile;
  files[1] = domainFile;
  for( int fd, file = 0; file < 2; ++file )
    if( (fd = open( files[file], O_RDONLY )) == -1 )
    {
      perror( "ERROR: parsing files" );
      exit( -1 );
    }
    else
    {
      /* redirection of fd to stdin */
      if( file == 0 )
        close( fileno( stdin ) );
      else
        clearerr( stdin );
      dup( fd );
      _low_yyfile = files[file];
      lineno = 1;
      rv += yyparse();
      close( fileno( stdin ) );
      close( fd );
    }
  return( rv );
}


int
main( int argc, char **argv )
{
  /* set signal handler */
  signal( SIGHUP, &SIGHUPHandler );
  
  /* register entry */
  registerEntry( "main()" );
  
  /* initialize */
  parseArguments( argc, argv );
  
  /* parse problem */
  node_t* result = nullptr;
  int rv = parseProblem();
  if( rv == noError )
  {
    /* initialize planner */
    initializeMemoryMgmt();
    initialize();

    /* go! */
    result = scheduler( globalSchedule );
    rv = (result == nullptr);
  }
  else
  {
    fprintf( stderr, "PARSE: parse error.\n" );
  }
  
  /* register exit */
  registerExit();
#if defined(COMPETITION_OUTPUT)
  if( result != nullptr )
  {
    fprintf( stdout, "%s,%.4f,%d", _low_problemName, currentElapsedTime(), result->cost );
    printPath( stdout, result, ",", "" );
    fprintf( stdout, "\n" );
  }
#endif

  return( rv );
}


} // end extern "C"
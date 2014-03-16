/*
**
** Universidad Simon Bolivar, 1999, 2000 (c)
** Blai Bonet and Hector Geffner. 1999, 2000.
**
*/


#ifndef PLANNER
#define PLANNER
/*********************************************************
**********************************************************
**
** Macros
**
**/

#if 0
#define MUTEX(x,y)              ((y) <= (x) ? _mutex[((y)+(((x)*((x)-1))>>1))-1] : _mutex[((x)+(((y)*((y)-1))>>1))-1])
#endif
#define MUTEX(x,y)              _mutex[(min(x,y)+((max(x,y)*(max(x,y)-1))>>1))-1]

#define fatal(code)             _fatal( (code), NULL, __FILE__, __LINE__ )
#define fatal1(code,s)          _fatal( (code), (s), __FILE__, __LINE__ )

#define PLUSSUM(x,y)            (((x) == INT_MAX) || ((y) == INT_MAX) ? INT_MAX : (x) + (y))
#if 0
#define PAIR(x,y)               ((x) <= (y) ? H2Cost[(x)][(y)-(x)] : H2Cost[(y)][(x)-(y)])
#endif
#define PAIR(x,y)               H2Cost[min(x,y)][max(x,y)-min(x,y)]



/*********************************************************
**********************************************************
**
** Constants
**
**/

#define MAXPARAMETERS          20
const int ATOMSPERPACK          = 8*sizeof( unsigned );
const int MAXATOMPACKS          = 1<<16;         /* enough for 4096 * 32 = 131072 atoms */
const int MAXSCHEMA             = 100000;

const int MINBUCKETTABLESIZE    = 2048;
const int NODEHASHSIZE          = 5119;            /* prime nearest to 5K */
const int ATOMHASHSIZE          = 1021;            /* prime nearest to 1K */
const float INCRATE             = 1.5;           /* increase rate for dynamic sized structures */

#define SIZE_ATOMS              (1 + numberAtoms)
#define SIZE_PACKS              (1 + numberAtoms / ATOMSPERPACK)
#define NODESIZE                (sizeof( node_t ) + SIZE_PACKS * sizeof( atom_t ))
const int MEGABYTE              = 1024*1024;

/* PDDL requirements */
const int REQ_STRIPS            = 1;
const int REQ_EQUALITY          = 2;
const int REQ_TYPING            = 4;
const int REQ_ADL               = 8;

/* search direction */
const int FORWARD               = 0;
const int BACKWARD              = 1;
const int numberDirections      = 2;

/* search algorithm */
const int _BFS                  = 0;
const int _GBFS                 = 1;
const int numberAlgorithms      = 2;

/* heuristics */
const int H1PLUS                = 0;
const int H1MAX                 = 1;
const int H2PLUS                = 2;
const int H2MAX                 = 3;
const int H2MAXP                = 4;
const int H1EPLUS               = 5;
const int H1EMAX                = 6;
const int numberHeuristics      = 7;

/* constraint types */
const int TIME                  = 1;
const int MEMORY                = 2;

/* exit codes */
const int noError               = 00;
const int noMoreMemory          = 10;
const int maxSchema             = 20;
const int maxAtoms              = 30;
const int noAlgorithm           = 40;
const int noChildren            = 50;
const int optionSyntax          = 60;
const int searchParameter       = 70;



/*********************************************************
**********************************************************
**
** Structures and Typedefs
**
**/

struct iatom_s
{
  int  idx;
  char name[128];
  int  parameters[MAXPARAMETERS];
  struct iatom_s *next;
} iatom_s;
typedef struct iatom_s iatom_t;


struct atom_s
{
  unsigned pack;
} atom_s;
typedef struct atom_s atom_t;


struct experience_s
{
  char opName[128];
  atom_t* tailState;
  atom_t* headState;
} experience_s;
typedef struct experience_s experience_t;


struct node_s
{
  int cost;                               /* cost from root to this node */
  unsigned long h1_plus;                  /* value of h^1-plus */
  unsigned long h2_plus;                  /* value of h^2-plus */
  unsigned long h1_max;                   /* value of h^1-max */
  unsigned long h2_max;                   /* value of h^2-max */
  unsigned long h1e_plus;                 /* value of h^1-e-plus */
  unsigned long h1e_max;                  /* value of h^1-e-max */
  int fvalue;                             /* f-function value */
  int valid;                              /* valid state? */
  int operatorId;                         /* operator id that leads to this state */
  int bucket;                             /* bucket number of node */
  int open;                               /* true if node in OPEN list */

  struct node_s *father;                  /* link to father nodes */
  struct node_s *hashNext;                /* link into nodeHashTable */
  struct node_s *hashPrev;                /* link into nodeHashTable */
  struct node_s *bucketNext;              /* link into bucketTable */
  struct node_s *bucketPrev;              /* link into bucketTable */

  atom_t *state;                          /* current state (must be the last field)  */
} node_s;
typedef struct node_s node_t;


struct suboperator_s
{
  int precSize;
  int addSize;
  int delSize;
  int *prec;
  int *add;
  int *del;
  struct suboperator_s *next;
} suboperator_s;
typedef struct suboperator_s suboperator_t;


struct operator_s
{
  char *name;
  int valid;
  int father;
  int precSize;
  int addSize;
  int delSize;
  int *prec;
  int *add;
  int *del;
  suboperator_t *suboperators;
} operator_s;
typedef struct operator_s operator_t;


struct cost_s
{
  unsigned long plus;
  unsigned long max;
} cost_s;
typedef struct cost_s cost_t;


struct mutex_s
{
  int x;
  int y;
  struct mutex_s *next;
  struct mutex_s *prev;
} mutex_s;
typedef struct mutex_s mutex_t;


struct mutexSet_s
{
  int x;
  int size;
  struct mutex_s *set;
  struct mutexSet_s *next;
} mutexSet_s;
typedef struct mutexSet_s mutexSet_t;


struct procRegister_s
{
  char *   procedure;
  float    diffTime;
  struct procRegister_s *next;
} procRegister_s;
typedef struct procRegister_s procRegister_t;


struct schedule_s
{
  int constraintType;
  int searchAlgorithm;
  int searchDirection;
  int searchHeuristic;
  unsigned long memory;
  unsigned long time;
  struct schedule_s *next;
} schedule_s;
typedef struct schedule_s schedule_t;



/*********************************************************
**********************************************************
**
** Extern Variables
**
**/

extern int             numberSchema;
extern int             globalInitialized;
extern int             operatorPrec[];
extern int             operatorPrecSize;
extern int             operatorAdd[];
extern int             operatorAddSize;
extern int             operatorDel[];
extern int             operatorDelSize;
extern int **          values;
extern int **          vars;

extern iatom_t *       readAtomHash( register int * );
extern void            addParents( register int, register int * );

extern char *          _low_yyfile;
extern int             _low_requirements;
extern char *          _low_problemName;
extern char *          _low_domainName;
extern char **         _low_schemaName;
extern char **         _low_objectName;
extern char **         _low_predicateName;
extern int             _low_numberPredicates;
extern schema_t *      _low_schemaTable[];
extern int             _low_initialAtoms[];
extern int             _low_goalAtoms[];
extern int             _low_copyGoalAtoms[];
extern suboperator_t * _low_suboperators;
extern int             _low_groundingOperators;
extern int             _low_negatedAtom[];



#endif

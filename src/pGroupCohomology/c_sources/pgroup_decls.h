/*****************************************************************************
   pgroup_decls.h : Header files listing declarations in pgroup.c

       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>

  Distributed under the terms of the GNU General Public License (GPL),
  version 2 or later (at your choice)

    This code is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    General Public License for more details.

  The full text of the GPL is available at:

                  http://www.gnu.org/licenses/
*****************************************************************************/

#include "meataxe.h"
#include "pgroup.h"
// the latter is for yesno etcetera

// "protecting" variables for macro evaluation
#if !defined(yes)
#define yes yes
#endif
#if !defined(no)
#define no no
#endif
#if !defined(true)
#define true true
#endif
#if !defined(false)
#define false false
#endif


#if !defined(__PGROUP_DECLS_INCLUDED)	/* Include only once */
#define __PGROUP_DECLS_INCLUDED

/* Simon King: define the following in meataxe.h (where it belongs) as macro
 PTR ptrPlus(PTR base, long offset);
*/
/* returns PTR to base + offset */

inline long maxlong(long n1, long n2);
inline long minlong(long n1, long n2);
inline long modifiedMinlong(long n1, long n2);

/* Idea: -1 represents plus infinity */
long listFun(long *l, long len, long fun(long n1, long n2));

// boolean certainThat(yesno yn);
#if !defined(certainThat)
#define certainThat(yn) ( ((yn) == yes) ? true : false )
#endif

// yesno booleanYesno(boolean stat);
#if !defined(booleanYesno)
#define booleanYesno(stat) (((stat)) ? yes : no)
#endif

// boolean longBoolean(long lbool);
#if !defined(longBoolean)
#define longBoolean(lbool) (((lbool)) ? true : false)
#endif

//long booleanLong(boolean bool);
#if !defined(booleanLong)
#define booleanLong(bool) (((bool)) ? 1 : 0)
#endif
char *booleanString(boolean stat);
char *yesnoString(yesno yn);

void loadDimensions(group_t *group);
long pathDimension(group_t *group, path_t *p);
void markPathDimensions(group_t *group);

group_t *newGroupRecord (void);
inline group_t *namedGroupRecord(char *stem);
void freeGroupRecord (group_t *group);

void readHeader(group_t *group); /* WARNING: only for groupInfo */
void loadNonTips(group_t *group);
inline void freeNonTips(char **nontip);

path_t *allocatePathTree(group_t *group);
void buildPathTree(group_t *group);
void buildLeftPathTree(group_t *group);
inline void freeRoot(path_t *root);

matrix_t **loadMatrixList(group_t *group, char *name, long num);
inline void loadActionMatrices(group_t *group);
inline void loadLeftActionMatrices(group_t *group);
void makeLeftActionMatrices(group_t *group);
void saveMatrixList(group_t *group, matrix_t **action, long num, char *name);
void saveActionMatrices(group_t *group);
void saveLeftActionMatrices(group_t *group);
matrix_t **allocateMatrixList(group_t *group, long num);
inline matrix_t **allocateActionMatrices(group_t *group);
inline void freeMatrixList(matrix_t **mat);
inline void freeActionMatrices(matrix_t **mat);

void addmul(matrix_t *dest, matrix_t *src, FEL f);

char *djg_strdup(char *src);
void strext(char *dest, char *stem, char *ext);

char arrowName(long a);

boolean smallerJenningsWord(JenningsWord_t *w1, JenningsWord_t *w2);

void innerLeftActionMatrix(group_t *group, PTR vec, PTR dest);
inline matrix_t *leftActionMatrix(group_t *group, PTR vec);
void innerRightActionMatrix(group_t *group, PTR vec, PTR dest);
inline matrix_t *rightActionMatrix(group_t *group, PTR vec);
void loadActionMatrices(group_t *group);
void loadLeftActionMatrices(group_t *group);

void loadGeneralRegularActionMatrices(group_t *group, matrix_t **action,
  char *name, long nor);
void loadRegularActionMatrices(group_t *group);
void makeBasisChangeMatrices(group_t *group);
void saveBasisChangeMatrices(group_t *group);
void loadBasisChangeMatrices(group_t *group);
void readRegFileHeader(group_t *group);

void convertPermutationsToAsci(char *infile, char *outfile);

void innerRightCompose(group_t *group, PTR alpha, PTR beta, long s, long r,
  long q, PTR scratch, PTR gamma);
/* alpha: matrix representing map from free rk s to free rk r
   beta : free rk r to free rk q
   free = free RIGHT G-module
   Result gamma: free rk s to free rk q: First alpha then beta
   Then gamma s * q rows
   gamma_{ki} = \sum_{j=1}^r beta_{kj} alpha_{ji}
   gamma must be initialised before calling innerCompose
   scratch: scratch space, nontips+1 rows
   Right: use right action matrix of alpha_ji
*/
void innerLeftCompose(group_t *group, PTR alpha, PTR beta, long s, long r,
  long q, PTR scratch, PTR gamma);
/* alpha: matrix representing map from free rk s to free rk r
   beta : free rk r to free rk q
   free = free RIGHT G-module
   Result gamma: free rk s to free rk q: First alpha then beta
   Then gamma s * q rows
   gamma_{ki} = \sum_{j=1}^r beta_{kj} alpha_{ji}
   gamma must be initialised before calling innerCompose
   scratch: scratch space, nontips+1 rows
   Left: use left action matrix of beta_kj
*/

void innerRightProduct(const matrix_t *dest, const matrix_t *src, PTR scratch);
void innerBasisChangeReg2Nontips(group_t *group, matrix_t **matlist,
  long num, PTR workspace);
void innerBasisChangeNontips2Reg(group_t *group, matrix_t **matlist,
  long num, PTR workspace);
void basisChangeReg2Nontips(group_t *group, matrix_t **matlist, long num);
void changeActionMatricesReg2Nontips(group_t *group);

long pathTreeGirth(group_t *group);
void calculateDimSteps(group_t *group);
group_t *fullyLoadedGroupRecord(char *stem);

inline boolean fileExists(const char *name);

inline boolean mateq(matrix_t *mat1, matrix_t *mat2);
int verifyGroupIsAbelian(group_t *A);

long *newLongArray(long N);
matrix_t *myMatalloc(long fl, long nor, long noc);
/* Can handle nor==0 */
matrix_t *myMatmul(matrix_t *dest, matrix_t *src);
/* Can handle dest->nor==0; znoc is src->noc at end */

long *collected(long *l);
/* l[0] is length of l */
long listPos(long *l, long n);

#endif

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
 PTR FfGetPtr(PTR base, long offset);
*/
/* returns PTR to base + offset */

inline long maxlong(long n1, long n2);
inline long minlong(long n1, long n2);
inline long modifiedMinlong(long n1, long n2);

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

int loadDimensions(group_t *group);
long pathDimension(group_t *group, path_t *p);
int markPathDimensions(group_t *group);

group_t *newGroupRecord (void);
inline group_t *namedGroupRecord(const char *stem);
void freeGroupRecord (group_t *group);

int readHeader(group_t *group); /* WARNING: only for groupInfo */
int loadNonTips(group_t *group);
inline void freeNonTips(char **nontip);

path_t *allocatePathTree(group_t *group);
int buildPathTree(group_t *group);
int buildLeftPathTree(group_t *group);
inline void freeRoot(path_t *root);

Matrix_t **loadMatrixList(group_t *group, char *name, long num);
inline int loadActionMatrices(group_t *group);
inline int loadLeftActionMatrices(group_t *group);
int makeLeftActionMatrices(group_t *group);
int saveMatrixList(group_t *group, Matrix_t **action, long num, char *name);
int saveActionMatrices(group_t *group);
int saveLeftActionMatrices(group_t *group);
Matrix_t **allocateMatrixList(group_t *group, long num);
inline Matrix_t **allocateActionMatrices(group_t *group);
inline void freeMatrixList(Matrix_t **mat);
inline void freeActionMatrices(Matrix_t **mat);

void addmul(Matrix_t *dest, Matrix_t *src, FEL f);

char *mtx_strdup(const char *src);
void strext(char *dest, char *stem, char *ext);

char arrowName(long a);

boolean smallerJenningsWord(JenningsWord_t *w1, JenningsWord_t *w2);

void innerLeftActionMatrix(group_t *group, PTR vec, PTR dest);
inline Matrix_t *leftActionMatrix(group_t *group, PTR vec);
void innerRightActionMatrix(group_t *group, PTR vec, PTR dest);
inline Matrix_t *rightActionMatrix(group_t *group, PTR vec);
inline int loadActionMatrices(group_t *group);
inline int loadLeftActionMatrices(group_t *group);

int loadGeneralRegularActionMatrices(group_t *group, Matrix_t **action,
  char *name, long nor);
int loadRegularActionMatrices(group_t *group);
int makeBasisChangeMatrices(group_t *group);
int saveBasisChangeMatrices(group_t *group);
int loadBasisChangeMatrices(group_t *group);
int readRegFileHeader(group_t *group);

int convertPermutationsToAsci(const char *infile, const char *outfile);

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

int innerRightProduct(const Matrix_t *dest, const Matrix_t *src, PTR scratch);
int innerBasisChangeReg2Nontips(group_t *group, Matrix_t **matlist,
  long num, PTR workspace);
int innerBasisChangeNontips2Reg(group_t *group, Matrix_t **matlist,
  long num, PTR workspace);
int basisChangeReg2Nontips(group_t *group, Matrix_t **matlist, long num);
int changeActionMatricesReg2Nontips(group_t *group);

long pathTreeGirth(group_t *group);
int calculateDimSteps(group_t *group);
group_t *fullyLoadedGroupRecord(char *stem);

inline boolean fileExists(const char *name);

inline boolean mateq(Matrix_t *mat1, Matrix_t *mat2);
int verifyGroupIsAbelian(group_t *A);

long *newLongArray(long N);

/* l[0] is length of l */
long listPos(long *l, long n);

#endif

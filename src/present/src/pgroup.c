/*****************************************************************************
   pgroup.c : routines for group algebras, common to most programs

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

#include "pgroup.h"
#include <unistd.h>
#include "meataxe.h"

/******************************************************************************/
char *djg_strdup(char *src)
{
  char *dest = (char *) malloc((strlen(src)+1) * sizeof(char));
  if (!dest) AllocationError("djg_strdup");
  strcpy(dest,src);
  return dest;
}

/******************************************************************************/
void strext(char *dest, char *stem, char *ext)
{
  strcpy(dest, stem);
  strcat(dest, ext);
  return;
}

/******************************************************************************/
static inline void gzip(const char *name)
{
/*  char buffer[MAXLINE];
  sprintf(buffer,"gzip %s",name);
  system(buffer);
*/
}

/*****************************************************************************/
inline boolean fileExists(char *name)
{
  int stat = access(name, F_OK);
  return (stat == 0) ? true : false;
}

/******************************************************************************/
static inline void gunzip(const char *name)
{
  char buffer[MAXLINE];
  sprintf(buffer,"gunzip %s",name);
  if (!fileExists(name)) { system(buffer); }
}


/******************************************************************************
 S. King (2008-12): This and some of the following functions should be macros
boolean certainThat(yesno yn)
{
  return (yn == yes) ? true : false;
}
*/

/******************************************************************************
yesno booleanYesno(boolean stat)
{
  return (stat) ? yes : no;
}
*/

/******************************************************************************
boolean longBoolean(long lbool)
{
  return (lbool) ? true : false;
}
*/

/******************************************************************************
long booleanLong(boolean bool)
{
  return (bool) ? 1 : 0;
}
*/

/******************************************************************************/
char *booleanString(boolean stat)
{
  static char buffer[MAXLINE];
  sprintf(buffer, (stat) ? "true" : "false");
  return buffer;
}

/******************************************************************************/
char *yesnoString(yesno yn)
{
  static char buffer[MAXLINE];
  if (yn == yes) sprintf(buffer, "yes");
  else
  {
    if (yn == no) sprintf(buffer, "no");
    else sprintf(buffer, "unknown");
  }
  return buffer;
}

/******************************************************************************/
group_t *newGroupRecord (void)
{
  group_t *group = (group_t *) malloc(sizeof(group_t));
  if (!group) AllocationError("newGroupRecord");
  group->stem = NULL;
  group->nontip = NULL;
  group->root = NULL;
  group->lroot = NULL;
  group->action = NULL;
  group->laction = NULL;
  group->bch = NULL;
  group->dim = NULL;
  group->dS = NULL;
  return group;
}

/******************************************************************************/
inline group_t *namedGroupRecord (char *stem)
{
  group_t *group = newGroupRecord();
  group->stem = djg_strdup(stem);
  return group;
}

/******************************************************************************/
static inline int IsWhitespace(char c)
{
  switch (c)
  {
    case ' ':
    case '\n':
    case '\t':
      return 1; /* true */
      break;
    default:
      return 0; /* false */
      break;
  }
}

/******************************************************************************/
static inline int IsDigit(char c)
{
  switch (c)
  {
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
      return 1; /* true */
      break;
    default:
      return 0; /* false */
      break;
  }
}

/*******************************************************************************
* static long ctol(char c)
* {
  switch (c)
  {
    case '0':
      return 0;
      break;
    case '1':
      return 1;
      break;
    case '2':
      return 2;
      break;
    case '3':
      return 3;
      break;
    case '4':
      return 4;
      break;
    case '5':
      return 5;
      break;
    case '6':
      return 6;
      break;
    case '7':
      return 7;
      break;
    case '8':
      return 8;
      break;
    case '9':
      return 9;
      break;
    default:
      return -1;
      break;
  }
* }
*/

/******************************************************************************/
static inline char NextSignificantCharacter(FILE *fp)
{
  char c;
  while ((c = fgetc(fp)) != EOF && IsWhitespace(c));
  return c;
}

/******************************************************************************/
static long GetNextLong(FILE *fp, char *buffer)
{
  char c, *this;
  long i;
  this = buffer; i = 0;
  for (this = buffer, i = 0, c = NextSignificantCharacter(fp);
       ;
       this++, i++, c = fgetc(fp))
  {
    if (c == EOF)
      OtherError("Unexpected EOF in GetNextLong");
    else if (i == MAXLINE)
      OtherError("Buffer Overflow in GetNextLong");
    else if (IsDigit(c))
      *this = c;
    else
      break;
  }
  *this = '\0';
  return atoi(buffer);
}

/******************************************************************************/
static inline char GetNextChar(FILE *fp)
{
  char c = NextSignificantCharacter(fp);
  if (c == EOF)
    OtherError("Unexpected EOF in GetNextChar");
  return c;
}

/******************************************************************************
static boolean IsArrow(char c, long arrows)
{
  return (c >= 'a' && c < 'a' + arrows);
}
Simon King (2008-12) make it a macro
*/
#if !defined(IsArrow)
#define IsArrow(c,arrows) ((c) >= 'a' && c < 'a' + (arrows))
#endif

/*******************************************************************************
* static boolean IsPathStart(char c, long arrows)
* {
  return (IsArrow(c,arrows) || c == '(');
* }
*/

/******************************************************************************/
static char GetNextPath(FILE *fp, char *dest, long maxlength, long arrows)
/* Returns character immediately following path */
{
  char c, *this;
  long i;
  this = dest; i = 0;
  for (this = dest, i = 0, c = NextSignificantCharacter(fp);
       ;
       this++, i++, c = fgetc(fp))
  {
    if (c == EOF)
      OtherError("Unexpected EOF in GetNextPath");
    else if (IsArrow(c,arrows))
      *this = c;
    else if (c == '(')
    {
      *(this++) = c;
      if (!IsDigit(c = NextSignificantCharacter(fp)))
        OtherError("GetNextPath: invalid vertex");
      *(this++) = c;
      if ((c = NextSignificantCharacter(fp)) != ')')
        OtherError("GetNextPath: invalid vertex path format");
      *(this++) = c;
      c = NextSignificantCharacter(fp);
      break;
    }
    else
      break;
    if (i == maxlength)
      OtherError("Buffer Overflow in GetNextPath");
  }
  *this = '\0';
  return c;
}

/******************************************************************************/
void loadDimensions(group_t *group)
{
  long dims, *dim;
  long i;
  char buffer[MAXLINE], dimfile[MAXLINE];
  FILE *fp;
  strext(dimfile, group->stem, ".dims");
  fp = fopen(dimfile, "r");
  if (!fp) OtherError("loadDimensions: opening file");
  dims = GetNextLong(fp, buffer);
  dim = (long *) malloc((dims+1) << LONGSH);
  if (!dim) AllocationError("loadDimensions");
  dim[0] = dims;
  for (i = 1; i <= dims; i++)
    dim[i] = GetNextLong(fp, buffer);
  fclose(fp);
  group->dim = dim;
  return;
}

/******************************************************************************/
void readHeader(group_t *group)
{
  char nonTipsFile[MAXLINE];
  FILE *fp;
  char *buffer;
  strext(nonTipsFile, group->stem, ".nontips");
  buffer = malloc((MAXLINE + 1) * sizeof(char));
  if (!buffer)
    AllocationError("loadNonTips");
  fp = fopen(nonTipsFile,"r");
  if (!fp)
    OtherError("Can't open input file in loadNonTips");
  group->arrows = GetNextLong(fp,buffer);
  group->nontips = GetNextLong(fp,buffer);
  group->maxlength = GetNextLong(fp,buffer);
  group->mintips = GetNextLong(fp,buffer);
  group->p = GetNextLong(fp,buffer);
  group->ordering = GetNextChar(fp);
  fclose(fp);
  return;
}

/******************************************************************************/
void loadNonTips(group_t *group)
{
  char nonTipsFile[MAXLINE];
  char **nontip;
  long maxlength, nontips, stringMaxlength;
  register long i;
  FILE *fp;
  char *buffer, c;
  strext(nonTipsFile, group->stem, ".nontips");
  buffer = malloc((MAXLINE + 1) * sizeof(char));
  if (!buffer)
    AllocationError("loadNonTips");
  fp = fopen(nonTipsFile,"r");
  if (!fp)
    OtherError("Can't open input file in loadNonTips");
  group->arrows = GetNextLong(fp,buffer);
  nontips = GetNextLong(fp,buffer);
  group->nontips = nontips;
  maxlength = GetNextLong(fp,buffer);
  stringMaxlength = (maxlength >= 3) ? maxlength : 3;
  group->maxlength = maxlength;
  group->mintips = GetNextLong(fp,buffer);
  group->p = GetNextLong(fp,buffer);
  group->ordering = GetNextChar(fp);
  zsetfield(group->p);
  zsetlen(nontips);
  //  nontip = (char **) malloc(nontips * sizeof(char *));
  nontip = (char **) malloc(nontips << PTRSH);
  if (!nontip)
    AllocationError("loadNonTips: 2");
  *nontip = (char *) malloc((stringMaxlength+1) * nontips
                              * sizeof(char));
  if (!*nontip)
    AllocationError("loadNonTips: 3");
  for (i = 1; i < nontips; i++)
    nontip[i] = nontip[0] + i * (stringMaxlength + 1);
  for (i = 0; i < nontips; i++)
  {
    c = GetNextPath(fp,nontip[i], stringMaxlength, group->arrows);
    /* c is the character immediately following the path; should be ';' */
    if (c != ';') OtherError("Corrupt data in loadNonTips");
  }
  fclose(fp);
  group->nontip = nontip;
  return;
}

/******************************************************************************/
path_t *allocatePathTree(group_t *group)
{
  path_t *root;
  long arrows = group->arrows;
  long nontips = group->nontips;
  register long i;
  path_t **kinder;
  root = (path_t *) malloc(nontips * sizeof(path_t));
  if (!root) AllocationError("allocatePathTree: 1");
  //  kinder = (path_t **) malloc(nontips * arrows * sizeof(path_t *));
  kinder = (path_t **) malloc(nontips * arrows << PTRSH);
  if (!kinder) AllocationError("allocatePathTree: 2");
  for (i = 0; i < nontips * arrows; i++)
    kinder[i] = NULL;
  for (i = 0; i < nontips; i++)
  {
    root[i].index = i;
    root[i].path = NULL;
    root[i].child = kinder + (i * arrows);
  }
  root[0].depth = 0;
  root[0].parent = NULL;
  root[0].path = "(1)";
  return root;
}

/******************************************************************************/
void buildPathTree(group_t *group)
{
  path_t *root;
  register long i,j;
  path_t *this, *parent;
  char arrow;
  root = allocatePathTree(group);
  for (i = 1; i < group->nontips; i++)
  {
    this = root + i; parent = root;
    this->path = group->nontip[i];
    for (j = 0, arrow = this->path[0]; this->path[j+1] != '\0'; j++)
    {
      parent = parent->child[arrow - 'a'];
      if (!parent) OtherError("buildPathTree: theoretical error");
      arrow = this->path[j+1];
    }
    parent->child[arrow - 'a'] = this;
    this->depth = parent->depth + 1;
    this->parent = parent;
    this->lastArrow = arrow - 'a';
  }
  group->root = root;
  return;
}

/******************************************************************************/
void buildLeftPathTree(group_t *group)
{
  path_t *lroot;
  register long i,j;
  path_t *this, *parent;
  char arrow;
  lroot = allocatePathTree(group);
  for (i = 1; i < group->nontips; i++)
  {
    this = lroot + i; parent = lroot;
    this->path = group->nontip[i];
    /* for (j = 1; this->path[j] != '\0'; j++) */
    for (j = strlen(this->path) - 1; j > 0; j--)
    {
      arrow = this->path[j];
      parent = parent->child[arrow - 'a'];
      if (!parent) OtherError("buildLeftPathTree: theoretical error");
    }
    arrow = this->path[0];
    parent->child[arrow - 'a'] = this;
    this->depth = parent->depth + 1;
    this->parent = parent;
    this->lastArrow = arrow - 'a';
  }
  group->lroot = lroot;
  return;
}

/******************************************************************************/
inline void freeNonTips(char **nontip)
{
  free(*nontip);
  free(nontip);
  return;
}

/******************************************************************************/
inline void freeRoot(path_t *root)
{
  free(root->child);
  free(root);
  return;
}

/******************************************************************************/
matrix_t **loadMatrixList(group_t *group, char *name, long num)
{
  matrix_t *bigmat;
  matrix_t **action; //, *mats;
  long nontips = group->nontips;
  //PTR base, ptr;
  long i;
  bigmat = matload(name); /* sets zfl, znoc to required values */
  if (!bigmat)
    OtherError("loadMatrixList: loading bigmat");
  if (bigmat->noc != nontips)
    { matfree(bigmat);
      OtherError("loadMatrixList: noc != nontips");
    }
  if (bigmat->nor != num * nontips)
    { matfree(bigmat);
      OtherError("loadMatrixList: nor ! num * nontips");
    }
  if (group->p != zchar)
    { matfree(bigmat);
      OtherError("loadMatrixList: matrices over wrong characteristic field");
    }
  /* base = bigmat->d;
     mats = (matrix_t *) malloc(num * sizeof(matrix_t));
  */
  //  action = (matrix_t **) malloc (num * sizeof(matrix_t *));
  action = (matrix_t **) malloc (num << PTRSH);
  /* if (!mats || !action) AllocationError("loadMatrixList"); 
     ptr = base;
  */
  for (i = 0; i < num; i++)
  {
    /*    action[i] = mats + i;
	  action[i]->fl = zfl;
	  action[i]->noc = nontips;
	  action[i]->nor = nontips;
	  action[i]->d = ptr;
	  zadvance(&ptr,nontips);
    */
    action[i] = _matextract(bigmat,i*nontips+1,nontips);
  }
  matfree(bigmat);
  return action;
}

/******************************************************************************/
inline void loadActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".gens");
  gunzip(name);
  group->action = loadMatrixList(group, name, group->arrows);
  gzip(name);
  return;
}

/******************************************************************************/
inline void loadLeftActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".lgens");
  gunzip(name);
  group->laction = loadMatrixList(group, name, group->arrows);
  gzip(name);
  return;
}

/******************************************************************************/
void loadBasisChangeMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".bch");
  gunzip(name);
  group->bch = loadMatrixList(group, name, 2);
  gzip(name);
  return;
}

/******************************************************************************/
void saveMatrixList(group_t *group, matrix_t **action, long num, char *name)
{
  matrix_t mat;
  mat.fl = group->p;
  mat.noc = group->nontips;
  mat.nor = group->nontips * num;
  mat.d = action[0]->d;
  if (matsave(&mat,name) != 0)
    OtherError("Saving in saveMatrixList");
  return;
}

/******************************************************************************/
void saveActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".gens");
  saveMatrixList(group, group->action, group->arrows, name);
  gzip(name);
  return;
}

/******************************************************************************/
void saveLeftActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".lgens");
  saveMatrixList(group, group->laction, group->arrows, name);
  gzip(name);
  return;
}

/******************************************************************************/
void saveBasisChangeMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".bch");
  saveMatrixList(group, group->bch, 2, name);
  gzip(name);
  return;
}

/******************************************************************************/
void saveBasisChangeMatrix(group_t *group, matrix_t *bw)
{
  char name[MAXLINE];
  strext(name, group->stem, ".bch");
  if (matsave(bw,name) != 0)
    OtherError("Saving in saveBasisChangeMatrix");
  return;
}

/******************************************************************************/
matrix_t **allocateMatrixList(group_t *group, long num)
{
  long nontips = group->nontips;
  PTR ptr, tmp;
  matrix_t *mat, **action;
  register long i;
  zsetlen(nontips);
  ptr = zalloc(num * nontips);
  mat = (matrix_t *) malloc(num * sizeof(matrix_t));
  //  action = (matrix_t **) malloc(num * sizeof(matrix_t *));
  action = (matrix_t **) malloc(num << PTRSH);
  if (!ptr || !mat || !action)
    AllocationError("allocateMatrixList");
  for (i = 0, tmp = ptr; i < num; i++, zadvance(&tmp,nontips))
  {
    action[i] = mat + i;
    action[i]->fl = zfl;
    action[i]->nor = nontips;
    action[i]->noc = nontips;
    action[i]->d = tmp;
  }
  return action;
}

/******************************************************************************/
inline matrix_t **allocateActionMatrices(group_t *group)
{
  return allocateMatrixList(group, group->arrows);
}

/******************************************************************************/
inline void freeMatrixList(matrix_t **mat)
{
  free(mat[0]->d);
  free(mat[0]);
  free(mat);
}

/******************************************************************************/
inline void freeActionMatrices(matrix_t **mat)
{
  free(mat[0]->d);
  free(mat[0]);
  free(mat);
}

/******************************************************************************/
/* returns PTR to base + offset 
   now a macro in meataxe.h, which is included by pgroup_decls.h
PTR ptrPlus(PTR base, long offset)
{
  PTR result = base;
  zadvance(&result, offset);
  return result;
}
*/
  /***************************************************************************/
  /* Simon King (2008-12): Make these macros*/
inline long maxlong(long n1, long n2)
{
  return (n1 >= n2) ? n1 : n2;
}


/******************************************************************************/
inline long minlong(long n1, long n2)
{
  return (n1 <= n2) ? n1 : n2;
}

/******************************************************************************/
inline long modifiedMinlong(long n1, long n2)
/* Allows for -1 being used to represent +infinity */
{
  if (n1 == -1) return n2;
  if (n2 == -1) return n1;
  return minlong(n1, n2);
}


/******************************************************************************/
long listFun(long *l, long len, long fun())
{
  long i, result;
  if (len <= 0) OtherError("listFun: length must be at least 1");
  result = l[0];
  for (i = 1; i < len; i++)
    result = fun(result, l[i]);
  return result;
}

/******************************************************************************/
void addmul(matrix_t *dest, matrix_t *src, FEL f)
{
  register long i;
  PTR pdest = dest->d;
  PTR psrc = src->d;
  for (i = dest->nor; i > 0; i--)
  {
    zaddmulrow(pdest,psrc,f);
    zsteprow(&pdest);
    zsteprow(&psrc);
  }
  return;
}

/******************************************************************************/
void freeGroupRecord (group_t *group)
{
  if (group->stem) free(group->stem);
  if (group->nontip) freeNonTips (group->nontip);
  if (group->root) freeRoot (group->root);
  if (group->lroot) freeRoot (group->lroot);
  if (group->action) freeActionMatrices (group->action);
  if (group->laction) freeActionMatrices (group->laction);
  if (group->bch) freeActionMatrices (group->bch);
  if (group->dim) free(group->dim);
  if (group->dS) free(group->dS);
  free (group);
  return;
}

/******************************************************************************/
char arrowName(long a)
{
  static char arrowname[] = ARROWNAMES;
  if (a >= MAXARROW) OtherError("arrowName: more arrownames please");
  return arrowname[a];
}

/******************************************************************************/
long pathDimension(group_t *group, path_t *p)
{
  if (p->depth == 0)
    return 0;
  else
    return pathDimension(group, p->parent) + group->dim[1+p->lastArrow];
}

/******************************************************************************/
void markPathDimensions(group_t *group)
{
  long i;
  switch (group->ordering)
  {
  case 'R' :
    for (i=0; i < group->nontips; i++)
      group->root[i].dim = group->root[i].depth;
    if (group->lroot)
      for (i=0; i < group->nontips; i++)
        group->lroot[i].dim = group->lroot[i].depth;
    break;
  case 'J' :
    for (i=0; i < group->nontips; i++)
      group->root[i].dim = pathDimension(group, group->root + i);
    if (group->lroot)
      for (i=0; i < group->nontips; i++)
        group->lroot[i].dim = pathDimension(group, group->lroot + i);
    break;
  default :
    OtherError("markPathDimensions: not implemented for this ordering");
    break;
  }
  return;
}

/******************************************************************************/
static inline boolean largerLex(char *s1, char *s2)
{
  char *p1, *p2;
  for (p1 = s1, p2 = s2;
       *p1 == *p2 && *p1 != '\0';  p1++, p2++);
  if (*p1 == '\0') return false;
  if (*p2 == '\0') return true;
  return (*p1 > *p2);
}

/******************************************************************************/
boolean smallerJenningsWord(JenningsWord_t *w1, JenningsWord_t *w2)
{
  if (w1->dimension != w2->dimension)
    return (w1->dimension > w2->dimension);
  if (w1->length != w2->length)
    return (w1->length < w2->length);
  return largerLex(w1->path, w2->path);
}

/******************************************************************************/
void innerRightActionMatrix(group_t *group, PTR vec, PTR dest)
{
  long a, i;
  PTR prev, this;
  memcpy(dest, vec, zsize(1));
  for (i = 1; i < group->nontips; i++)
  {
    prev = ptrPlus(dest, group->lroot[i].parent->index);
    this = ptrPlus(dest, i);
    a = group->lroot[i].lastArrow;
    zmaprow(prev, group->laction[a]->d, group->nontips, this);
  }
  return;
}

/******************************************************************************/
void innerLeftActionMatrix(group_t *group, PTR vec, PTR dest)
{
  long a, i;
  PTR prev, this;
  memcpy(dest, vec, zrowsize_io); //zsize(1));
  for (i = 1; i < group->nontips; i++)
  {
    prev = ptrPlus(dest, group->root[i].parent->index);
    this = ptrPlus(dest, i);
    a = group->root[i].lastArrow;
    zmaprow(prev, group->action[a]->d, group->nontips, this);
  }
  return;
}

/******************************************************************************/
inline matrix_t *rightActionMatrix(group_t *group, PTR vec)
{
  matrix_t *mat = matalloc(zfl, group->nontips, group->nontips);
  innerRightActionMatrix(group, vec, mat->d);
  return mat;
}

/******************************************************************************/
inline matrix_t *leftActionMatrix(group_t *group, PTR vec)
{
  matrix_t *mat = matalloc(zfl, group->nontips, group->nontips);
  innerLeftActionMatrix(group, vec, mat->d);
  return mat;
}

/******************************************************************************/
void innerRightCompose(group_t *group, PTR alpha, PTR beta, long s, long r,
  long q, PTR scratch, PTR gamma)
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
{
  long nontips = group->nontips;
  long i,j,k;
  PTR alpha_ji, beta_kj, gamma_ki;
  PTR mat = scratch, tmp = ptrPlus(scratch, nontips);
  for (i = 0; i < s; i++)
  {
    for (j = 0; j < r; j++)
    {
      alpha_ji = ptrPlus(alpha, j + i * r);
      innerRightActionMatrix(group, alpha_ji, mat);
      for (k = 0; k < q; k++)
      {
        beta_kj = ptrPlus(beta, k + j * q);
        gamma_ki = ptrPlus(gamma, k + i * q);
        zmaprow(beta_kj, mat, nontips, tmp);
        zaddrow(gamma_ki, tmp);
      }
    }
  }
  return;
}

/******************************************************************************/
void innerLeftCompose(group_t *group, PTR alpha, PTR beta, long s, long r,
  long q, PTR scratch, PTR gamma)
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
{
  long nontips = group->nontips;
  long i,j,k;
  PTR alpha_ji, beta_kj, gamma_ki;
  PTR mat = scratch, tmp = ptrPlus(scratch, nontips);
  for (k = 0; k < q; k++)
  {
    for (j = 0; j < r; j++)
    {
      beta_kj = ptrPlus(beta, k + j * q);
      innerLeftActionMatrix(group, beta_kj, mat);
      for (i = 0; i < s; i++)
      {
        alpha_ji = ptrPlus(alpha, j + i * r);
        gamma_ki = ptrPlus(gamma, k + i * q);
        zmaprow(alpha_ji, mat, nontips, tmp);
        zaddrow(gamma_ki, tmp);
      }
    }
  }
  return;
}

/*******************************************************************************
* void convertPermutationsToGapCode(char *infile, char *outfile)
{
  long this_line, max_per_line = 10;
  char *tail;
  long header[3], *line;
  long nontips, num, i, j;
  FILE *fin, *fout;
  fin = SFOpen(infile, FM_READ);
  fout = SFOpen(outfile, FM_CREATE);
  if (!fin || !fout) OtherError("convertPTC: opening files");
  if (zreadlong(fin, header, 3) != 3)
    OtherError("convertPTGC: reading header");
  ** val of header[0] always seems to be -1 : documented by Ringe? **
  nontips = header[1];
  num = header[2];
  line = (long *) malloc(nontips << LONGSH);
  if (!line) AllocationError("convertPTGC");
  fprintf(fout, "pl := List([[");
  for (i = 0; i < num; i++)
  {
    if (zreadlong(fin, line, nontips) != nontips)
      OtherError("convertPTGC: reading body");
    this_line = 0;
    for (j = 0; j < nontips; j++)
    {
      if (++this_line >= max_per_line)
      {
        this_line = 0;
        tail = ",\n";
      }
      else tail = ", ";
      if (j >= nontips - 1) tail = "]";
      fprintf(fout, "%d%s", line[j], tail);
    }
    fprintf(fout, (i < num - 1) ? ",\n [" : "],\n");
  }
  fprintf(fout, "PermList);\n");
  fclose(fin); fclose(fout); free(line);
  return;
}
*/

/******************************************************************************/
void convertPermutationsToAsci(char *infile, char *outfile)
{
  long header[3], *line;
  long nontips, num, i, j;
  FILE *fin, *fout;
  fin = SFOpen(infile, FM_READ);
  fout = SFOpen(outfile, FM_CREATE);
  if (!fin || !fout) OtherError("convertPTC: opening files");
  if (zreadlong(fin, header, 3) != 3)
    OtherError("convertPTGC: reading header");
  /* val of header[0] always seems to be -1 : documented by Ringe? */
  nontips = header[1];
  num = header[2];
  line = (long *) malloc(nontips << LONGSH);
  if (!line) AllocationError("convertPTGC");
  fprintf(fout, "%ld\n%ld\n", num, nontips);
  for (i = 0; i < num; i++)
  {
    if (zreadlong(fin, line, nontips) != nontips)
      OtherError("convertPTGC: reading body");
    for (j = 0; j < nontips; j++)
      fprintf(fout, "%ld\n", line[j]);
  }
  fclose(fin); fclose(fout); free(line);
  return;
}

/******************************************************************************/
void loadGeneralRegularActionMatrices(group_t *group, matrix_t **action,
  char *name, long num)
{
  long buffer[3], nontips = group->nontips;
  PTR ptr;
  FEL F_MINUS = zsub(F_ZERO, F_ONE);
  long i,j;
  FILE *fp;
  fp = SFOpen(name, FM_READ);
  if (!fp) OtherError("loadGRAM: opening file");
  if (zreadlong(fp, buffer, 3) != 3)
    OtherError("loadGRAM: reading header");
  if (buffer[1] != nontips || buffer[2] != num)
    OtherError("loadGRAM: incompatible file header");
  for (i = 0; i < num; i++)
  {
    ptr = action[i]->d;
    for (j = 1; j <= nontips; j++, zsteprow(&ptr))
      zinsert(ptr, j, F_MINUS);
  }
  for (i = 0; i < num; i++)
  {
    ptr = action[i]->d;
    for (j = 1; j <= nontips; j++, zsteprow(&ptr))
    {
      if (zreadlong(fp,buffer,1) != 1) OtherError("loadGRAM: reading body");
      zinsert(ptr, buffer[0], (buffer[0] == j) ? F_ZERO : F_ONE);
    }
  }
  fclose(fp);
  return;
}

/******************************************************************************/
void loadRegularActionMatrices(group_t *group)
{
  char regname[MAXLINE];
  strext(regname, group->stem, ".reg");
  group->action = allocateActionMatrices(group);
  loadGeneralRegularActionMatrices(group, group->action, regname,
    group->arrows);
  return;
}

/******************************************************************************/
void makeBasisChangeMatrices(group_t *group)
/* Assumes group->action matrices currently wrt basis of group elements */
{
  register long i;
  matrix_t **bch = allocateMatrixList(group, 2);
  matrix_t *bw = bch[0], *wb;
  matrix_t **action = group->action;
  long nontips = group->nontips;
  PTR src, dest;
  path_t *p;
  zinsert(bw->d, 1, F_ONE);
  for (i = 1; i < nontips; i++)
  {
    p = group->root + i;
    dest = ptrPlus(bw->d, i);
    src = ptrPlus(bw->d, p->parent->index);
    zmaprow(src, action[p->lastArrow]->d, nontips, dest);
  }
  wb = matinv(bw);
  if (!wb) OtherError("makeBasisChangeMatrix: inverting bw");
  memcpy(bch[1]->d, wb->d, zsize(nontips));
  matfree(wb);
  group->bch = bch;
  return;
}

/******************************************************************************/
void readRegFileHeader(group_t *group)
{
  long buffer;
  char regname[MAXLINE];
  FILE *fp;
  strext(regname, group->stem, ".reg");
  fp = SFOpen(regname, FM_READ);
  if (!fp) OtherError("readRegFileHeader: opening .reg file");
  zreadlong(fp, &buffer, 1);
  zreadlong(fp, &buffer, 1); group->nontips = buffer;
  zreadlong(fp, &buffer, 1); group->arrows = buffer;
  fclose(fp);
  return;
}

/******************************************************************************/
void makeLeftActionMatrices(group_t *group)
{
  matrix_t **laction = allocateActionMatrices(group);
  long a;
  path_t *p;
  PTR vec = zalloc(1);
  if (!vec) AllocationError("makeLeftActionMatrices");
  for (a = 0; a < group->arrows; a++)
  {
    zmulrow(vec, F_ZERO);
    p = group->root->child[a];
    zinsert(vec, 1 + p->index, F_ONE); /* Should work with Jennings order too */
    innerLeftActionMatrix(group, vec, laction[a]->d);
  }
  group->laction = laction;
  return;
}

/*********** pmatrix.c partly merged in here **********************************/

void innerRightProduct(const matrix_t *dest, const matrix_t *src, PTR scratch)
/* Assembles dest * src at scratch. */
/* src should be square, scratch should point to enough space. */
{
  register long i;
  PTR this_dest = dest->d;
  PTR this_scratch = scratch;
  if (src->fl != dest->fl || src->nor != dest->noc || src->nor != src->noc)
    OtherError("innerRightProduct: matrices incompatible");
  zsetlen(src->noc);
  for (i = dest->nor; i != 0; --i)
  {
    zmaprow(this_dest,src->d,src->nor,this_scratch);
    zsteprow(&this_scratch);
    zsteprow(&this_dest);
  }
  return;
}

static matrix_t *innerRightAction(matrix_t *dest, const matrix_t *src,
  PTR scratch)
/* Guaranteed not to alter dest->d */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  innerRightProduct(dest,src,scratch);
  memcpy(dest->d, scratch, zsize(dest->nor));
  return dest;
}

static matrix_t *innerLeftAction(const matrix_t *src, matrix_t *dest,
  PTR scratch)
/* Guaranteed not to alter dest->d */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  register long i;
  PTR this_src = src->d;
  PTR this_scratch = scratch;
  if (src->fl != dest->fl || src->noc != dest->nor || src->nor != src->noc)
  {
    MTXFAIL(ERR_INCOMPAT,NULL);
  }
  zsetlen(dest->noc);
  for (i = dest->nor; i != 0; --i)
  {
    zmaprow(this_src,dest->d,dest->nor,this_scratch);
    zsteprow(&this_scratch);
    zsteprow(&this_src);
  }
  memcpy(dest->d, scratch, zsize(dest->nor));
  return dest;
}

/******************************************************************************/
void innerBasisChangeNontips2Reg(group_t *group, matrix_t **matlist,
  long num, PTR workspace)
  /* Alters matrices in matlist */
  /* workspace points to group->nontips rows scratch space */
{
  register long i;
  matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    innerLeftAction(wb, matlist[i], workspace);
    innerRightAction(matlist[i], bw, workspace);
  }
  return;
}

/******************************************************************************/
void innerBasisChangeReg2Nontips(group_t *group, matrix_t **matlist,
  long num, PTR workspace)
/* Alters matrices in matlist */
/* workspace points to group->nontips rows scratch space */
{
  register long i;
  matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    innerLeftAction(bw, matlist[i], workspace);
    innerRightAction(matlist[i], wb, workspace);
  }
  return;
}

/******************************************************************************/
void basisChangeReg2Nontips(group_t *group, matrix_t **matlist, long num)
/* Alters matrices in matlist */
{
  PTR workspace = zalloc(group->nontips);
  if (!workspace) AllocationError("basisChangeReg2Nontips");
  innerBasisChangeReg2Nontips(group, matlist, num, workspace);
  free(workspace);
  return;
}

/******************************************************************************/
void changeActionMatricesReg2Nontips(group_t *group)
{
  PTR workspace;
  workspace = zalloc(group->nontips);
  if (!workspace) AllocationError("changeActionMatricesReg2Nontips: workspace");  innerBasisChangeReg2Nontips(group, group->action, group->arrows, workspace);
  free(workspace);
  return;
}

/******************************************************************************/
long pathTreeGirth(group_t *group)
{
  long d, girth = 0;
  for (d = 0; group->dS[d] < group->nontips; d++)
    if (group->dS[d+1] - group->dS[d] > girth)
      girth = group->dS[d+1] - group->dS[d];
  return girth;
}

/******************************************************************************/
void calculateDimSteps(group_t *group)
/* Assumes we are working with RLL, but that the nontips
 * are arranged in ascending length-lex order. */
{
  long depth, i;
  long *dS; 
  switch(group->ordering)
  {
  case 'R' :
    dS = (long *) malloc((group->maxlength + 3) << LONGSH);
    if (!dS) AllocationError("calculateDimSteps");
    dS[0] = 0;
    dS[1] = 1;
    i = 1;
    for (depth = 2; depth <= group->maxlength; depth++)
    {
      while (strlen(group->root[i].path) < depth) i++;
      if (strlen(group->root[i].path) != depth)
        OtherError("Theoretical Error: calculateDimSteps");
      dS[depth] = i;
    }
    dS[group->maxlength+1] = group->nontips;
    dS[group->maxlength+2] = group->nontips;
    group->dS = dS;
    break;
  case 'J' :
    dS = (long *) malloc((group->nontips + 2) << LONGSH);
    if (!dS) AllocationError("calculateDimSteps");
    dS[0] = 0;
    dS[1] = 1;
    for (i = 1, depth = 1; i < group->nontips; i++)
      if (depth < group->root[i].dim)
      {
        if (group->root[i].dim != ++depth)
          OtherError("Theoretical Error: calculateDimSteps");
        dS[depth] = i;
      }
    dS[depth+1] = group->nontips;
    i = 1;
    group->dS = (long *) malloc((depth + 2) << LONGSH);
    if (!group->dS) AllocationError("calculateDimSteps");
    memcpy(group->dS, dS, (depth + 2) << LONGSH);
    free(dS);
    /* printf("Dim steps:\n"); */
    /* for (i=0; i <= depth+1; i++) printf("%d\n", group->dS[i]); */
    break;
  default:
    OtherError("calculateDimSteps: not implemented for this ordering");
    break;
  }
  pathTreeGirth(group);
  return;
}

/******************************************************************************/
group_t *fullyLoadedGroupRecord(char *stem)
{
  group_t *G = namedGroupRecord(stem);
  loadNonTips(G);
  if (G->ordering == 'L')
    OtherError("fullyLoadedGroupRecord: can't cope with LL ordering");
  if (G->ordering == 'J') loadDimensions(G);
  buildPathTree(G);
  buildLeftPathTree(G);
  markPathDimensions(G);
  loadActionMatrices(G);
  loadLeftActionMatrices(G);
  calculateDimSteps(G);
  return G;
}

/******************************************************************************/
inline boolean mateq(matrix_t *mat1, matrix_t *mat2)
{
  register long i;
  PTR row1, row2;
  if (mat1->fl != mat2->fl) return false;
  if (mat1->nor != mat2->nor) return false;
  if (mat1->noc != mat2->noc) return false;
  zsetfield(mat1->fl);
  zsetlen(mat1->noc);
  row1 = mat1->d;
  row2 = mat2->d;
  for (i = mat1->nor; i > 0; --i, zsteprow(&row1), zsteprow(&row2))
    if (zcmprow(row1,row2)) return false;
  return true;
}

/******************************************************************************/
static boolean matricesCommute(matrix_t *a, matrix_t *b, matrix_t *ab,
  matrix_t *ba)
{
  innerRightProduct(a, b, ab->d);
  innerRightProduct(b, a, ba->d);
  return (mateq(ab,ba)) ? true : false;
}

/******************************************************************************/
int verifyGroupIsAbelian(group_t *A)
{
  long Asize = A->nontips;
  long ngens = A->arrows;
  long fl = A->action[0]->fl;
  long i, j;
  boolean thisPairCommutes;
  matrix_t *ab = matalloc(fl, Asize, Asize);
  matrix_t *ba = matalloc(fl, Asize, Asize);
  if (!ab || !ba) AllocationError("verifyGroupIsAbelian");
  for (i = 0; i < ngens; i++)
    for (j = i+1; j < ngens; j++)
    {
      thisPairCommutes = matricesCommute(A->action[i], A->action[j], ab, ba);
      if (!thisPairCommutes) return 0;
	/*      {
	 *char invalid[MAXLINE];
         *sprintf(invalid,
         * "verifyGroupIsAbelian for %s: gens %ld and %ld do not commute",
         * A->stem, i, j);
	 *OtherError(invalid);
	}*/
    }
  return 1;
}

/******************************************************************************/
long *newLongArray(long N)
/* Array entries initialized to 0 */
{
  long *l, i;
  if (N <= 0) OtherError("newLongArray: invalid input");
  l = (long *) malloc(N << LONGSH);
  if (!l) AllocationError("newLongArray");
  for (i = 0; i < N; i++) l[i] = 0;
  return l;
}

/******************************************************************************/
matrix_t *myMatalloc(long fl, long nor, long noc)
/* Can handle nor==0 */
{
  long nor1;
  matrix_t *mat;
  nor1 = (nor == 0) ? 1 : nor;
  mat = matalloc(fl, nor1, noc);
  if (!mat) AllocationError("myMatalloc");
  if (nor == 0)
  {
    free(mat->d);
    mat->d = NULL;
    mat->nor = 0;
  }
  return mat;
}

/******************************************************************************/
matrix_t *myMatmul(matrix_t *dest, matrix_t *src)
/* Can handle dest->nor==0; znoc is src->noc at end */
{
  if (src->fl != dest->fl || src->nor != dest->noc)
    OtherError("myMatmul: incompatible matrices");
  zsetfield(src->fl);
  if (dest->nor == 0)
  {
    if (dest->d)
    {
      free (dest->d);
      dest->d = NULL;
    }
    dest->noc = src->noc;
  }
  else
    matmul(dest, src);
  zsetlen(src->noc);
  return dest;
}

/******************************************************************************/
long *collected(long *l)
/* l[0] is length */
{
  long len, *col, pos;
  len = l[0];
  col = (long *) malloc((len+1) << LONGSH);
  if (!col) AllocationError("collected");
  if (len == 0)
  {
    pos = 0;
  }
  else
  {
    boolean unfinished;
    col[1] = listFun(l+1, len, minlong);
    pos = 1;
    unfinished = true;
    while (unfinished)
    {
      long i, this = 0;
      boolean found = false;
      for (i = 1; i <= len; i++)
      if (l[i] > col[pos])
      {
        if (found)
        {
          if (l[i] < this) this = l[i];
        }
        else
        {
          found = true;
          this = l[i];
        }
      }
      if (found)
        col[++pos] = this;
      else
        unfinished = false;
    }
  }
  col[0] = pos;
  return col;
}

/******************************************************************************/
long listPos(long *l, long n)
{
  long i;
  for (i = 1; i <= l[0]; i++)
    if (l[i] == n) return i;
  return -1;
}

/*****************************************************************************
   pgroup.c : routines for group algebras, common to most programs

       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>
       Copyright (C) 2015 Simon A. King <simon.king@uni-jena.de>

    This file is part of p_group_cohomology.

    p_group_cohomoloy is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 2 of the License, or
    (at your option) any later version.

    p_group_cohomoloy is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.
*****************************************************************************/

#include "pgroup.h"
#include "pgroup_decls.h"
#include <unistd.h>

MTX_DEFINE_FILE_INFO

/***
 * The following value has to be put into the ...->Magic field of a matrix
 * in order to be recognised as a matrix by MatIsValid
 ***/

#define MAT_MAGIC 0x6233af91

typedef unsigned char BYTE;

/***
 * NULL on error
 *
 * In contrast to strdup, it calls MtxError
 ****************************************************************************/
char *mtx_strdup(const char *src)
{
  char *dest = (char *) malloc((strlen(src)+1) * sizeof(char));
  if (!dest)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
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

/*****************************************************************************/
inline boolean fileExists(const char *name)
{
  int stat = access(name, F_OK);
  return (stat == 0) ? true : false;
}

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

/****
 * NULL on error
 ***************************************************************************/
group_t *newGroupRecord (void)
{
  group_t *group = (group_t *) malloc(sizeof(group_t));
  if (!group)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
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

/****
 * NULL on error
 ***************************************************************************/
inline group_t *namedGroupRecord (const char *stem)
{
  group_t *group = newGroupRecord();
  if (!group) return NULL;
  if ((group->stem = mtx_strdup(stem)) == NULL)
  { freeGroupRecord(group);
    return NULL;
  }
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

/******************************************************************************/
static inline char NextSignificantCharacter(FILE *fp)
{
  char c;
  while ((c = fgetc(fp)) != EOF && IsWhitespace(c));
  return c;
}

/****
 * Change fp to NULL pointer on error, close the file, and return -1
 ***************************************************************************/
static long GetNextLong(FILE **fp, char *buffer)
{
  char c, *this;
  long i;
  this = buffer; i = 0;
  for (this = buffer, i = 0, c = NextSignificantCharacter(*fp);
       ;
       this++, i++, c = fgetc(*fp))
  {
    if (c == EOF)
    { MTX_ERROR1("unexpected EOF: %E", MTX_ERR_FILEFMT);
      fclose(*fp);
      *fp = NULL;
      return -1;
    }
    else if (i == MAXLINE)
    { MTX_ERROR1("Buffer Overflow: %E", MTX_ERR_RANGE);
      fclose(*fp);
      *fp = NULL;
      return -1;
    }
    else if (IsDigit(c))
      *this = c;
    else
      break;
  }
  *this = '\0';
  return atoi(buffer);
}

/****
 * Change fp to NULL pointer on error, close the file, and return ' '
 ***************************************************************************/
static inline char GetNextChar(FILE **fp)
{
  char c = NextSignificantCharacter(*fp);
  if (c == EOF)
    { MTX_ERROR1("unexpected EOF: %E", MTX_ERR_FILEFMT);
      fclose(*fp);
      *fp = NULL;
      return ' ';
    }
  return c;
}

/******************************************************************************/

#if !defined(IsArrow)
#define IsArrow(c,arrows) ((c) >= 'a' && c < 'a' + (arrows))
#endif


/****
 * Change fp to NULL pointer on error, close the file, and return ' '
 ***************************************************************************/
static char GetNextPath(FILE **fp, char *dest, long maxlength, long arrows)
/* Returns character immediately following path */
{
  char c, *this;
  long i;
  this = dest; i = 0;
  for (this = dest, i = 0, c = NextSignificantCharacter(*fp);
       ;
       this++, i++, c = fgetc(*fp))
  {
    if (c == EOF)
    { MTX_ERROR1("unexpected EOF: %E", MTX_ERR_FILEFMT);
      fclose(*fp);
      *fp = NULL;
      return ' ';
    }
    else if (IsArrow(c,arrows))
      *this = c;
    else if (c == '(')
    {
      *(this++) = c;
      if (!IsDigit(c = NextSignificantCharacter(*fp)))
        { MTX_ERROR1("invalid vertex: %E", MTX_ERR_FILEFMT);
          fclose(*fp);
          *fp = NULL;
          return ' ';
        }
      *(this++) = c;
      if ((c = NextSignificantCharacter(*fp)) != ')')
        { MTX_ERROR1("invalid vertex path format: %E", MTX_ERR_FILEFMT);
          fclose(*fp);
          *fp = NULL;
          return ' ';
        }
      *(this++) = c;
      c = NextSignificantCharacter(*fp);
      break;
    }
    else
      break;
    if (i == maxlength)
    { MTX_ERROR1("buffer overflow: %E", MTX_ERR_NOMEM);
      fclose(*fp);
      *fp = NULL;
      return ' ';
    }
  }
  *this = '\0';
  return c;
}

/****
 * 1 on error
 ***************************************************************************/
int loadDimensions(group_t *group)
{
  long dims, *dim;
  long i;
  char buffer[MAXLINE], dimfile[MAXLINE];
  FILE *fp;
  strext(dimfile, group->stem, ".dims");
  fp = fopen(dimfile, "r");
  if (!fp)
  {
      MTX_ERROR1("Cannot open file %s", dimfile);
      return 1;
  }
  dims = GetNextLong(&fp, buffer);
  if (!fp) return 1;
  dim = (long *) malloc((dims+1) * sizeof(long));
  if (!dim)
  { fclose(fp);
    MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return 1;
  }
  dim[0] = dims;
  for (i = 1; i <= dims; i++)
  {  dim[i] = GetNextLong(&fp, buffer);
      if (!fp)
      {
          free(dim);
          return 1;
      }
  }
  fclose(fp);
  group->dim = dim;
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int readHeader(group_t *group)
{
  char nonTipsFile[MAXLINE];
  FILE *fp;
  char *buffer;
  strext(nonTipsFile, group->stem, ".nontips");
  buffer = malloc((MAXLINE + 1) * sizeof(char));
  if (!buffer)
  {
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
  }
  fp = fopen(nonTipsFile,"r");
  if (!fp)
  {
      free(buffer);
      MTX_ERROR1("%E", MTX_ERR_FILEFMT);
      return 1;
  }
  group->arrows = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  group->nontips = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  group->maxlength = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  group->mintips = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  group->p = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  free(buffer);
  group->ordering = GetNextChar(&fp);
  if (!fp)
  {
      return 1;
  }
  fclose(fp);
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int loadNonTips(group_t *group)
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
  {
    MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return 1;
  }
  fp = fopen(nonTipsFile,"r");
  if (!fp)
  {
      free(buffer);
      MTX_ERROR1("%E", MTX_ERR_FILEFMT);
      return 1;
  }
  group->arrows = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  nontips = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  group->nontips = nontips;
  maxlength = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  stringMaxlength = (maxlength >= 3) ? maxlength : 3;
  group->maxlength = maxlength;
  group->mintips = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  group->p = GetNextLong(&fp,buffer);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  group->ordering = GetNextChar(&fp);
  if (!fp)
  {
      free(buffer);
      return 1;
  }
  FfSetField(group->p);
  FfSetNoc(nontips);
  //  nontip = (char **) malloc(nontips * sizeof(char *));
  nontip = (char **) malloc(nontips * sizeof(void*));
  if (!nontip)
  {
      free(buffer);
      fclose(fp);
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
  }
  *nontip = (char *) malloc((stringMaxlength+1) * nontips
                              * sizeof(char));
  if (!*nontip)
  {
      fclose(fp);
      free(buffer);
      free(nontip);
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
  }
  for (i = 1; i < nontips; i++)
    nontip[i] = nontip[0] + i * (stringMaxlength + 1);
  for (i = 0; i < nontips; i++)
  {
    c = GetNextPath(&fp,nontip[i], stringMaxlength, group->arrows);
    if (!fp)
    {
      free(buffer);
      free(nontip);
      free(*nontip);
      return 1;
    }
    /* c is the character immediately following the path; should be ';' */
    if (c != ';')
    {
      free(buffer);
      free(nontip);
      free(*nontip);
      fclose(fp);
      MTX_ERROR1("%E", MTX_ERR_FILEFMT);
      return 1;
    }
  }
  fclose(fp);
  free(buffer);
  group->nontip = nontip;
  return 0;
}

/****
 * NULL on error
 ***************************************************************************/
path_t *allocatePathTree(group_t *group)
{
  path_t *root;
  long arrows = group->arrows;
  long nontips = group->nontips;
  register long i;
  path_t **kinder;
  root = (path_t *) malloc(nontips * sizeof(path_t));
  if (!root)
  {
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return NULL;
  }
  //  kinder = (path_t **) malloc(nontips * arrows * sizeof(path_t *));
  kinder = (path_t **) malloc(nontips * arrows * sizeof(void*));
  if (!kinder)
  {
      free(root);
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return NULL;
  }
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

/*****
 * 1 on error
 **************************************************************************/
int buildPathTree(group_t *group)
{
  path_t *root;
  register long i,j;
  path_t *this, *parent;
  char arrow;
  root = allocatePathTree(group);
  if (!root) return 1;
  for (i = 1; i < group->nontips; i++)
  {
    this = root + i; parent = root;
    this->path = group->nontip[i];
    for (j = 0, arrow = this->path[0]; this->path[j+1] != '\0'; j++)
    {
      parent = parent->child[arrow - 'a'];
      if (!parent)
      { freeRoot(root);
        MTX_ERROR("theoretical error");
        return 1;
      }
      arrow = this->path[j+1];
    }
    parent->child[arrow - 'a'] = this;
    this->depth = parent->depth + 1;
    this->parent = parent;
    this->lastArrow = arrow - 'a';
  }
  group->root = root;
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int buildLeftPathTree(group_t *group)
{
  path_t *lroot;
  register long i,j;
  path_t *this, *parent;
  char arrow;
  lroot = allocatePathTree(group);
  if (!lroot) return 1;
  for (i = 1; i < group->nontips; i++)
  {
    this = lroot + i; parent = lroot;
    this->path = group->nontip[i];
    /* for (j = 1; this->path[j] != '\0'; j++) */
    for (j = strlen(this->path) - 1; j > 0; j--)
    {
      arrow = this->path[j];
      parent = parent->child[arrow - 'a'];
      if (!parent)
      { freeRoot(lroot);
        MTX_ERROR("theoretical error");
        return 1;
      }
    }
    arrow = this->path[0];
    parent->child[arrow - 'a'] = this;
    this->depth = parent->depth + 1;
    this->parent = parent;
    this->lastArrow = arrow - 'a';
  }
  group->lroot = lroot;
  return 0;
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

/****
 * NULL on error
 ***************************************************************************/
Matrix_t **loadMatrixList(group_t *group, char *name, long num)
{
  Matrix_t *bigmat;
  Matrix_t **action;
  long nontips = group->nontips;
  long i;
  bigmat = MatLoad(name); /* sets FfOrder, FfNoc to required values */
  if (!bigmat) return NULL;
  if (bigmat->Noc != nontips)
    { MatFree(bigmat);
      MTX_ERROR1("noc != nontips: %E", MTX_ERR_INCOMPAT);
      return NULL;
    }
  if (bigmat->Nor != num * nontips)
    { MatFree(bigmat);
      MTX_ERROR1("nor ! num * nontips: %E", MTX_ERR_INCOMPAT);
      return NULL;
    }
  if (group->p != FfChar)
    { MatFree(bigmat);
      MTX_ERROR1("matrices over wrong characteristic field: %E", MTX_ERR_INCOMPAT);
      return NULL;
    }
  action = (Matrix_t **) malloc (num * sizeof(void*));
  if (!action)
  {
      MatFree(bigmat);
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return NULL;
  }
  Matrix_t *tmp;
  size_t chunksize = FfCurrentRowSize*nontips;
  for (i = 0; i < num; i++)
  {
      tmp = MatAlloc(bigmat->Field, nontips, bigmat->Noc);
      if (!tmp)
      { MatFree(bigmat);
        MTX_ERROR1("%E", MTX_ERR_NOMEM);
        return NULL;
      }
      memcpy(tmp->Data, MatGetPtr(bigmat, i*nontips), chunksize);
      action[i] = tmp;
  }
  MatFree(bigmat);
  return action;
}

/****
 * 1 on error
 ***************************************************************************/
inline int loadActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".gens");
  group->action = loadMatrixList(group, name, group->arrows);
  if (!group->action) return 1;
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
inline int loadLeftActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".lgens");
  group->laction = loadMatrixList(group, name, group->arrows);
  if (!group->laction) return 1;
  return 0;
}

/***
 * 1 on error
 ****************************************************************************/
int loadBasisChangeMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".bch");
  group->bch = loadMatrixList(group, name, 2);
  if (!group->bch) return 1;
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int saveMatrixList(group_t *group, Matrix_t **action, long num, char *name)
{
  Matrix_t mat;
  mat.Field = group->p;
  mat.Noc = group->nontips;
  mat.Nor = group->nontips * num;
  mat.Data = action[0]->Data;
  mat.Magic = MAT_MAGIC;
  if (MatSave(&mat,name) != 0)
  {
      MTX_ERROR1("%E", MTX_ERR_FILEFMT);
      return 1;
  }
  return 0;
}

/***
 * 1 on error
 ****************************************************************************/
int saveActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".gens");
  if (saveMatrixList(group, group->action, group->arrows, name)) return 1;
  /*gzip(name);*/
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int saveLeftActionMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".lgens");
  if (saveMatrixList(group, group->laction, group->arrows, name)) return 1;
  /*gzip(name);*/
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int saveBasisChangeMatrices(group_t *group)
{
  char name[MAXLINE];
  strext(name, group->stem, ".bch");
  if (saveMatrixList(group, group->bch, 2, name)) return 1;
  /*gzip(name);*/
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int saveBasisChangeMatrix(group_t *group, Matrix_t *bw)
{
  char name[MAXLINE];
  strext(name, group->stem, ".bch");
  if (MatSave(bw,name) != 0)
  {
      MTX_ERROR1("%E", MTX_ERR_FILEFMT);
      return 1;
  }
  return 0;
}

/****
 * NULL on error
 ***************************************************************************/
Matrix_t **allocateMatrixList(group_t *group, long num)
{
  long nontips = group->nontips;
  PTR ptr, tmp;
  Matrix_t *mat, **action;
  register long i;
  FfSetNoc(nontips);
  ptr = FfAlloc(num * nontips);
  if (!ptr)
  {
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return NULL;
  }
  mat = (Matrix_t *) malloc(num * sizeof(Matrix_t));
  if (!mat)
  {
      free(ptr);
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return NULL;
  }
  action = (Matrix_t **) malloc(num * sizeof(Matrix_t *));
  if (!action)
  {
      free(mat);
      free(ptr);
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return NULL;
  }
  for (i = 0, tmp = ptr; i < num; i++, tmp=FfGetPtr(tmp,nontips))
  {
    action[i] = mat + i;
    action[i]->Field = FfOrder;
    action[i]->Nor = nontips;
    action[i]->Noc = nontips;
    action[i]->Data = tmp;
    action[i]->PivotTable = NULL;
    action[i]->RowSize = FfCurrentRowSize;
    action[i]->Magic = MAT_MAGIC;
  }
  return action;
}

/****
 * NULL on error
 ***************************************************************************/
inline Matrix_t **allocateActionMatrices(group_t *group)
{
  return allocateMatrixList(group, group->arrows);
}

/******************************************************************************/
inline void freeMatrixList(Matrix_t **mat)
{
  free(mat[0]->Data);
  free(mat[0]);
  free(mat);
}

/******************************************************************************/
inline void freeActionMatrices(Matrix_t **mat)
{
  free(mat[0]->Data);
  free(mat[0]);
  free(mat);
}

/******************************************************************************
 * The following is basically a copy of FfMapRow, deleting some assembly code.
 * Only difference: The @em result is not initialized to zero.
 ** Multiply the vector @em row by the matrix @em matrix from the right, and
 ** add the product to @em result.
 ** @attention @em result and @em row must not overlap. Otherwise the result is
 ** undefined.
 ** @param row The source vector (nor columns).
 ** @param matrix A matrix (nor by nor).
 ** @param nor Number of rows in the matrix. It must coincide with FfCurrentRowSizeIo*MPB.
 ** @param[out] result The resulting vector (nor columns).
*/
void FfAddMapRow(PTR row, PTR matrix, int nor, PTR result)
{
    register int i;
    register FEL f;
    BYTE *m = (BYTE *) matrix;
    register long *l = (long *)result;

    if (FfOrder == 2)       /* GF(2) is a special case */
    {
        register long *x1 = (long *) matrix;
        register BYTE *r = (BYTE *) row;

        for (i = nor; i > 0; ++r)
        {
            register BYTE mask;
            if (*r == 0)   /* Skip eight rows */
            {
            i -= 8;
            x1 += 8 * LPR;
            continue;
            }
            for (mask = 0x80; mask != 0 && i > 0; mask >>= 1, --i)
            {
                if ((mask & *r) == 0)
                {
                    x1 += LPR;  /* Skip that row */
                    continue;
                }
                register long *x2 = (long *)result;
                register int k;
                for (k = LPR; k; --k)
                    *x2++ ^= *x1++;
            }
        }
    }
    else                /* Any other field */
    {
        register BYTE *brow = (BYTE *) row;
        register int pos = 0;

        for (i = nor; i > 0; --i)
        {
            f = mtx_textract[pos][*brow];
            if (++pos == (int) MPB)
            {
                pos = 0;
                ++brow;
            }
            if (f != FF_ZERO)
            {
                register BYTE *v = m;
                register BYTE *r = result;
                register int k = FfCurrentRowSizeIo;
                if (f == FF_ONE)
                {
                    for (; k != 0; --k)
                    {
                        register BYTE x = *v++;
                        if (x!=0)
                            *r = mtx_tadd[*r][x];
                        ++r;
                    }
                }
                else
                {
                    register BYTE *multab = mtx_tmult[f];
                    for (; k != 0; --k)
                    {
                        if (*v != 0)
                            *r = mtx_tadd[multab[*v]][*r];
                        ++v;
                        ++r;
                    }
                }
            }
            m += FfCurrentRowSize;              /* next row */
        }
    }
}


/***************************************************************************/
static inline long maxlong(long n1, long n2)
{
  return (n1 >= n2) ? n1 : n2;
}


/******************************************************************************/
static inline long minlong(long n1, long n2)
{
  return (n1 <= n2) ? n1 : n2;
}

/******************************************************************************/
static inline long modifiedMinlong(long n1, long n2)
/* Allows for -1 being used to represent +infinity */
{
  if (n1 == -1) return n2;
  if (n2 == -1) return n1;
  return minlong(n1, n2);
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

/****
 * ' ' on error
 ***************************************************************************/
char arrowName(long a)
{
  static char arrowname[] = ARROWNAMES;
  if (a >= MAXARROW)
  {
      MTX_ERROR1("Need more arrow names: %E", MTX_ERR_RANGE);
      return ' ';
  }
  return arrowname[a];
}

/******************************************************************************/
long pathDimension(group_t *group, path_t *p)
{
  if (p->depth == 0)
    return 0;
  else
  {
    return pathDimension(group, p->parent) + group->dim[1+p->lastArrow];
  }
}

/****
 * 1 on error
 ***************************************************************************/
int markPathDimensions(group_t *group)
{
  long i;
  switch (group->ordering)
  {
  case 'R' :
    for (i=0; i < group->nontips; i++)
    {
      group->root[i].dim = group->root[i].depth;
    }
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
    MTX_ERROR("not implemented for this ordering");
    return 1;
  }
  return 0;
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
  register int i;
  PTR this = dest+FfCurrentRowSize;
  memcpy(dest, vec, FfCurrentRowSize);
  for (i = 1; i < group->nontips; i++, this+=FfCurrentRowSize)
  {
    FfMapRow(FfGetPtr(dest, group->lroot[i].parent->index), group->laction[group->lroot[i].lastArrow]->Data, group->nontips, this);
  }
  return;
}

/******************************************************************************/
void innerLeftActionMatrix(group_t *group, PTR vec, PTR dest)
{
  register int i;
  PTR this = dest + FfCurrentRowSize;
  memcpy(dest, vec, FfCurrentRowSize);
  for (i = 1; i < group->nontips; i++, this+=FfCurrentRowSize)
  {
    FfMapRow(FfGetPtr(dest, group->root[i].parent->index), group->action[group->root[i].lastArrow]->Data, group->nontips, this);
  }
  return;
}

/******************************************************************************/
inline Matrix_t *rightActionMatrix(group_t *group, PTR vec)
{
  Matrix_t *mat = MatAlloc(FfOrder, group->nontips, group->nontips);
  innerRightActionMatrix(group, vec, mat->Data);
  return mat;
}

/******************************************************************************/
inline Matrix_t *leftActionMatrix(group_t *group, PTR vec)
{
  Matrix_t *mat = MatAlloc(FfOrder, group->nontips, group->nontips);
  innerLeftActionMatrix(group, vec, mat->Data);
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
  PTR mat = scratch, tmp = FfGetPtr(scratch, nontips);
  alpha_ji = alpha;
  for (i = 0; i < s; i++)
  {
    beta_kj = beta;
    for (j = 0; j < r; j++, alpha_ji+=FfCurrentRowSize)
    {
      /*alpha_ji = FfGetPtr(alpha, j + i * r);*/
      innerRightActionMatrix(group, alpha_ji, mat);
      gamma_ki = FfGetPtr(gamma, i * q);
      for (k = 0; k < q; k++, beta_kj+=FfCurrentRowSize, gamma_ki+=FfCurrentRowSize)
      {
        /*beta_kj = FfGetPtr(beta, k + j * q);
        gamma_ki = FfGetPtr(gamma, k + i * q);*/
        FfAddMapRow(beta_kj, mat, nontips, gamma_ki);
      }
    }
  }
  return;
}

/******************************************************************************/
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
/*void innerLeftCompose(group_t *group, PTR alpha, PTR beta, long s, long r,
  long q, PTR scratch, PTR gamma)
{
  long nontips = group->nontips;
  long i,j,k;
  PTR alpha_ji, beta_kj, gamma_ki;
  PTR mat = scratch, tmp = FfGetPtr(scratch, nontips);
  for (k = 0; k < q; k++)
  {
    for (j = 0; j < r; j++)
    {
      beta_kj = FfGetPtr(beta, k + j * q);
      innerLeftActionMatrix(group, beta_kj, mat);
      for (i = 0; i < s; i++)
      {
        alpha_ji = FfGetPtr(alpha, j + i * r);
        gamma_ki = FfGetPtr(gamma, k + i * q);
        FfMapRow(alpha_ji, mat, nontips, tmp);
        FfAddRow(gamma_ki, tmp);
      }
    }
  }
  return;
}*/

/****
 * 1 on error
 ***************************************************************************/
int convertPermutationsToAsci(const char *infile, const char *outfile)
{
  long header[3], *line;
  long nontips, num, i, j;
  FILE *fin, *fout;
  fin = SysFopen(infile, FM_READ);
  if (!fin) return 1;
  fout = SysFopen(outfile, FM_CREATE);
  if (!fout)
  {
      fclose(fin);
      return 1;
  }
  if (SysReadLong(fin, header, 3) != 3)
  {
      fclose(fin);
      fclose(fout);
      MTX_ERROR1("reading header: %E", MTX_ERR_FILEFMT);
      return 1;
  }
  /* val of header[0] always seems to be -1 : documented by Ringe? */
  nontips = header[1];
  num = header[2];
  line = (long *) malloc(nontips * sizeof(long));
  if (!line)
  {
      fclose(fin);
      fclose(fout);
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
  }
  fprintf(fout, "%ld\n%ld\n", num, nontips);
  for (i = 0; i < num; i++)
  {
    if (SysReadLong(fin, line, nontips) != nontips)
    {
        free(line);
        fclose(fin);
        fclose(fout);
        MTX_ERROR1("reading body: %E", MTX_ERR_FILEFMT);
        return 1;
    }
    for (j = 0; j < nontips; j++)
      fprintf(fout, "%ld\n", line[j]);
  }
  fclose(fin); fclose(fout); free(line);
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int loadGeneralRegularActionMatrices(group_t *group, Matrix_t **action,
  char *name, long num)
{
  long buffer[3], nontips = group->nontips;
  PTR ptr;
  FEL F_MINUS = FfNeg(FF_ONE);
  long i,j;
  FILE *fp;
  fp = SysFopen(name, FM_READ);
  if (!fp) return 1;
  if (SysReadLong(fp, buffer, 3) != 3)
  {
      fclose(fp);
      MTX_ERROR1("reading header: %E", MTX_ERR_FILEFMT);
      return 1;
  }
  if (buffer[1] != nontips || buffer[2] != num)
  { fclose(fp);
    MTX_ERROR1("incompatible file header: %E", MTX_ERR_FILEFMT);
    return 1;
  }
  for (i = 0; i < num; i++)
  {
    ptr = action[i]->Data;
    for (j = 0; j < nontips; j++, FfStepPtr(&ptr))
      FfInsert(ptr, j, F_MINUS);
  }
  for (i = 0; i < num; i++)
  {
    ptr = action[i]->Data;
    for (j = 0; j < nontips; j++, FfStepPtr(&ptr))
    {
      if (SysReadLong(fp,buffer,1) != 1)
      { fclose(fp);
        MTX_ERROR1("reading body: %E", MTX_ERR_FILEFMT);
        return 1;
      }
      /* For backwards compatibility, we have a shift by one when reading
       * or saving the action matrices
       */
      FfInsert(ptr, buffer[0]-1, (buffer[0]-1 == j) ? FF_ZERO : FF_ONE);
    }
  }
  fclose(fp);
  return 0;
}

/***
 * 1 on error
 ****************************************************************************/
int loadRegularActionMatrices(group_t *group)
{
  char regname[MAXLINE];
  strext(regname, group->stem, ".reg");
  group->action = allocateActionMatrices(group);
  if (!group->action) return 1;
  return loadGeneralRegularActionMatrices(group, group->action, regname,
    group->arrows);
}

/****
 * 1 on error
 ***************************************************************************/
int makeBasisChangeMatrices(group_t *group)
/* Assumes group->action matrices currently wrt basis of group elements */
{
  register long i;
  Matrix_t **bch = allocateMatrixList(group, 2);
  if (!bch) return 1;
  Matrix_t *bw = bch[0], *wb;
  Matrix_t **action = group->action;
  long nontips = group->nontips;
  PTR src, dest;
  path_t *p;
  FfInsert(bw->Data, 0, FF_ONE);
  for (i = 1; i < nontips; i++)
  {
    p = group->root + i;
    dest = FfGetPtr(bw->Data, i);
    src = FfGetPtr(bw->Data, p->parent->index);
    FfMapRow(src, action[p->lastArrow]->Data, nontips, dest);
  }
  wb = MatInverse(bw);
  if (!wb)
  { freeMatrixList(bch);
    return 1;
  }
  memcpy(bch[1]->Data, wb->Data, (FfCurrentRowSize*nontips));
  MatFree(wb);
  group->bch = bch;
  return 0;
}

/***
 * 1 on error
 ****************************************************************************/
int readRegFileHeader(group_t *group)
{
  long buffer;
  char regname[MAXLINE];
  FILE *fp;
  strext(regname, group->stem, ".reg");
  fp = SysFopen(regname, FM_READ);
  if (!fp) return 1;
  SysReadLong(fp, &buffer, 1);
  SysReadLong(fp, &buffer, 1); group->nontips = buffer;
  SysReadLong(fp, &buffer, 1); group->arrows = buffer;
  fclose(fp);
  return 0;
}

/***
 * 1 on error
 ****************************************************************************/
int makeLeftActionMatrices(group_t *group)
{
  Matrix_t **laction = allocateActionMatrices(group);
  if (!laction) return 1;
  long a;
  path_t *p;
  PTR vec = FfAlloc(1);
  if (!vec)
  {
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
  }
  for (a = 0; a < group->arrows; a++)
  {
    /*FfMulRow(vec, FF_ZERO);*/
    memset(vec, 0, FfCurrentRowSize);
    p = group->root->child[a];
    FfInsert(vec, p->index, FF_ONE); /* Should work with Jennings order too */
    innerLeftActionMatrix(group, vec, laction[a]->Data);
  }
  group->laction = laction;
  free(vec);
  return 0;
}

/**
 * 1 on error
 *******************************/
int innerRightProduct(const Matrix_t *dest, const Matrix_t *src, PTR scratch)
/* Assembles dest*src at scratch.
 * src should be square, scratch should point to enough space,
 * which is not required to be empty. */
{
  Matrix_t Res;
  FfSetField(src->Field);
  FfSetNoc(src->Noc);
  memset(scratch, 0, dest->Nor*FfCurrentRowSize);
  Res.Magic = dest->Magic;
  Res.Field = dest->Field;
  Res.Nor = dest->Nor;
  Res.Noc = src->Noc;
  Res.PivotTable = NULL;
  Res.Data = scratch;
  Res.RowSize = FfCurrentRowSize;
  if (!MatMulStrassen(&Res, dest, src)) { return 1; }
  FfSetNoc(src->Noc);
  return 0;
}

/**
 * NULL on error
 ******/
Matrix_t *innerRightAction(Matrix_t *dest, const Matrix_t *src, PTR scratch)
/* Guaranteed not to alter dest->Data */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  if (innerRightProduct(dest,src,scratch)) return NULL;
  memcpy(dest->Data, scratch, (FfCurrentRowSize*dest->Nor));
  return dest;
}

/**
 * NULL on error
 ****/
Matrix_t *innerLeftAction(const Matrix_t *src, Matrix_t *dest, PTR scratch)
/* Guaranteed not to alter src->Data */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  if (src->Field != dest->Field || src->Noc != dest->Nor || src->Nor != src->Noc)
  {
    MTX_ERROR1("%E", MTX_ERR_INCOMPAT);
    return NULL;
  }
  FfSetNoc(dest->Noc);
  memset(scratch, 0, FfCurrentRowSize*dest->Nor);
  Matrix_t Res;
  Res.Magic = dest->Magic;
  Res.Field = dest->Field;
  Res.Nor = dest->Nor;
  Res.Noc = src->Noc;
  Res.PivotTable = NULL;
  Res.Data = scratch;
  Res.RowSize = FfCurrentRowSize;
  if (!MatMulStrassen(&Res, src, dest)) { return NULL; }
  /*
  register long i;
  PTR this_src = src->Data;
  PTR this_scratch = scratch;
  for (i = dest->Nor; i != 0; --i)
  {
    FfMapRow(this_src,dest->Data,dest->Nor,this_scratch);
    FfStepPtr(&this_scratch);
    FfStepPtr(&this_src);
  }*/
  FfSetNoc(Res.Noc);
  memcpy(dest->Data, scratch, (FfCurrentRowSize*dest->Nor));
  return dest;
}

/****
 * 1 on error
 ***************************************************************************/
int innerBasisChangeNontips2Reg(group_t *group, Matrix_t **matlist,
  long num, PTR workspace)
  /* Alters matrices in matlist */
  /* workspace points to group->nontips rows scratch space */
{
  register long i;
  Matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    if (!innerLeftAction(wb, matlist[i], workspace)) return 1;
    if (!innerRightAction(matlist[i], bw, workspace)) return 1;
  }
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int innerBasisChangeReg2Nontips(group_t *group, Matrix_t **matlist,
  long num, PTR workspace)
/* Alters matrices in matlist */
/* workspace points to group->nontips rows scratch space */
{
  register long i;
  Matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    if (!innerLeftAction(bw, matlist[i], workspace)) return 1;
    if (!innerRightAction(matlist[i], wb, workspace)) return 1;
  }
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
int basisChangeReg2Nontips(group_t *group, Matrix_t **matlist, long num)
/* Alters matrices in matlist */
{
  PTR workspace = FfAlloc(group->nontips);
  if (!workspace)
  {
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
  }
  int r = innerBasisChangeReg2Nontips(group, matlist, num, workspace);
  free(workspace);
  return r;
}

/******
 * 1 on error
 *************************************************************************/
int changeActionMatricesReg2Nontips(group_t *group)
{
  PTR workspace;
  workspace = FfAlloc(group->nontips);
  if (!workspace)
  {
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
  }
  int r = innerBasisChangeReg2Nontips(group, group->action, group->arrows, workspace);
  free(workspace);
  return r;
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

/****
 * 1 on error
 ***************************************************************************/
int calculateDimSteps(group_t *group)
/* Assumes we are working with RLL, but that the nontips
 * are arranged in ascending length-lex order. */
{
  long depth, i;
  long *dS;
  switch(group->ordering)
  {
  case 'R' :
    dS = (long *) malloc((group->maxlength + 3) * sizeof(long));
    if (!dS)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return 1;
      }
    dS[0] = 0;
    dS[1] = 1;
    i = 1;
    for (depth = 2; depth <= group->maxlength; depth++)
    {
      while (strlen(group->root[i].path) < depth) i++;
      if (strlen(group->root[i].path) != depth)
      {
          free(dS);
          MTX_ERROR("Theoretical Error: calculateDimSteps");
          return 1;
      }
      dS[depth] = i;
    }
    dS[group->maxlength+1] = group->nontips;
    dS[group->maxlength+2] = group->nontips;
    group->dS = dS;
    break;
  case 'J' :
    dS = (long *) malloc((group->nontips + 2) * sizeof(long));
    if (!dS)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return 1;
      }
    dS[0] = 0;
    dS[1] = 1;
    for (i = 1, depth = 1; i < group->nontips; i++)
      if (depth < group->root[i].dim)
      {
        if (group->root[i].dim != ++depth)
        { free(dS);
          MTX_ERROR("Theoretical Error");
          return 1;
        }
        dS[depth] = i;
      }
    dS[depth+1] = group->nontips;
    i = 1;
    group->dS = (long *) malloc((depth + 2) * sizeof(long));
    if (!group->dS)
      {
          free(dS);
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return 1;
      }
    memcpy(group->dS, dS, (depth + 2) * sizeof(long));
    free(dS);
    /* printf("Dim steps:\n"); */
    /* for (i=0; i <= depth+1; i++) printf("%d\n", group->dS[i]); */
    break;
  default:
    MTX_ERROR("not implemented for this ordering");
    return 1;
  }
  pathTreeGirth(group);
  return 0;
}

/****
 * NULL on error
 ***************************************************************************/
group_t *fullyLoadedGroupRecord(char *stem)
{
  group_t *G = namedGroupRecord(stem);
  if (!G) return NULL;
  if (loadNonTips(G))
  { freeGroupRecord(G);
    return NULL;
  }
  if (G->ordering == 'L')
  {
      MTX_ERROR("can't cope with LL ordering");
      return NULL;
  }
  if (G->ordering == 'J')
  { if (loadDimensions(G))
    { freeGroupRecord(G);
      return NULL;
    }
  }
  if (buildPathTree(G))
  { freeGroupRecord(G);
    return NULL;
  }
  if (buildLeftPathTree(G))
  { freeGroupRecord(G);
    return NULL;
  }
  if (markPathDimensions(G))
  { freeGroupRecord(G);
    return NULL;
  }
  if (loadActionMatrices(G))
  { freeGroupRecord(G);
    return NULL;
  }
  if (loadLeftActionMatrices(G))
  { freeGroupRecord(G);
    return NULL;
  }
  if (calculateDimSteps(G))
  { freeGroupRecord(G);
    return NULL;
  }
  return G;
}

/****
 * Potential error if -1 is returned
 ***************************************************************************/
static int matricesCommute(Matrix_t *a, Matrix_t *b, Matrix_t *ab,
  Matrix_t *ba)
{
  if (innerRightProduct(a, b, ab->Data)) return -1;
  if (innerRightProduct(b, a, ba->Data)) return -1;
  return MatCompare(ab,ba);
}

/*****
 * potential error if -1 is returned
 **************************************************************************/
int verifyGroupIsAbelian(group_t *A)
{
  long Asize = A->nontips;
  long ngens = A->arrows;
  long fl = A->action[0]->Field;
  long i, j;
  int thisPairCommutes;
  Matrix_t *ab = MatAlloc(fl, Asize, Asize);
  Matrix_t *ba = MatAlloc(fl, Asize, Asize);
  if (!ab || !ba)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return -1;
      }
  for (i = 0; i < ngens; i++)
    for (j = i+1; j < ngens; j++)
    {
      thisPairCommutes = matricesCommute(A->action[i], A->action[j], ab, ba);
      if (thisPairCommutes > 0) {MatFree(ab); MatFree(ba); return 0;}
      if (thisPairCommutes < 0)
      {
        if (thisPairCommutes == -1) {MatFree(ab); MatFree(ba); return -1;}
        MatFree(ab);
        MatFree(ba);
        return 0;
      }
    }
  MatFree(ab);
  MatFree(ba);
  return 1;
}

/****
 * NULL on error
 ***************************************************************************/
long *newLongArray(long N)
/* Array entries initialized to 0 */
{
  long *l, i;
  if (N <= 0)
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return NULL;
  }
  l = (long *) malloc(N * sizeof(long));
  if (!l)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  for (i = 0; i < N; i++) l[i] = 0;
  return l;
}

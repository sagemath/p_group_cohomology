/*****************************************************************************
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
/*
*  slice.c : Methods for the disk-based slice product storage system
*  Author: David J Green
*  First version: 16 March 2000 from urbild.c
*/

#include "nDiag.h"
#include "fp_decls.h"
#include "meataxe.h"
#include <stdio.h>

MTX_DEFINE_FILE_INFO

/*******************************************************************************
* static long layerSize(ngs_t *ngs, group_t *group, long dim)
{
  return ngs->r * (group->dS[dim+1] - group->dS[dim]);
* }
*/

/*******************************************************************************
* static long nodeIndex(ngs_t *ngs, group_t *group, long blo, long pat)
{
  long d = group->root[pat].dim;
  return (blo - 1) * (group->dS[d+1] - group->dS[d]) + pat - group->dS[d];
* }
*/

/******************************************************************************/
void freeGeneralVector(gV_t *gv)
{
  if (gv->w) free(gv->w);
  free(gv);
  return;
}

/****
 * NULL on error
 ***************************************************************************/
inline gV_t *generalVectorTemplate(long nor)
{
  gV_t *gv;
  PTR w;
  gv = (gV_t *) malloc(sizeof(gV_t));
  if (!gv)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  w = FfAlloc(nor);
  if (!w)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  gv->w = w;
  gv->radical = true; /* "default" value */
  return gv;
}

/******************************************************************************/
void pushGeneralVector(ngs_t *ngs, gV_t *gv)
{
  if (ngs->gVwaiting)
  {
    printf("Warning: pushGeneralVector discarding\n");
    freeGeneralVector(gv);
  }
  else
    ngs->gVwaiting = gv;
  return;
}

/***
 * 1 on error
 ****************************************************************************/
int makeVectorMonic(ngs_t *ngs, gV_t *gv)
/* f is the leading coefficient */
{
  register long nor = ngs->r + ngs->s;
  register FEL f = gv->coeff;
  register FEL g;
  PTR ptr;
  register int i;
  if (f == FF_ONE) return 0;
  if (f == FF_ZERO)
  { MTX_ERROR1("%E", MTX_ERR_DIV0);
    return 1;
  }
  g = FfInv(f);
  for (i = 0, ptr = gv->w; i < nor; i++, ptr+=FfCurrentRowSize) FfMulRow(ptr, g);
  return 0;
}

/******************************************************************************/
void findLeadingMonomial(gV_t *gv, long r, group_t *group)
/* By negative length, then by block, then by RLL */
{
  FEL coeff;
  register int b;
  register PTR ptr = gv->w;
  path_t rootcol;
  gv->len = group->maxlength+1;
  gv->coeff = FF_ZERO;
  gv->dim = ZERO_BLOCK;
  for (b = 0; b < r; b++, ptr+=FfCurrentRowSize)
  {
    register int col = FfFindPivot(ptr, &coeff);
    if (col != -1)
    {
      rootcol = group->root[col];
      if (rootcol.depth < gv->len)
      {
        gv->dim = rootcol.depth;
        gv->coeff = coeff;
        gv->len = rootcol.depth;
        gv->block = b;
        gv->col = col;
      }
    }
  }
}

/****
 * 1 on error
 ******************************************************************************/
int multiply(PTR row, Matrix_t *mat, PTR result, long r)
// Tests indicate that using Strassen (via innerRightProduct) unconditionally is fastest
//~ { if (r < 100)
  //~ {
    //~ register long i;
    //~ register PTR p1 = row;
    //~ register PTR p2 = result;
    //~ for (i = 0; i < r; i++, p1+=FfCurrentRowSize, p2+=FfCurrentRowSize)
    //~ {
        //~ FfMapRow(p1, mat->Data, FfNoc, p2);
    //~ }
    //~ return 0;
  //~ }
  //~ else
  { Matrix_t Row;
    FfSetField(mat->Field);
    FfSetNoc(mat->Noc);
    Row.Magic = mat->Magic;
    Row.Field = mat->Field;
    Row.Nor = r;
    Row.Noc = mat->Nor;  // sic!
    Row.PivotTable = NULL;
    Row.Data = row;
    Row.RowSize = FfCurrentRowSize;
    return innerRightProduct(&Row, mat, result);
  }
//~ }

/****
 * 1 on error
 ***************************************************************************/
int createWordForest(ngs_t *ngs, group_t *group)
/* There is a separate routine to initialize */
/* Forest contains ngs->r trees */
{
  register long i, j, k;
  long nodes = group->nontips;
  long arrows = group->arrows;
  long r = ngs->r;
  //  modW_t **proot = (modW_t **) malloc(r * sizeof(modW_t *));
  modW_t **proot = (modW_t **) malloc(r * sizeof(void*));
  modW_t *proot0 = (modW_t *) malloc(r * nodes * sizeof(modW_t));
  //  modW_t **kinder = (modW_t **) malloc(r * arrows * nodes * sizeof(modW_t *));
  modW_t **kinder = (modW_t **) malloc(r * arrows * nodes * sizeof(void*));
  modW_t *node;
  if (!proot || !proot0 || !kinder)
    { MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return 1;
    }
  for (i = 0; i < r * arrows * nodes; i++)
    kinder[i] = NULL;
  for (i = 0; i < r; i++)
  {
    proot[i] = proot0 + i * nodes;
    for (j = 0; j < nodes; j++)
    {
      node = proot[i] + j;
      node->child =
        kinder + ((i * nodes + j) * arrows);
      node->divisor = NULL;
      node->status = NO_DIVISOR;
      for (k = 0; k < arrows; k++)
        if (group->root[j].child[k] != NULL)
          node->child[k] =
            proot[i] + group->root[j].child[k]->index;
    }
  }
  ngs->proot = proot;
  return 0;
}

/******************************************************************************
Simon King (2008-12) this function occurs only once, hence, insert it manually
void freeWordForest(ngs_t *ngs)
{
  modW_t **proot = ngs->proot;
  free(proot[0][0].child);
  free(proot[0]);
  free(proot);
  return;
}
*/

/****
 * 1 on error
 ***************************************************************************/
static int updateWordStatusData(ngs_t *ngs, group_t *group)
{
  register long blo, pat, nops;
  register long dim = ngs->dimLoaded;
  register modW_t *node;
  if (dim == NONE)
  {
      MTX_ERROR("no dimLoaded");
      return 1;
  }
  for (blo = 0, nops = 0; blo < ngs->r; blo++)
    for (pat = group->dS[dim]; pat < group->dS[dim+1]; pat++)
    {
      node = ngs->proot[blo] + pat;
      if (node->divisor && node->qi != 0) node->status = nops++;
    }
  ngs->nops = nops;
  return 0;
}

/******************************************************************************/
static char *storedProductFile(ngs_t *ngs, long dim)
/* String returned must be used at once, never reused, never freed. */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%s%ld.stp", ngs->stem, dim);
  return buffer;
}

/******************************************************************************
 * Return 1 on error
 */
static int removeStoredProductFile(ngs_t *ngs, long d)
{
  if (remove(storedProductFile(ngs, d)))
  { MTX_ERROR1("Cannot remove file %s", storedProductFile(ngs, d));
    return 1;
  }
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int destroyCurrentDimension(ngs_t *ngs)
{
  if (ngs->dimLoaded == NONE)
  { MTX_ERROR("no current dimension");
    return 1;
  }
  if (ngs->dimLoaded != ngs->expDim)
    { if (removeStoredProductFile(ngs, ngs->dimLoaded)) return 1; }
  ngs->blockLoaded = NONE;
  ngs->dimLoaded = NONE;
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int destroyCurrentDimensionIfAny(ngs_t *ngs)
{
  if (ngs->dimLoaded == NONE) return 0;
  return destroyCurrentDimension(ngs);
}

/******************************************************************************/
int destroyExpansionSliceFile(ngs_t *ngs)
{
  return removeStoredProductFile(ngs, ngs->expDim);
}

/******************************************************************************/
static long smallestDimensionOfReduced(ngs_t *ngs)
{
  if (!ngs->firstReduced) return NONE;
  return ngs->firstReduced->gv->dim;
}

/*****
 * 1 on error
 **************************************************************************/
static int loadBlock(ngs_t *ngs, long block)
{
  FILE *fp;
  long nor = ngs->r + ngs->s;
  long totrows, blen = ngs->blockSize;
  long lastblock = (ngs->nops - 1) / ngs->blockSize;
  if (block == lastblock)
    blen = 1 + (ngs->nops-1) % ngs->blockSize;
  fp = readhdrplus(storedProductFile(ngs, ngs->dimLoaded), NULL, &totrows,
    NULL);
  if (!fp) {printf("readhdrplus returns NULL\n"); return 1;}
  if (totrows != nor * ngs->nops)
  {
    MTX_ERROR1("incorrect number of rows: %E", MTX_ERR_INCOMPAT);
    return 1;
  }
  /*FfSeekRow(fp, 1 + block * nor * ngs->blockSize);*/
  totrows = FfCurrentRowSizeIo*(block * nor * ngs->blockSize);
  if (totrows) SysFseekRelative(fp, totrows);
  register long blennor = blen * nor;
  totrows = FfReadRows(fp, ngs->thisBlock, blennor);
  if (totrows != blennor)
  { fclose(fp);
    MTX_ERROR2("%s: %E", storedProductFile(ngs, ngs->dimLoaded), MTX_ERR_FILEFMT);
    return 1;
  }
  fclose(fp);
  ngs->blockLoaded = block;
  return 0;
}

/*****
 * NULL on error
 **************************************************************************/
PTR nodeVector(ngs_t *ngs, group_t *group, modW_t *node)
{
  PTR w;
  long i = node->status;
  if (i == NO_DIVISOR)
  {
      MTX_ERROR("no divisor");
      return NULL;
  }
  if (i == SCALAR_MULTIPLE)
    w = node->divisor->gv->w;
  else
  {
    long block = i / ngs->blockSize;
    long pos = i % ngs->blockSize;
    long nor = ngs->r + ngs->s;
    if (ngs->blockLoaded != block)
    { if (loadBlock(ngs, block)) return NULL;
    }
    w = FfGetPtr(ngs->thisBlock, pos * nor);
  }
  return w;
}

static inline void commenceNewDimension(ngs_t *ngs, group_t *group, int dim)
{
    (ngs)->dimLoaded = dim;
    updateWordStatusData((ngs),(group)), (group);
    (ngs)->blockLoaded = NONE;
}


/*****
 * 1 on error
 **************************************************************************/
static int calculateNextProducts(ngs_t *ngs, group_t *group)
/* Assumes ngs->dimLoaded is set */
{
  long d = ngs->dimLoaded;
  /* long lS = layerSize(ngs, group, d); */
  register long a;
  long pat;
  long blo;
  long nor = ngs->r + ngs->s;
  register long nops = 0;
  register long offset = 0;
  modW_t *node;
  PTR w, dest;
  FILE *fp = writehdrplus(storedProductFile(ngs, d+1), FfOrder, 0, group->nontips);
  if (!fp) return 1;
  for (blo = 0; blo < ngs->r; blo++)
    for (pat = group->dS[d]; pat < group->dS[d+1]; pat++)
    {
      node = ngs->proot[blo] + pat;
      if (node->status == NO_DIVISOR) continue;
      w = nodeVector(ngs, group, node);
      if (!w) return 1;
      for (a = 0; a < group->arrows; a++)
      {
        if (node->child[a])
        {
          dest = FfGetPtr(ngs->theseProds, nor * offset++);
          if (multiply(w, group->action[a], dest, nor)) return 1;
          nops++;
          if (offset == ngs->blockSize)
          {
            if (FfWriteRows(fp, ngs->theseProds, nor * offset) != nor * offset)
            { fclose(fp);
              MTX_ERROR1("expected nor * offset: %E", MTX_ERR_INCOMPAT);
              return 1;
            }
            offset = 0;
          }
        }
      }
    }
  if (offset != 0)
  {
    if (FfWriteRows(fp, ngs->theseProds, nor * offset) != nor * offset)
    { fclose(fp);
      MTX_ERROR1("expected nor * offset: %E", MTX_ERR_INCOMPAT);
      return 1;
    }
  }
  int r = alterhdrplus(fp, nops * nor);
  fclose(fp);
  return r;
}

/****
 * 1 on error
 ***************************************************************************/
static int createEmptySliceFile(ngs_t *ngs, group_t *group, long d)
{
  FILE *fp = writehdrplus(storedProductFile(ngs, d), FfOrder, 0, group->nontips);
  if (!fp) return 1;
  fclose(fp);
  return 0;
}

/******************************************************************************/
static boolean expansionSlicePresent(ngs_t *ngs)
{
  if (ngs->expDim == NO_BUCHBERGER_REQUIRED) return false;
  if (ngs->expDim == NOTHING_TO_EXPAND) return false;
  return true;
}

/******************************************************************************/
static inline boolean shouldUseExpansionSlice(ngs_t *ngs, long dim)
{
  if (!expansionSlicePresent(ngs)) return false;
  if (ngs->expDim > dim) return false;
  if (ngs->dimLoaded != NONE && ngs->dimLoaded >= ngs->expDim) return false;
  return true;
}

/****
 * 1 on error
 ***************************************************************************/
int loadExpansionSlice(ngs_t *ngs, group_t *group)
{
  if (ngs->dimLoaded != NONE)
  { MTX_ERROR1("something already loaded: %E", MTX_ERR_BADUSAGE);
    return 1;
  }
  commenceNewDimension(ngs, group, ngs->expDim);
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
int incrementSlice(ngs_t *ngs, group_t *group)
{
  register long n = ngs->dimLoaded;
  if (n == NONE)
  { MTX_ERROR1("nothing loaded: %E", MTX_ERR_BADUSAGE);
    return 1;
  }
  if (calculateNextProducts(ngs, group)) return 1;
  if (destroyCurrentDimension(ngs)) return 1;
  commenceNewDimension(ngs,group,n+1);
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
int selectNewDimension(ngs_t *ngs, group_t *group, long dim)
{
  register long n;
  if (ngs->dimLoaded == dim) return 0;
  if (ngs->dimLoaded != NONE && ngs->dimLoaded > dim)
  {
    printf("Warning sND: Backtracking\n");
    if (destroyCurrentDimension(ngs)) return 1;
  }
  if (shouldUseExpansionSlice(ngs, dim))
  {
    if (destroyCurrentDimensionIfAny(ngs)) return 1;
    if (loadExpansionSlice(ngs, group)) return 1;
  }
  if (ngs->dimLoaded == NONE)
  {
    n = smallestDimensionOfReduced(ngs);
    if (n == NONE || n > dim) n = dim;
    if (createEmptySliceFile(ngs, group, n)) return 1;
    commenceNewDimension(ngs, group, n); /* uWSD should set nops = 0 */
    if (ngs->nops != 0)
    { MTX_ERROR1("theoretical error: ngs->nops = %d\n",ngs->nops);
      return 1;
    }
  }
  for (n = ngs->dimLoaded; n < dim; n++)
    if (incrementSlice(ngs, group)) return 1;
  return 0;
}

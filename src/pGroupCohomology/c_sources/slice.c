/*****************************************************************************
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
/*
*  slice.c : Methods for the disk-based slice product storage system
*  Author: David J Green
*  First version: 16 March 2000 from urbild.c
*/

#include "nDiag.h"
#include "meataxe.h"

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

/******************************************************************************/
inline gV_t *generalVectorTemplate(long nor)
{
  gV_t *gv;
  PTR w;
  gv = (gV_t *) malloc(sizeof(gV_t));
  w = zalloc(nor);
  if (!gv || !w) AllocationError("generalVectorTemplate");
  gv->w = w;
  gv->radical = true; /* "default" value */
  return gv;
}

/******************************************************************************
gV_t *popGeneralVector(ngs_t *ngs)
{
  gV_t *gv;
  if (ngs->gVwaiting)
  {
    gv = ngs->gVwaiting;
    ngs->gVwaiting = NULL;
  }
  else
    gv = generalVectorTemplate(ngs->r + ngs->s);
  return gv;
}
*/
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

/******************************************************************************/
inline void makeVectorMonic(ngs_t *ngs, gV_t *gv)
/* f is the leading coefficient */
{
  register long nor = ngs->r + ngs->s;
  register FEL f = gv->coeff;
  register FEL g;
  PTR ptr;
  register long i;
  if (f == F_ONE) return;
  if (f == F_ZERO) OtherError("makeVectorMonic: input is zero");
  g = zdiv(F_ONE, f);
  for (i = 0, ptr = gv->w; i < nor; i++, zsteprow(&ptr)) zmulrow(ptr, g);
  return;
}

/******************************************************************************/
void findLeadingMonomial(gV_t *gv, long r, group_t *group)
/* By dim, then by block, then by RLL */
{
  FEL coeff;
  register long b;
  // register long d;
  //  register long col;
  PTR ptr = gv->w;
  gv->dim = group->nontips + 1;
  gv->coeff = F_ZERO;
  for (b = 1; b <= r; b++, zsteprow(&ptr))
  {  
    register long col = zfindpiv(ptr, &coeff);
    if (col != 0)
    {
      register long d = group->root[col-1].dim;
      if (d < gv->dim)
      {  
        gv->dim = d;
        gv->coeff = coeff;
        gv->len = group->root[col-1].depth;
        gv->block = b;
        gv->col = col;
      }
    }
  }  
  if (gv->dim == group->nontips + 1) gv->dim = ZERO_BLOCK;
  return;
}    

/******************************************************************************/
inline void multiply(PTR row, matrix_t *mat, PTR result, long r)
{
  register long i;
  PTR p1 = row;
  PTR p2 = result;
  register long noc = znoc;
  for (i = 0; i < r; i++)
  {
    zmaprow(p1, mat->d, noc, p2);
    zsteprow(&p1); zsteprow(&p2);
  }
  return;
}

/******************************************************************************/
void createWordForest(ngs_t *ngs, group_t *group)
/* There is a separate routine to initialize */
/* Forest contains ngs->r trees */
{
  register long i, j, k;
  long nodes = group->nontips;
  long arrows = group->arrows;
  long r = ngs->r;
  //  modW_t **proot = (modW_t **) malloc(r * sizeof(modW_t *));
  modW_t **proot = (modW_t **) malloc(r << PTRSH);
  modW_t *proot0 = (modW_t *) malloc(r * nodes * sizeof(modW_t));
  //  modW_t **kinder = (modW_t **) malloc(r * arrows * nodes * sizeof(modW_t *));
  modW_t **kinder = (modW_t **) malloc(r * arrows * nodes << PTRSH);
  modW_t *node;
  if (!proot || !proot0 || !kinder)
    AllocationError("createWordForest");
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
  return;
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

/******************************************************************************/
long maxDim(group_t *group)
{
  register long d = 0;
  switch (group->ordering)
  {
  case 'R' :
    d = group->maxlength;
    break;
  case 'J' :
    for (d = 0; group->dS[d+1] != group->nontips; d++);
    break;
  default :
    OtherError("maxDim: not implemented for this ordering");
    break;
  }
  return d;
}

/******************************************************************************/
static void updateWordStatusData(ngs_t *ngs, group_t *group)
{
  register long blo, pat, nops;
  register long dim = ngs->dimLoaded;
  register modW_t *node;
  if (dim == NONE) OtherError("uWSD: no dimLoaded");
  for (blo = 0, nops = 0; blo < ngs->r; blo++)
    for (pat = group->dS[dim]; pat < group->dS[dim+1]; pat++)
    {
      node = ngs->proot[blo] + pat;
      if (node->divisor && node->qi != 0) node->status = nops++;
    }
  ngs->nops = nops;
  return;
}

/******************************************************************************/
static char *storedProductFile(ngs_t *ngs, long dim)
/* String returned must be used at once, never reused, never freed. */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%s%ld.stp", ngs->stem, dim);
  return buffer;
}

/******************************************************************************/
static void removeStoredProductFile(ngs_t *ngs, long d)
{
  static char buffer[MAXLINE];
  sprintf(buffer, "rm %s", storedProductFile(ngs, d));
  system(buffer);
  return;
}

/******************************************************************************/
void destroyCurrentDimension(ngs_t *ngs)
{
  if (ngs->dimLoaded == NONE) OtherError("dCD: no current dimension");
  if (ngs->dimLoaded != ngs->expDim)
    removeStoredProductFile(ngs, ngs->dimLoaded);
  ngs->blockLoaded = NONE;
  ngs->dimLoaded = NONE;
  return;
}

/******************************************************************************/
void destroyCurrentDimensionIfAny(ngs_t *ngs)
{
  if (ngs->dimLoaded == NONE) return;
  destroyCurrentDimension(ngs);
  return;
}

/******************************************************************************/
void destroyExpansionSliceFile(ngs_t *ngs)
{
  removeStoredProductFile(ngs, ngs->expDim);
  return;
}

/******************************************************************************/
static long smallestDimensionOfReduced(ngs_t *ngs)
{
  if (!ngs->firstReduced) return NONE;
  return ngs->firstReduced->gv->dim;
}

/******************************************************************************/
static void loadBlock(ngs_t *ngs, long block)
{
  FILE *fp;
  long nor = ngs->r + ngs->s;
  long totrows, blen = ngs->blockSize;
  long lastblock = (ngs->nops - 1) / ngs->blockSize;
  if (block == lastblock)
    blen = 1 + (ngs->nops-1) % ngs->blockSize;
  fp = readhdrplus(storedProductFile(ngs, ngs->dimLoaded), NULL, &totrows,
    NULL);
  if (totrows != nor * ngs->nops)
  {
    OtherError("loadBlock: incorrect number of rows");
  }
  zseek(fp, 1 + block * nor * ngs->blockSize);
  register long blennor = blen * nor;
  if (zreadvec(fp, ngs->thisBlock, blennor) != blennor)
    OtherError("loadBlock: reading");
  fclose(fp);
  ngs->blockLoaded = block;
  return;
}

/******************************************************************************/
PTR nodeVector(ngs_t *ngs, group_t *group, modW_t *node)
{
  PTR w;
  long i = node->status;
  if (i == NO_DIVISOR)
    OtherError("nodeVector: no divisor");
  if (i == SCALAR_MULTIPLE)
    w = node->divisor->gv->w;
  else
  {
    long block = i / ngs->blockSize;
    long pos = i % ngs->blockSize;
    long nor = ngs->r + ngs->s;
    if (ngs->blockLoaded != block) loadBlock(ngs, block);
    w = ptrPlus(ngs->thisBlock, pos * nor);
  }
  return w;
}

/*******************************************************************************
* static void checkStoredProducts(ngs_t *ngs, group_t *group)
{
  long dim = ngs->dimLoaded;
  long blo, i;
  long nops = 0;
  gV_t *gv = popGeneralVector(ngs);
  PTR tmp=gv->w;
  modW_t *node;
  boolean discs = false;
  for (blo = 0; blo < ngs->r; blo++)
  {
    for (i = group->dS[dim]; i < group->dS[dim+1]; i++)
    {
      node = ngs->proot[blo] + i;
      if (node->status == NO_DIVISOR || node->status == SCALAR_MULTIPLE)
        continue;
      nops++;
      gv->w = nodeVector(ngs, group, node);
      findLeadingMonomial(gv, ngs->r, group);
      if (gv->block != blo+1 || gv->col != i+1)
      {
        discs = true;
      }
    }
  }
  gv->w = tmp;
  pushGeneralVector(ngs, gv);
  if (discs)
  {
    OtherError("Discrepancies");
  }
  return;
* }
*/

/******************************************************************************
Simon King: This should be a macro
static void commenceNewDimension(ngs_t *ngs, group_t *group, long dim)
{
  ngs->dimLoaded = dim;
  updateWordStatusData(ngs, group);
  ngs->blockLoaded = NONE;
  return;
}
*/
#if !defined(commenceNewDimension)
#define commenceNewDimension(ngs,group,dim) ( {(ngs)->dimLoaded = dim; updateWordStatusData((ngs),(group)), (group); (ngs)->blockLoaded = NONE;})
#endif

/******************************************************************************/
static void calculateNextProducts(ngs_t *ngs, group_t *group)
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
  FILE *fp = writehdrplus(storedProductFile(ngs, d+1), zfl, 0, group->nontips);
  for (blo = 0; blo < ngs->r; blo++)
    for (pat = group->dS[d]; pat < group->dS[d+1]; pat++)
    {
      node = ngs->proot[blo] + pat;
      if (node->status == NO_DIVISOR) continue;
      w = nodeVector(ngs, group, node);
      for (a = 0; a < group->arrows; a++)
      {
        if (node->child[a])
        {
          dest = ptrPlus(ngs->theseProds, nor * offset++);
          multiply(w, group->action[a], dest, nor);
          nops++;
          if (offset == ngs->blockSize)
          {
            if (zwritevec(fp, ngs->theseProds, nor * offset) != nor * offset)
              OtherError("cNP: writing vectors");
            offset = 0;
          }
        }
      }
    }
  if (offset != 0)
  {
    if (zwritevec(fp, ngs->theseProds, nor * offset) != nor * offset)
      OtherError("cNP: writing vectors");
  }
  alterhdrplus(fp, nops * nor);
  fclose(fp);
  return;
}

/******************************************************************************/
static void createEmptySliceFile(ngs_t *ngs, group_t *group, long d)
{
  FILE *fp = writehdrplus(storedProductFile(ngs, d), zfl, 0, group->nontips);
  fclose(fp);
  return;
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

/******************************************************************************/
void loadExpansionSlice(ngs_t *ngs, group_t *group)
{
  if (ngs->dimLoaded != NONE)
    OtherError("loadExpSlice: something already loaded");
  commenceNewDimension(ngs, group, ngs->expDim);
  return;
}

/******************************************************************************/
void incrementSlice(ngs_t *ngs, group_t *group)
{
  register long n = ngs->dimLoaded;
  if (n == NONE)
    OtherError("incrementSlice: nothing loaded");
  calculateNextProducts(ngs, group);
  destroyCurrentDimension(ngs);
  commenceNewDimension(ngs,group,n+1);
  return;
}

/******************************************************************************/
void selectNewDimension(ngs_t *ngs, group_t *group, long dim)
{
  register long n;
  if (ngs->dimLoaded == dim) return;
  if (ngs->dimLoaded != NONE && ngs->dimLoaded > dim)
  {
    printf("Warning sND: Backtracking\n");
    destroyCurrentDimension(ngs);
  }
  if (shouldUseExpansionSlice(ngs, dim))
  {
    destroyCurrentDimensionIfAny(ngs);
    loadExpansionSlice(ngs, group);
  }
  if (ngs->dimLoaded == NONE)
  {
    n = smallestDimensionOfReduced(ngs);
    if (n == NONE || n > dim) n = dim;
    createEmptySliceFile(ngs, group, n);
    commenceNewDimension(ngs, group, n); /* uWSD should set nops = 0 */
    if (ngs->nops != 0) OtherError("sND: theoretical error");
  }
  for (n = ngs->dimLoaded; n < dim; n++)
    incrementSlice(ngs, group);
  return;
}

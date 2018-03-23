/*****************************************************************************
       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>

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
*  urbild.c : Miscellaneous subfree module routines, new storage methods
*  Author: David J Green
*  First version: 13 March 2000 from widget.c
*/

#include "nDiag.h"
#include "slice_decls.h"
#include "fp_decls.h"
#include "meataxe.h"

MTX_DEFINE_FILE_INFO

/******
 * 1 on error
 *************************************************************************/
int saveMinimalGenerators(nFgs_t *nFgs, char *outfile, group_t *group)
/* corrupts nFgs (REALLY?? 13.03.00)*/
{
  ngs_t *ngs = nFgs->ngs;
  FILE *fp;
  long nor = 0;
  gV_t *gv;
  rV_t *rv;
  fp = writehdrplus(outfile, FfOrder, 0, group->nontips);
  if (!fp) return 1;
  for (rv = ngs->firstReduced; rv; rv = rv->next)
  {
    gv = rv->gv;
    if (!gv->radical) /* i.e. this rv a min generator */
    {
      if (FfWriteRows(fp,gv->w,ngs->r) != ngs->r)
      { fclose(fp);
        return 1;
      }
      nor += ngs->r;
    }
  }
  int r = alterhdrplus(fp,nor);
  fclose(fp);
  return r;
}

/******************************************************************************/
Matrix_t *getMinimalGenerators(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  long nor = 0;
  long noc = group->nontips;
  long i;
  gV_t *gv;
  rV_t *rv;
  Matrix_t *OUT;
  PTR p;
  register char *b;
  /* fp = writehdrplus(outfile, FfOrder, 0, group->nontips);
   i.e. FfOrder is the fl, group->nontips is noc, and nor will be determined now:
  */
  for (rv = ngs->firstReduced; rv; rv = rv->next)
  {
    gv = rv->gv;
    if (!gv->radical) /* i.e. this rv a min generator */
    {
      nor += ngs->r;
    }
  }
  /* alterhdrplus(fp,nor);*/
  OUT = MatAlloc(FfOrder, nor, noc);
  p = (PTR)OUT->Data;
  for (rv = ngs->firstReduced; rv; rv = rv->next)
  {
    gv = rv->gv;
    if (!gv->radical) /* i.e. this rv a min generator */
    {
      b = (char *)gv->w;
      for (i = 0; i < ngs->r; ++i)
    { memcpy(p,b,FfCurrentRowSize);
      b += FfCurrentRowSize;
      FfStepPtr(&(p));
    }
    }
  }
  return OUT;
}

/******
 * 1 on error
 *************************************************************************/
int saveUrbildGroebnerBasis(nRgs_t *nRgs, char *outfile, group_t *group)
{
  ngs_t *ngs = nRgs->ngs;
  FILE *fp;
  long nor = 0;
  long t = ngs->r + ngs->s;
  gV_t *gv;
  rV_t *rv;
  fp = writehdrplus(outfile, FfOrder, 0, group->nontips);
  if (!fp) return 1;
  for (rv = ngs->firstReduced; rv; rv = rv->next)
  {
    gv = rv->gv;
    if (FfWriteRows(fp, gv->w, t) != t)
    { fclose(fp);
      return 1;
    }
    nor += t;
  }
  int r = alterhdrplus(fp,nor);
  fclose(fp);
  return r;
}

/******************************************************************************/
long numberOfHeadyVectors(ngs_t *ngs)
{
  rV_t *rv;
  uV_t *uv;
  long gens = 0;
  for (rv = ngs->firstReduced; rv; rv = rv->next)
    if (!rv->gv->radical) gens++;
  for (uv = ngs->unreducedHeap; uv; uv = uv->next)
    if (!uv->gv->radical) gens++;
  return gens;
}

/******************************************************************************/
long dimensionOfDeepestHeady(ngs_t *ngs)
{
  rV_t *rv;
  uV_t *uv;
  long hd = 0;
  for (rv = ngs->firstReduced; rv; rv = rv->next)
    if (!rv->gv->radical && rv->gv->dim > hd) hd = rv->gv->dim;
  for (uv = ngs->unreducedHeap; uv; uv = uv->next)
    if (!uv->gv->radical && uv->gv->dim > hd) hd = uv->gv->dim;
  return hd;
}

/******************************************************************************/
static inline long numberOfReducedVectors(ngs_t *ngs)
{
  long n;
  rV_t *rv;
  for (n = 0, rv = ngs->firstReduced; rv; n++, rv = rv->next);
  return n;
}

/******************************************************************************/
static inline long numberOfUnreducedVectors(ngs_t *ngs)
{
  long n;
  uV_t *uv;
  for (n = 0, uv = ngs->unreducedHeap; uv; n++, uv = uv->next);
  return n;
}

#if !defined(targetPnontips)
#define targetPnontips(ngs,group) ((ngs)->r * (group)->nontips - (ngs)->targetRank)
#endif

/*****
 * 1 on error
 **************************************************************************/
int saveNFgs(nFgs_t *nFgs, group_t *group, char *outfile, char *markfile)
{
  ngs_t *ngs = nFgs->ngs;
  FILE *fp;
  long nor;
  rV_t *rv;
  fp = writehdrplus(outfile, FfOrder, 0, group->nontips);
  if (!fp) return 1;
  for (rv = ngs->firstReduced, nor = 0; rv ; rv = rv->next, nor += ngs->r)
    if (FfWriteRows(fp,rv->gv->w,ngs->r) != ngs->r)
    { fclose(fp);
      return 1;
    }
  int r = alterhdrplus(fp,nor);
  fclose(fp);
  if (r) return 1;
  fp = fopen(markfile, "w");
  if (!fp) return 1;
  for (rv = ngs->firstReduced; rv ; rv = rv->next)
    fprintf(fp, "%c", rv->gv->radical ? 'R' : 'H');
  fprintf(fp,"\n");
  fclose(fp);
  /* printf("marks saved to %s\n", markfile); */
  return 0;
}

/****
 * 1 on error
 **************************************************************************/
int saveNRgs(nRgs_t *nRgs, group_t *group, char *outfile, char *markfile)
{
  ngs_t *ngs = nRgs->ngs;
  FILE *fp;
  long nor;
  rV_t *rv;
  fp = writehdrplus(outfile, FfOrder, 0, group->nontips);
  if (!fp) return 1;
  for (rv = ngs->firstReduced, nor = 0; rv ; rv = rv->next, nor += ngs->r)
    if (FfWriteRows(fp,rv->gv->w,ngs->r) != ngs->r)
    { fclose(fp);
      return 1;
    }
  int r = alterhdrplus(fp,nor);
  fclose(fp);
  if (r) return 1;
  fp = writehdrplus(markfile, FfOrder, 0, group->nontips);
  if (!fp) return 1;
  for (rv = ngs->firstReduced, nor = 0; rv ; rv = rv->next, nor += ngs->s)
    if (FfWriteRows(fp, FfGetPtr(rv->gv->w, ngs->r), ngs->s) != ngs->s)
    {
        fclose(fp);
        return 1;
    }
  r = alterhdrplus(fp,nor);
  fclose(fp);
  /* printf("preimages saved to %s\n", markfile); */
  return r;
}

/****
 * Null on error
 ***************************************************************/
static ngs_t *ngsAllocation(long r, long s, group_t *group, char *stem)
{
  ngs_t *ngs = (ngs_t *) malloc(sizeof(ngs_t));
  if (!ngs)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  ngs->r = r;
  ngs->s = s;
  ngs->firstReduced = NULL;
  ngs->lastReduced = NULL;
  ngs->unreducedHeap = NULL;
  ngs->pnontips = r * group->nontips;
  ngs->expDim = NOTHING_TO_EXPAND;
  ngs->targetRank = RANK_UNKNOWN;
  ngs->gVwaiting = NULL;
  if (createWordForest(ngs, group))
  { free(ngs);
    return NULL;
  }
  ngs->dimLoaded = NONE;
  ngs->blockLoaded = NONE;
  ngs->blockSize = BLOCK_SIZE;
  ngs->thisBlock = FfAlloc(ngs->blockSize * (r + s));
  ngs->theseProds = FfAlloc(ngs->blockSize * (r + s));
  ngs->w = FfAlloc(r + s);
  if (!ngs->thisBlock || !ngs->theseProds || !ngs->w)
  { free(ngs);
    MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  strcpy(ngs->stem, stem);
  return ngs;
}

/****
 * Null on error
 ***************************************************************************/
nFgs_t *nFgsAllocation(group_t *group, long r, char *stem)
{
  char thisStem[MAXLINE];
  nFgs_t *nFgs = (nFgs_t *) malloc(sizeof(nFgs_t));
  if (!nFgs)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  sprintf(thisStem, "%sf", stem);
  nFgs->ngs = ngsAllocation(r, 0, group, thisStem);
  if (!nFgs->ngs)
  {
      free(nFgs);
      return NULL;
  }
  nFgs->finished = false;
  nFgs->nRgsUnfinished = false;
  nFgs->max_unfruitful = MAX_UNFRUITFUL;
  return nFgs;
}

/******************************************************************************/
void freeReducedVector(rV_t *rv, ngs_t *ngs)
{
  if (rv->gv) freeGeneralVector(rv->gv);
  free(rv);
  return;
}

/******************************************************************************/
static void freeReducedVectors(rV_t *first, ngs_t *ngs)
{
  rV_t *rv, *next;
  if (first && first->prev) first->prev->next = NULL;
  for (rv = first; rv; rv = next)
  {
    next = rv->next;
    freeReducedVector(rv, ngs);
  }
  return;
}

/******************************************************************************/
void freeUnreducedVector(uV_t *uv)
{
  if (uv->gv) freeGeneralVector(uv->gv);
  free(uv);
  return;
}

/******************************************************************************/
static void freeUnreducedVectors(ngs_t *ngs)
{
  uV_t *first = ngs->unreducedHeap;
  uV_t *uv, *next;
  if (first && first->prev) first->prev->next = NULL;
  for (uv = first; uv; uv = next)
  {
    next = uv->next;
    freeUnreducedVector(uv);
  }
  return;
}

/******************************************************************************/
void freeNgs(ngs_t *ngs)
{
  freeReducedVectors(ngs->firstReduced, ngs);
  freeUnreducedVectors(ngs);
  if (ngs->proot)
  {
    // freeWordForest(ngs);
    modW_t **proot = ngs->proot;
    free(proot[0][0].child);
    free(proot[0]);
    free(proot);
  }
  if (ngs->gVwaiting) freeGeneralVector(ngs->gVwaiting);
  if (ngs->thisBlock) free(ngs->thisBlock);
  if (ngs->theseProds) free(ngs->theseProds);
  if (ngs->w) free(ngs->w);
  free(ngs);
  return;
}

/*****
 * NULL on error
 **************************************************************************/
nRgs_t *nRgsAllocation(group_t *group, long r, long s, char *stem)
{
  char thisStem[MAXLINE];
  nRgs_t *nRgs = (nRgs_t *) malloc(sizeof(nRgs_t));
  if (!nRgs)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  sprintf(thisStem, "%sr", stem);
  nRgs->ngs = ngsAllocation(r, s, group, thisStem);
  if (!nRgs->ngs)
  {
      free(nRgs);
      return NULL;
  }
  nRgs->ker = nFgsAllocation(group, s, stem);
  if (!nRgs->ker)
  { freeNgs(nRgs->ngs);
    free(nRgs);
    return NULL;
  }
  nRgs->overshoot = MAX_OVERSHOOT;
  return nRgs;
}

/******************************************************************************/
void freeNFgs(nFgs_t *nFgs)
{
  freeNgs(nFgs->ngs);
  free(nFgs);
  return;
}

/******************************************************************************/
void freeNRgs(nRgs_t *nRgs)
{
  freeNgs(nRgs->ngs);
  freeNFgs(nRgs->ker);
  free(nRgs);
  return;
}

/******************************************************************************/
static boolean vectorLessThan(gV_t *w1, gV_t *w2)
{
  if (w1->len > w2->len) return true;
  if (w1->len < w2->len) return false;
  if (w1->block > w2->block) return true;
  if (w1->block < w2->block) return false;
  if (w1->col > w2->col) return true;
  if (w1->col < w2->col) return false;
  if (w2->radical && !w1->radical) return true;
  return false;
}

/******************************************************************************/
static rV_t *reducedSuccessor(ngs_t *ngs, rV_t *rv)
{
  return (rv == NULL) ? ngs->firstReduced : rv->next;
}

/******************************************************************************/
static void insertReducedVectorAfter(ngs_t *ngs, rV_t *base, rV_t *rv)
{
  rV_t *next = reducedSuccessor(ngs, base);
  rv->prev = base;
  rv->next = next;
  if (next == NULL)
    ngs->lastReduced = rv;
  else
    next->prev = rv;
  if (base == NULL)
    ngs->firstReduced = rv;
  else
    base->next = rv;
  return;
}

/*****
 * 1 on error
 **************************************************************************/
static int lowerExpDimIfNecessary(ngs_t *ngs, long d)
{
  if (ngs->expDim == NO_BUCHBERGER_REQUIRED) { return 0;}
  if (d != ngs->dimLoaded)
  { MTX_ERROR3("The current dimension should be %d, not %d: %E", ngs->dimLoaded, d, MTX_ERR_INCOMPAT);
    return 1;
  }
  if (ngs->expDim == NOTHING_TO_EXPAND)
  {
    ngs->expDim = d;
    return 0;
  }
  if (ngs->expDim > d)
  {
    if (destroyExpansionSliceFile(ngs)) return 1;
    ngs->expDim = d;
  }
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
int insertReducedVector(ngs_t *ngs, rV_t *rv)
/* See expansion routines for info on expDim */
{
  rV_t *base = ngs->lastReduced;
  while (base && vectorLessThan(base->gv, rv->gv))
    base = base->prev;
  insertReducedVectorAfter(ngs, base, rv);
  rv->expDim = rv->gv->dim;
  return lowerExpDimIfNecessary(ngs, rv->expDim);
}

/******************************************************************************/
void unlinkReducedVector(ngs_t *ngs, rV_t *rv)
{
  rV_t *rv1;
  rv1 = rv->prev;
  if (rv1 == NULL)
    ngs->firstReduced = rv->next;
  else
    rv1->next = rv->next;
  rv1 = rv->next;
  if (rv1 == NULL)
    ngs->lastReduced = rv->prev;
  else
    rv1->prev = rv->prev;
  rv->prev = NULL; rv->next = NULL;
  return;
}

/*****
 * NULL on error
 **************************************************************************/
uV_t *unreducedVector(ngs_t *ngs, gV_t *gv)
{
  uV_t *uv = (uV_t *) malloc(sizeof(uV_t));
  if (!uv)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  uv->gv = gv; uv->prev = NULL; uv->next = NULL;
  return uv;
}

/******************************************************************************/
uV_t *unreducedSuccessor(ngs_t *ngs, uV_t *uv)
{
  return (uv == NULL) ? ngs->unreducedHeap : uv->next;
}

/******************************************************************************/
static void insertUnreducedVectorAfter(ngs_t *ngs, uV_t *base, uV_t *uv)
{
  uV_t *next = unreducedSuccessor(ngs, base);
  uv->prev = base;
  uv->next = next;
  if (next != NULL)
    next->prev = uv;
  if (base == NULL)
    ngs->unreducedHeap = uv;
  else
    base->next = uv;
  return;
}

/******************************************************************************/
void insertUnreducedVector(ngs_t *ngs, uV_t *uv)
{
  register uV_t *base = NULL;
  register uV_t *succ;
  while ((succ = unreducedSuccessor(ngs,base)) &&
    vectorLessThan(uv->gv, succ->gv))
    base = succ;
  insertUnreducedVectorAfter(ngs, base, uv);
  return;
}

/*****
 * 1 on error
 **************************************************************************/
int insertNewUnreducedVector(ngs_t *ngs, gV_t *gv)
{
  uV_t *uv = unreducedVector(ngs, gv);
  if (!uv) return 1;
  insertUnreducedVector(ngs, uv);
  return 0;
}

/******************************************************************************/
void unlinkUnreducedVector(ngs_t *ngs, uV_t *uv)
{
  uV_t *uv1;
  uv1 = uv->prev;
  if (uv1 == NULL)
    ngs->unreducedHeap = uv->next;
  else
    uv1->next = uv->next;
  uv1 = uv->next;
  if (uv1 != NULL)
    uv1->prev = uv->prev;
  uv->prev = NULL; uv->next = NULL;
  return;
}

/*****
 * NULL on error
 **************************************************************************/
rV_t *reducedVector(gV_t *gv, group_t *group)
{
  rV_t *rv = (rV_t *) malloc(sizeof(rV_t));
  if (!rv)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  rv->gv = gv;
  rv->node = NULL; rv->next = NULL; rv->prev = NULL;
  return rv;
}

/******
 * 1 on error
 *************************************************************************/
int processNewFlaggedGenerator(nFgs_t *nFgs, PTR w, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  gV_t *gv = popGeneralVector(ngs);
  if (!gv) return 1;
  /* gv->radical is set to true on creation; set to false below */
  PTR w_tmp = gv->w;
  gv->w = w;
  findLeadingMonomial(gv, ngs->r, group);
  gv->w = w_tmp;
  if (gv->dim != ZERO_BLOCK)
  {
    memcpy(gv->w, w, (FfCurrentRowSize*ngs->r));
    gv->radical = false;
    /* false means: not known to be in radical of kernel */
    if (makeVectorMonic(ngs, gv)) return 1;
    if (insertNewUnreducedVector (ngs, gv)) return 1;
  }
  else pushGeneralVector(ngs, gv);
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
int nFgsInitializeVectors(nFgs_t *nFgs, PTR mat, long n, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  PTR w;
  register long i;
  for (w = mat, i = 0; i < n; i++, w = FfGetPtr(w, ngs->r))
    if (processNewFlaggedGenerator(nFgs, w, group)) return 1;
  return 0;
}

/******
 * 1 on error
 *************************************************************************/
int nRgsInitializeVectors(nRgs_t *nRgs, PTR im, PTR pre, long n,
  group_t *group)
{
  ngs_t *ngs = nRgs->ngs;
  PTR w, m, w_tmp;
  gV_t *gv;
  register long i;
  for (w = im, m = pre, i = 0; i < n;
    i++, w = FfGetPtr(w, ngs->r), m = FfGetPtr(m, ngs->s))
  {
    gv = popGeneralVector(ngs);
    if (!gv)
    { MTX_ERROR("Error in popGeneralVector");
      return 1;
    }
    /* gv->radical is true by default; superfluous for nRgs */
    w_tmp = gv->w;
    gv->w = w;
    findLeadingMonomial(gv, ngs->r, group);
    gv->w = w_tmp;
    if (gv->dim == ZERO_BLOCK)
    {
      pushGeneralVector(ngs, gv);
      if (processNewFlaggedGenerator (nRgs->ker, m, group)) return MTX_ERROR("Error in processNewFlaggedGenerator"),1;
    }
    else
    {
      memcpy(gv->w, w, (FfCurrentRowSize*ngs->r));
      memcpy(FfGetPtr(gv->w, ngs->r), m, (FfCurrentRowSize*ngs->s));
      if (makeVectorMonic(ngs, gv)) return MTX_ERROR("Error in makeVectorMonic"),1;
      if (insertNewUnreducedVector(ngs, gv)) return  MTX_ERROR("Error in insertNewUnreducedVector"),1;
    }
  }
  return 0;
}

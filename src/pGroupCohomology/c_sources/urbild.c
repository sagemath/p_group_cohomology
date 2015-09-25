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
*  urbild.c : Miscellaneous subfree module routines, new storage methods
*  Author: David J Green
*  First version: 13 March 2000 from widget.c
*/

#include "nDiag.h"
#include "slice_decls.h"
#include "meataxe.h"

/******************************************************************************/
void saveMinimalGenerators(nFgs_t *nFgs, char *outfile, group_t *group)
/* corrupts nFgs (REALLY?? 13.03.00)*/
{
  ngs_t *ngs = nFgs->ngs;
  FILE *fp;
  long nor = 0;
  gV_t *gv;
  rV_t *rv;
  fp = writehdrplus(outfile, zfl, 0, group->nontips);
  if (!fp) OtherError("saveMinimalGenerators: opening outfile");
  for (rv = ngs->firstReduced; rv; rv = rv->next)
  {
    gv = rv->gv;
    if (!gv->radical) /* i.e. this rv a min generator */
    {
      if (zwritevec(fp,gv->w,ngs->r) != ngs->r)
        OtherError("saveMinimalGenerators: writing vectors");
      nor += ngs->r;
    }
  }
  alterhdrplus(fp,nor);
  fclose(fp);
  return;
}

/******************************************************************************/
matrix_t *getMinimalGenerators(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  long nor = 0;
  long noc = group->nontips;
  long i;
  gV_t *gv;
  rV_t *rv;
  matrix_t *OUT;
  PTR p;
  register char *b;
  /* fp = writehdrplus(outfile, zfl, 0, group->nontips);
   i.e. zfl is the fl, group->nontips is noc, and nor will be determined now:
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
  OUT = matalloc(zfl, nor, noc);
  p = (PTR)OUT->d;
  for (rv = ngs->firstReduced; rv; rv = rv->next)
  {
    gv = rv->gv;
    if (!gv->radical) /* i.e. this rv a min generator */
    {
      /* if (zwritevec(fp,gv->w,ngs->r) != ngs->r)
        OtherError("saveMinimalGenerators: writing vectors");
      */
      b = (char *)gv->w;
      for (i = 0; i < ngs->r; ++i)
	{ memcpy(p,b,zrowsize);
	  b += zrowsize;
	  zsteprow(&(p));
	}
    }
  }
  return OUT;
}

/******************************************************************************/
void saveUrbildGroebnerBasis(nRgs_t *nRgs, char *outfile, group_t *group)
{
  ngs_t *ngs = nRgs->ngs;
  FILE *fp;
  long nor = 0;
  long t = ngs->r + ngs->s;
  gV_t *gv;
  rV_t *rv;
  fp = writehdrplus(outfile, zfl, 0, group->nontips);
  if (!fp) OtherError("saveUrbildGB: opening outfile");
  for (rv = ngs->firstReduced; rv; rv = rv->next)
  {
    gv = rv->gv;
    if (zwritevec(fp, gv->w, t) != t)
      OtherError("saveUrbildGB: writing vectors");
    nor += t;
  }
  alterhdrplus(fp,nor);
  fclose(fp);
  return;
}

/******************************************************************************/
inline long numberOfHeadyVectors(ngs_t *ngs)
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

/******************************************************************************
static long targetPnontips(ngs_t *ngs, group_t *group)
{
  return (ngs->r * group->nontips - ngs->targetRank);
}
*/
#if !defined(targetPnontips)
#define targetPnontips(ngs,group) ((ngs)->r * (group)->nontips - (ngs)->targetRank)
#endif

/******************************************************************************
Apparently this function is redundant and used only in one place - remove it!
long countGenerators(nFgs_t *nFgs)
{
  return numberOfHeadyVectors(nFgs->ngs);
}
*/

/******************************************************************************
Apparently this function is redundant and used only in one place - remove it!
long headyDim(nFgs_t *nFgs)
{
  return dimensionOfDeepestHeady(nFgs->ngs);
}
*/

/*******************************************************************************
* static long vectorPosition(rV_t *here)
* {
  long n;
  rV_t *rv;
  for (n = 0, rv = here; rv; n++, rv = rv->prev);
  return n;
* }
*/

/******************************************************************************/
void saveNFgs(nFgs_t *nFgs, group_t *group, char *outfile, char *markfile)
{
  ngs_t *ngs = nFgs->ngs;
  FILE *fp;
  long nor;
  rV_t *rv;
  fp = writehdrplus(outfile, zfl, 0, group->nontips);
  if (!fp) OtherError("saveNFgs: opening outfile");
  for (rv = ngs->firstReduced, nor = 0; rv ; rv = rv->next, nor += ngs->r)
    if (zwritevec(fp,rv->gv->w,ngs->r) != ngs->r)
      OtherError("saveNFgs: writing vectors");
  alterhdrplus(fp,nor);
  fclose(fp);
  fp = fopen(markfile, "w");
  if (!fp) OtherError("saveNFgs: opening markfile");
  for (rv = ngs->firstReduced; rv ; rv = rv->next)
    fprintf(fp, "%c", rv->gv->radical ? 'R' : 'H');
  fprintf(fp,"\n");
  fclose(fp);
  /* printf("marks saved to %s\n", markfile); */
  return;
}

/******************************************************************************/
void saveNRgs(nRgs_t *nRgs, group_t *group, char *outfile, char *markfile)
{
  ngs_t *ngs = nRgs->ngs;
  FILE *fp;
  long nor;
  rV_t *rv;
  fp = writehdrplus(outfile, zfl, 0, group->nontips);
  if (!fp) OtherError("saveNRgs: opening outfile");
  for (rv = ngs->firstReduced, nor = 0; rv ; rv = rv->next, nor += ngs->r)
    if (zwritevec(fp,rv->gv->w,ngs->r) != ngs->r)
      OtherError("saveNRgs: writing vectors");
  alterhdrplus(fp,nor);
  fclose(fp);
  fp = writehdrplus(markfile, zfl, 0, group->nontips);
  if (!fp) OtherError("saveNRgs: opening markfile");
  for (rv = ngs->firstReduced, nor = 0; rv ; rv = rv->next, nor += ngs->s)
    if (zwritevec(fp, ptrPlus(rv->gv->w, ngs->r), ngs->s) != ngs->s)
      OtherError("saveNRgs: writing marks");
  alterhdrplus(fp,nor);
  fclose(fp);
  /* printf("preimages saved to %s\n", markfile); */
  return;
}

/******************************************************************************/
static ngs_t *ngsAllocation(long r, long s, group_t *group, char *stem)
{
  ngs_t *ngs = (ngs_t *) malloc(sizeof(ngs_t));
  if (!ngs) AllocationError("ngsAllocation");
  ngs->r = r;
  ngs->s = s;
  ngs->firstReduced = NULL;
  ngs->lastReduced = NULL;
  ngs->unreducedHeap = NULL;
  ngs->pnontips = r * group->nontips;
  ngs->expDim = NOTHING_TO_EXPAND;
  ngs->targetRank = RANK_UNKNOWN;
  ngs->gVwaiting = NULL;
  createWordForest(ngs, group);
  ngs->dimLoaded = NONE;
  ngs->blockLoaded = NONE;
  ngs->blockSize = BLOCK_SIZE;
  ngs->thisBlock = zalloc(ngs->blockSize * (r + s));
  ngs->theseProds = zalloc(ngs->blockSize * (r + s));
  ngs->w = zalloc(r + s);
  if (!ngs->thisBlock || !ngs->theseProds || !ngs->w)
    AllocationError("ngsAlloc: 2");
  strcpy(ngs->stem, stem);
  return ngs;
}

/******************************************************************************/
nFgs_t *nFgsAllocation(group_t *group, long r, char *stem)
{
  char thisStem[MAXLINE];
  nFgs_t *nFgs = (nFgs_t *) malloc(sizeof(nFgs_t));
  if (!nFgs) AllocationError("nFgsAllocation");
  sprintf(thisStem, "%sf", stem);
  nFgs->ngs = ngsAllocation(r, 0, group, thisStem);
  nFgs->finished = false;
  nFgs->nRgsUnfinished = false;
  nFgs->max_unfruitful = MAX_UNFRUITFUL;
  return nFgs;
}

/******************************************************************************/
nRgs_t *nRgsAllocation(group_t *group, long r, long s, char *stem)
{
  char thisStem[MAXLINE];
  nRgs_t *nRgs = (nRgs_t *) malloc(sizeof(nRgs_t));
  if (!nRgs) AllocationError("nRgsAllocation");
  sprintf(thisStem, "%sr", stem);
  nRgs->ngs = ngsAllocation(r, s, group, thisStem);
  nRgs->ker = nFgsAllocation(group, s, stem);
  nRgs->overshoot = MAX_OVERSHOOT;
  return nRgs;
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
static void freeNgs(ngs_t *ngs)
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
  if (w1->dim > w2->dim) return true;
  if (w1->dim < w2->dim) return false;
  if (w1->block > w2->block) return true;
  if (w1->block < w2->block) return false;
  if (w1->len < w2->len) return true;
  if (w1->len > w2->len) return false;
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

/******************************************************************************/
static void lowerExpDimIfNecessary(ngs_t *ngs, long d)
{
  if (ngs->expDim == NO_BUCHBERGER_REQUIRED) return;
  if (d != ngs->dimLoaded) OtherError("lEDIN: d not the current dimension\n");
  if (ngs->expDim == NOTHING_TO_EXPAND)
  {
    ngs->expDim = d;
    return;
  }
  if (ngs->expDim > d)
  {
    destroyExpansionSliceFile(ngs);
    ngs->expDim = d;
  }
  return;
}

/******************************************************************************/
void insertReducedVector(ngs_t *ngs, rV_t *rv)
/* See expansion routines for info on expDim */
{
  rV_t *base = ngs->lastReduced;
  while (base && vectorLessThan(base->gv, rv->gv))
    base = base->prev;
  insertReducedVectorAfter(ngs, base, rv);
  rv->expDim = rv->gv->dim;
  lowerExpDimIfNecessary(ngs, rv->expDim);
  return;
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

/******************************************************************************/
uV_t *unreducedVector(ngs_t *ngs, gV_t *gv)
{
  uV_t *uv = (uV_t *) malloc(sizeof(uV_t));
  if (!uv) AllocationError("unreducedVector");
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

/******************************************************************************/
void insertNewUnreducedVector(ngs_t *ngs, gV_t *gv)
{
  uV_t *uv = unreducedVector(ngs, gv);
  insertUnreducedVector(ngs, uv);
  return;
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

/******************************************************************************/
rV_t *reducedVector(gV_t *gv, group_t *group)
{
  rV_t *rv = (rV_t *) malloc(sizeof(rV_t));
  if (!rv) AllocationError("reducedVector");
  rv->gv = gv;
  rv->node = NULL; rv->next = NULL; rv->prev = NULL;
  return rv;
}

/******************************************************************************/
void processNewFlaggedGenerator(nFgs_t *nFgs, PTR w, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  gV_t *gv = popGeneralVector(ngs);
  /* gv->radical is set to true on creation; set to false below */
  PTR w_tmp = gv->w;
  gv->w = w;
  findLeadingMonomial(gv, ngs->r, group);
  gv->w = w_tmp;
  if (gv->dim != ZERO_BLOCK)
  {
    memcpy(gv->w, w, zsize(ngs->r));
    gv->radical = false;
    /* false means: not known to be in radical of kernel */
    makeVectorMonic(ngs, gv);
    insertNewUnreducedVector (ngs, gv);
  }
  else pushGeneralVector(ngs, gv);
  return;
}

/******************************************************************************/
void nFgsInitializeVectors(nFgs_t *nFgs, PTR mat, long n, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  PTR w;
  register long i;
  for (w = mat, i = 0; i < n; i++, zadvance(&w, ngs->r))
    processNewFlaggedGenerator(nFgs, w, group);
  return;
}

/******************************************************************************/
void nRgsInitializeVectors(nRgs_t *nRgs, PTR im, PTR pre, long n,
  group_t *group)
{
  ngs_t *ngs = nRgs->ngs;
  PTR w, m, w_tmp;
  gV_t *gv;
  register long i;
  for (w = im, m = pre, i = 0; i < n;
    i++, zadvance(&w, ngs->r), zadvance(&m, ngs->s))
  {
    gv = popGeneralVector(ngs);
    /* gv->radical is true by default; superfluous for nRgs */
    w_tmp = gv->w;
    gv->w = w;
    findLeadingMonomial(gv, ngs->r, group);
    gv->w = w_tmp;
    if (gv->dim == ZERO_BLOCK)
    {
      pushGeneralVector(ngs, gv);
      processNewFlaggedGenerator (nRgs->ker, m, group);
    }
    else
    {
      memcpy(gv->w, w, zsize(ngs->r));
      memcpy(ptrPlus(gv->w, ngs->r), m, zsize(ngs->s));
      makeVectorMonic(ngs, gv);
      insertNewUnreducedVector(ngs, gv);
    }
  }
  return;
}

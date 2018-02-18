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
* aufloesung.c : resolution-related routines for minAufl
* First version: 15 March 2000 from resol.c
* Author: David J Green
*/

#include "modular_resolution.h"
#include "meataxe.h"
#include "aufnahme.h"
#include "fp_decls.h"
#define LONGLINE 320
MTX_DEFINE_FILE_INFO

/******************************************************************************/
char *differentialFile(resol_t *resol, long n)
/* String returned must be used at once, never reused, never freed. */
/* Represents d_n : P_n -> P_{n-1} */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%sd%02ld.bin", resol->stem, n);
  return buffer;
}

/******************************************************************************/
char *urbildGBFile(resol_t *resol, long n)
/* String returned must be used at once, never reused, never freed. */
/* Represents urbild Groebner basis for d_n : P_n -> P_{n-1} */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%sd%02ld.ugb", resol->stem, n);
  return buffer;
}

/******************************************************************************/
char *resolDir(long Gsize)
/* String returned must be used at once, never reused, never freed. */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%ldres", Gsize);
  return buffer;
}

/******************************************************************************/
char *resolStem(long Gsize, char *Gname)
/* String returned must be used at once, never reused, never freed. */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%s/%s", resolDir(Gsize), Gname);
  return buffer;
}

/***
 * NULL on error
 ****************************************************************************/
static resol_t *innerNewResolutionRecord (void)
{
  resol_t *resol = (resol_t *) malloc(sizeof(resol_t));
  if (!resol)
  { MTX_ERROR1("%E",MTX_ERR_NOMEM);
    return NULL;
  }
  resol->group = NULL;
  resol->stem = NULL;
  resol->moduleStem = NULL;
  resol->numproj = -1;
  resol->numproj_alloc = -1;
  resol->projrank = NULL;
  resol->Imdim = NULL;
  return resol;
}

/*****
 * NULL on error
 **************************************************************************/
resol_t *newResolutionRecord (void)
{
  resol_t *resol = innerNewResolutionRecord();
  if (!resol) return NULL;
  resol->group = newGroupRecord();
  if (!resol->group)
  { freeResolutionRecord(resol);
    return NULL;
  }
  return resol;
}

/******************************************************************************/
static void setDimIm(resol_t *resol, long n)
{
  resol->Imdim[n] = resol->projrank[n-1] * resol->group->nontips
                    - resol->Imdim[n-1];
  return;
}

/****
 * 1 on error
 ***************************************************************************/
static int initializeResolSizeArrays(resol_t *resol)
{
  long alloc = NUMPROJ_BASE;
  long *projrank = newLongArray(alloc + 1);
  if (!projrank) return 1;
  long *Imdim = newLongArray(alloc + 2);
  if (!Imdim)
  { free(projrank);
    return 1;
  }
  projrank[0] = 1;
  Imdim[0] = 1;
  resol->projrank = projrank;
  resol->Imdim = Imdim;
  resol->numproj_alloc = alloc;
  resol->numproj = 0;
  setDimIm(resol, 1);
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
static int ensureResolSizeArraysLargeEnough(resol_t *resol, long N)
{
  long alloc, alloc_old = resol->numproj_alloc;
  long *projrank_old = resol->projrank, *Imdim_old = resol->Imdim;
  long *projrank, *Imdim;
  if (N <= alloc_old) return 0;
  for (alloc = alloc_old; alloc < N; alloc += NUMPROJ_INCREMENT);
  projrank = newLongArray(alloc + 1);
  if (!projrank) return 1;
  Imdim = newLongArray(alloc + 2);
  if (!Imdim)
  { free(projrank);
    return 1;
  }
  memcpy(projrank, projrank_old, (alloc + 1) * sizeof(long));
  memcpy(Imdim, Imdim_old, (alloc + 2) * sizeof(long));
  resol->projrank = projrank;
  resol->Imdim = Imdim;
  resol->numproj_alloc = alloc;
  free(projrank_old);
  free(Imdim_old);
  return 0;
}

/****
 * NULL on error
 ***************************************************************************/
resol_t *newResolWithGroupLoaded (char *RStem, char *GStem, long N)
{
  resol_t *resol;
  resol = innerNewResolutionRecord();
  if (!resol) return NULL;
  resol->group = fullyLoadedGroupRecord(GStem);
  if (!resol->group) return NULL;
  if ((resol->stem = mtx_strdup(RStem)) == NULL) return NULL;
  if (initializeResolSizeArrays(resol)) return NULL;
  ensureResolSizeArraysLargeEnough(resol, N);
  return resol;
}

/******************************************************************************/
void freeResolutionRecord (resol_t *resol)
{
  if (resol->Imdim) free(resol->Imdim);
  if (resol->group) freeGroupRecord(resol->group);
  if (resol->stem) free(resol->stem);
  if (resol->moduleStem) free(resol->moduleStem);
  if (resol->projrank) free(resol->projrank);
  free (resol);
  return;
}

/***
 * -1 on error
 ****************************************************************************/
long rankProj(resol_t *resol, long n)
{
  if (n < 0)
  { MTX_ERROR("non-negative degree expected"); return -1;}
  if (n > resol->numproj)
  {
    MTX_ERROR1("not yet known in that degree: %E", MTX_ERR_INCOMPAT);
    return -1;
  }
  return resol->projrank[n];
}

/*** -1 on error
 ****************************************************************************/
long dimIm(resol_t *resol, long n)
{
  if (n < 0 || n > resol->numproj + 1)
  {
      MTX_ERROR1("%E", MTX_ERR_RANGE);
      return -1;
  }
  return resol->Imdim[n];
}

/**** 1 on error
 ***************************************************************************/
int setRankProj(resol_t *resol, long n, long r)
{
  if (n != resol->numproj + 1)
  { MTX_ERROR1("unexpected degree: %E", MTX_ERR_BADARG);
    return 1;
  }
  if (r < 0)
  { MTX_ERROR1("negative rank impossible: %E", MTX_ERR_INCOMPAT);
    return 1;
  }
  ensureResolSizeArraysLargeEnough(resol, n);
  resol->projrank[n] = r;
  resol->numproj = n;
  setDimIm(resol, n+1);
  return 0;
}

/****
 * 1 in error
 ***************************************************************************/
int setRankProjCoverForModule(resol_t *resol, long rkP0, long dimM)
{
  if (resol->numproj != 0)
  { MTX_ERROR1("numproj not zero: %E", MTX_ERR_INCOMPAT);
    return 1;
  }
  resol->Imdim[0] = dimM;
  resol->numproj = -1;
  return setRankProj(resol, 0, rkP0);
}

/****
 * NULL on error
 ***************************************************************************/
nRgs_t *urbildSetup(resol_t *resol, long n, PTR mat, long numnor)
/* mat should be a block of length numnor = num * nor */
{
  char thisStem[MAXLINE];
  nRgs_t *nRgs;
  ngs_t *ngs;
  group_t *group = resol->group;
  long r = rankProj(resol, n-1);
  if (r==-1) return NULL;
  long s = rankProj(resol, n);
  if (s==-1) return NULL;
  long nor = r+s;
  long num = numnor / nor;
  if (numnor != num * nor)
  {
      MTX_ERROR("Theoretical Error");
      return NULL;
  }
  sprintf(thisStem, "%sd%ldu", resol->stem, n);
  nRgs = nRgsAllocation(group, r, s, thisStem);
  if (!nRgs) return NULL;
  ngs = nRgs->ngs;
  ngs->expDim = NO_BUCHBERGER_REQUIRED;
  ngs->targetRank = dimIm(resol, n);
  if (ngs->targetRank == -1)
  {
      freeNRgs(nRgs);
      return NULL;
  }
  nRgs->ker->ngs->targetRank = dimIm(resol, n+1);
  if (nRgs->ker->ngs->targetRank == -1)
  {
      freeNRgs(nRgs);
      return NULL;
  }
  if (nRgsAssertReducedVectors(nRgs, mat, num, group))
  {
      freeNRgs(nRgs);
      return NULL;
  }
  return nRgs;
}

/****
 * NULL on error
 ***************************************************************************/
nRgs_t *nRgsStandardSetup(resol_t *resol, long n, PTR mat)
/* mat should be a block of length r * s */
{
  register long i;
  PTR ptr;
  char thisStem[MAXLINE];
  FEL minus_one = FfNeg(FF_ONE);
  group_t *group = resol->group;
  long r = rankProj(resol, n-1);
  if (r==-1) return NULL;
  long s = rankProj(resol, n);
  if (s==-1) return NULL;
  nRgs_t *nRgs;
  ngs_t *ngs;
  register PTR pre = FfAlloc(s * s); /* Initialization guaranteed */
  if (!pre)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  sprintf(thisStem, "%sd%ld", resol->stem, n);
  nRgs = nRgsAllocation(group, r, s, thisStem);
  if (!nRgs) return NULL;
  ngs = nRgs->ngs;
  register long s1 = s+1;
  for (i = 1, ptr = pre; i <= s; i++, ptr = FfGetPtr(ptr, s1))
    FfInsert(ptr, 0, minus_one);
  if (nRgsInitializeVectors(nRgs, mat, pre, s, group))
  {
      /*MTX_ERROR("Error initializing nRgs vectors");*/
      return NULL;
  }
  free(pre);
  ngs->targetRank = dimIm(resol, n);
  if (ngs->targetRank == -1)
  { freeNRgs(nRgs);
    MTX_ERROR("ngs->targetRank == -1: Theoretical error");
    return NULL;
  }
  nRgs->ker->ngs->targetRank = dimIm(resol, n+1);
  if (nRgs->ker->ngs->targetRank == -1)
  { freeNRgs(nRgs);
    MTX_ERROR("nRgs->ker->ngs->targetRank == -1: Theoretical error");
    return NULL;
  }
  /* nRgs->ker->ngs->targetRank = RANK_UNKNOWN; */
  return nRgs;
}

/******************************************************************************/
static char dateCommand[LONGLINE];

/******************************************************************************/
void initializeDateCommand(char *stem)
{
  sprintf(dateCommand, "date >> %s.chat", stem);
  return;
}

/******************************************************************************/
char *numberedFile(long n, char *stem, char *extension)
/* String returned must be used at once, never reused, never freed. */
/* extension WITHOUT dot */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%s%ld.%s", stem, n, extension);
  return buffer;
}

/****
 * NULL on error
 ***************************************************************************/
Matrix_t *makeFirstDifferential(resol_t *resol)
{
  long i;
  PTR ptr;
  group_t *group = resol->group;
  long dimP1 = 0;
  Matrix_t *pres;
  switch(group->ordering)
  {
  case 'R' :
    dimP1 = group->arrows;
    break;
  case 'J' :
    dimP1 = group->dS[2] - 1;
    break;
  default :
    MTX_ERROR("not implemented for this ordering");
    return NULL;
  }
  pres = MatAlloc(FfOrder, dimP1, group->nontips);
  if (!pres)
  {
      MTX_ERROR1("%E", MTX_ERR_NOMEM);
      return NULL;
  }
  for (i = 1, ptr = pres->Data; i <= dimP1; i++, FfStepPtr(&ptr))
    FfInsert(ptr, i, FF_ONE);
  if (setRankProj(resol, 1, dimP1))
  { MatFree(pres);
    return NULL;
  }
  return pres;
}

/****
 * NULL on error
 ***************************************************************************/
nRgs_t *loadDifferential(resol_t *resol, long n)
{
  nRgs_t *nRgs;
  Matrix_t *pres = MatLoad(differentialFile(resol, n));
  if (!pres)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  nRgs = nRgsStandardSetup(resol, n, pres->Data);
  MatFree(pres);
  return nRgs;
}

/****
 * NULL on error
 ***************************************************************************/
nRgs_t *loadUrbildGroebnerBasis(resol_t *resol, long n)
{
  nRgs_t *nRgs;
  Matrix_t *pres = MatLoad(urbildGBFile(resol, n));
  if (!pres)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  nRgs = urbildSetup(resol, n, pres->Data, pres->Nor);
  MatFree(pres);
  return nRgs;
}

/****
 * 1 on error
 ***************************************************************************/
static int readThisProjective(resol_t *resol, long n)
{
  long rs, r;
  r = rankProj(resol, n-1);
  if (r==-1) return 1;
  rs = numberOfRowsStored(differentialFile(resol, n));
  if (rs==-1) return 1;
  if (rs % r != 0)
  { MTX_ERROR("theoretical error");
    return 1;
  }
  return setRankProj(resol, n, rs/r);
}

/******************************************************************************/
void readKnownResolution(resol_t *resol, long N)
{
  long n;
  for (n = 1; n <= N; n++)
    readThisProjective(resol, n);
  return;
}

/****
 * 1 on error
 ***************************************************************************/
int innerPreimages(nRgs_t *nRgs, PTR images, long num, group_t *group,
  PTR preimages)
/* Assumes urbildGB already loaded */
/* images should be a block of length num * ngs->r */
/* preimages should be a block of length num * ngs->s, INITIALIZED TO ZERO */
/* Places result in preimages */
{
  ngs_t *ngs = nRgs->ngs;
  register long i;
  PTR tmp;
  register gV_t *gv;
  register uV_t *uv;
  for (i = 0; i < num; i++)
  {
    gv = popGeneralVector(ngs);
    if (!gv) return 1;
    tmp = gv->w;
    gv->w = FfGetPtr(images, i * ngs->r);
    findLeadingMonomial(gv, ngs->r, group);
    gv->w = tmp;
    if (gv->dim == ZERO_BLOCK)
    {
      /* This image is zero, which of course has preimage zero */
      pushGeneralVector(ngs, gv);
    }
    else
    {
      memcpy(gv->w, FfGetPtr(images, i * ngs->r), (FfCurrentRowSize*ngs->r));
      /* That gv->w is initialized is very likely, but not absolutely certain */
      /*initializeRows(FfGetPtr(gv->w, ngs->r), ngs->s);*/
      memset(FfGetPtr(gv->w, ngs->r), 0, FfCurrentRowSize*ngs->s);
      uv = unreducedVector(ngs, gv);
      if (!uv) return 1;
      uv->index = i;
      insertUnreducedVector(ngs, uv);
    }
  }
  return urbildAufnahme(nRgs, group, preimages);
}

/****
 * 1 on error
 ***************************************************************************/
int makeThisDifferential(resol_t *resol, long n)
/* n must be at least two */
{
  group_t *G = resol->group;
  nRgs_t *nRgs = loadDifferential(resol, n-1);
  nFgs_t *ker = nRgs->ker;
  if (nRgsBuchberger(nRgs, G)) return 1;
  if (setRankProj(resol, n, numberOfHeadyVectors(ker->ngs)))
  {
      freeNRgs(nRgs);
      return 1;
  }
  if (saveMinimalGenerators(ker, differentialFile(resol, n), G)) return 1;
  if (saveUrbildGroebnerBasis(nRgs, urbildGBFile(resol, n-1), G)) return 1;
  freeNRgs(nRgs);
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
static int makeThisCohringDifferential(resol_t *resol, long n)
/* Know resolving trivial mod, so can use makeFirstDifferential if n=1 */
{
  if (n == 1)
    return (makeFirstDifferential(resol))? 0 : 1;
  return makeThisDifferential(resol, n);
}

/*****
 * 1 on error
 **************************************************************************/
int readOrConstructThisProjective(resol_t *resol, long n)
{
  if (n != resol->numproj + 1)
  {
      MTX_ERROR1("%E", MTX_ERR_BADARG);
      return 1;
  }
  if (fileExists(differentialFile(resol, n)))
  {
    return readThisProjective(resol, n);
  }
  else
  { return makeThisCohringDifferential(resol, n);
  }
}

/***
 * 1 on error
 ****************************************************************************/
int ensureThisProjectiveKnown(resol_t *resol, long n)
{
  long d;
  while ((d = resol->numproj + 1) <= n)
    if (readOrConstructThisProjective(resol, d)) return 1;
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int ensureThisUrbildGBKnown(resol_t *resol, long n)
{
  if (n < 1 || n > resol->numproj)
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
  if (fileExists(urbildGBFile(resol, n))) return 0;
  return makeThisDifferential(resol, n+1);
}


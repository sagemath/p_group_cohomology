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
* aufloesung.c : resolution-related routines for minAufl
* First version: 15 March 2000 from resol.c
* Author: David J Green
*/

#include "aufloesung.h"
#include "meataxe.h"
#define LONGLINE 320

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

/******************************************************************************/
static resol_t *innerNewResolutionRecord (void)
{
  resol_t *resol = (resol_t *) malloc(sizeof(resol_t));
  if (!resol) AllocationError("innerNewResolutionRecord");
  resol->group = NULL;
  resol->stem = NULL;
  resol->moduleStem = NULL;
  resol->numproj = -1;
  resol->numproj_alloc = -1;
  resol->projrank = NULL;
  resol->Imdim = NULL;
  return resol;
}

/******************************************************************************/
resol_t *newResolutionRecord (void)
{
  resol_t *resol = innerNewResolutionRecord();
  resol->group = newGroupRecord();
  return resol;
}

/******************************************************************************/
static void setDimIm(resol_t *resol, long n)
{
  resol->Imdim[n] = resol->projrank[n-1] * resol->group->nontips
                    - resol->Imdim[n-1];
  return;
}

/******************************************************************************/
static void initializeResolSizeArrays(resol_t *resol)
{
  long alloc = NUMPROJ_BASE;
  long *projrank = newLongArray(alloc + 1);
  long *Imdim = newLongArray(alloc + 2);
  projrank[0] = 1;
  Imdim[0] = 1;
  resol->projrank = projrank;
  resol->Imdim = Imdim;
  resol->numproj_alloc = alloc;
  resol->numproj = 0;
  setDimIm(resol, 1);
  return;
}

/******************************************************************************/
static void ensureResolSizeArraysLargeEnough(resol_t *resol, long N)
{
  long alloc, alloc_old = resol->numproj_alloc;
  long *projrank_old = resol->projrank, *Imdim_old = resol->Imdim;
  long *projrank, *Imdim;
  if (N <= alloc_old) return;
  for (alloc = alloc_old; alloc < N; alloc += NUMPROJ_INCREMENT);
  projrank = newLongArray(alloc + 1);
  Imdim = newLongArray(alloc + 2);
  memcpy(projrank, projrank_old, (alloc + 1) << LONGSH);
  memcpy(Imdim, Imdim_old, (alloc + 2) << LONGSH);
  resol->projrank = projrank;
  resol->Imdim = Imdim;
  resol->numproj_alloc = alloc;
  free(projrank_old);
  free(Imdim_old);
  return;
}

/******************************************************************************/
resol_t *newResolWithGroupLoaded (char *RStem, char *GStem, long N)
{
  resol_t *resol;
  resol = innerNewResolutionRecord();
  resol->group = fullyLoadedGroupRecord(GStem);
  resol->stem = djg_strdup(RStem);
  initializeResolSizeArrays(resol);
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

/******************************************************************************/
long rankProj(resol_t *resol, long n)
{
  if (n < 0)
  { OtherError("rankProj: non-negative degree expected");}
  if (n > resol->numproj)
  {
    OtherError("rankProj: not yet known in that degree");
  }
  return resol->projrank[n];
}

/******************************************************************************/
long dimIm(resol_t *resol, long n)
{
  if (n < 0 || n > resol->numproj + 1)
    OtherError("dimIm: degree out of range");
  return resol->Imdim[n];
}

/******************************************************************************/
void setRankProj(resol_t *resol, long n, long r)
{
  if (n != resol->numproj + 1) OtherError("setRankProj: unexpected degree");
  if (r < 0) OtherError("setRankProj: negative rank impossible");
  ensureResolSizeArraysLargeEnough(resol, n);
  resol->projrank[n] = r;
  resol->numproj = n;
  setDimIm(resol, n+1);
  return;
}

/******************************************************************************/
void setRankProjCoverForModule(resol_t *resol, long rkP0, long dimM)
{
  if (resol->numproj != 0)
    OtherError("setRankProjCoverForModule: numproj not zero");
  resol->Imdim[0] = dimM;
  resol->numproj = -1;
  setRankProj(resol, 0, rkP0);
  return;
}

/******************************************************************************/
nRgs_t *urbildSetup(resol_t *resol, long n, PTR mat, long numnor)
/* mat should be a block of length numnor = num * nor */
{
  char thisStem[MAXLINE];
  nRgs_t *nRgs;
  ngs_t *ngs;
  group_t *group = resol->group;
  long r = rankProj(resol, n-1);
  long s = rankProj(resol, n);
  long nor = r+s;
  long num = numnor / nor;
  if (numnor != num * nor) OtherError("urbildSetup: Theoretical Error");
  sprintf(thisStem, "%sd%ldu", resol->stem, n);
  nRgs = nRgsAllocation(group, r, s, thisStem);
  ngs = nRgs->ngs;
  ngs->expDim = NO_BUCHBERGER_REQUIRED;
  ngs->targetRank = dimIm(resol, n);
  nRgs->ker->ngs->targetRank = dimIm(resol, n+1);
  nRgsAssertReducedVectors(nRgs, mat, num, group);
  return nRgs;
}

/******************************************************************************/
nRgs_t *nRgsStandardSetup(resol_t *resol, long n, PTR mat)
/* mat should be a block of length r * s */
{
  register long i;
  PTR ptr;
  char thisStem[MAXLINE];
  FEL minus_one = zsub(F_ZERO, F_ONE);
  group_t *group = resol->group;
  long r = rankProj(resol, n-1);
  long s = rankProj(resol, n);
  nRgs_t *nRgs;
  ngs_t *ngs;
  register PTR pre = zalloc(s * s); /* Initialization guaranteed */
  if (!pre) AllocationError("nRgsStandardSetup");
  sprintf(thisStem, "%sd%ld", resol->stem, n);
  nRgs = nRgsAllocation(group, r, s, thisStem);
  ngs = nRgs->ngs;
  for (i = 1, ptr = pre; i <= s; i++, zadvance(&ptr, s+1))
    zinsert(ptr, 1, minus_one);
  nRgsInitializeVectors(nRgs, mat, pre, s, group);
  free(pre);
  ngs->targetRank = dimIm(resol, n);
  nRgs->ker->ngs->targetRank = dimIm(resol, n+1);
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

/******************************************************************************/
matrix_t *makeFirstDifferential(resol_t *resol)
{
  long i;
  PTR ptr;
  group_t *group = resol->group;
  long dimP1 = 0;
  matrix_t *pres;
  switch(group->ordering)
  {
  case 'R' :
    dimP1 = group->arrows;
    break;
  case 'J' :
    dimP1 = group->dS[2] - 1;
    break;
  default :
    OtherError("makeFirstDifferential: not implemented for this ordering");
    break;
  }
  pres = matalloc(zfl, dimP1, group->nontips);
  if (!pres) AllocationError("makeFirstDifferential");
  for (i = 2, ptr = pres->d; i <= dimP1 + 1; i++, zsteprow(&ptr))
    zinsert(ptr, i, F_ONE);
  /*matsave(pres, differentialFile(resol, 1));
  matfree(pres);
  */
  setRankProj(resol, 1, dimP1);
  return pres;
}

/******************************************************************************/
nRgs_t *loadDifferential(resol_t *resol, long n)
{
  nRgs_t *nRgs;
  matrix_t *pres = matload(differentialFile(resol, n));
  if (!pres) AllocationError("loadDifferential");
  nRgs = nRgsStandardSetup(resol, n, pres->d);
  matfree(pres);
  return nRgs;
}

/******************************************************************************/
nRgs_t *loadUrbildGroebnerBasis(resol_t *resol, long n)
{
  nRgs_t *nRgs;
  matrix_t *pres = matload(urbildGBFile(resol, n));
  if (!pres) AllocationError("loadUrbildGroebnerBasis");
  nRgs = urbildSetup(resol, n, pres->d, pres->nor);
  matfree(pres);
  return nRgs;
}

/******************************************************************************/
static void readThisProjective(resol_t *resol, long n)
{
  long rs, r;
  r = rankProj(resol, n-1);
  rs = numberOfRowsStored(differentialFile(resol, n));
  if (rs % r != 0) OtherError("readThisProjective: theoretical error");
  setRankProj(resol, n, rs/r);
  return;
}

/******************************************************************************/
void readKnownResolution(resol_t *resol, long N)
{
  long n;
  for (n = 1; n <= N; n++)
    readThisProjective(resol, n);
  return;
}

/******************************************************************************/
static void initializeRows(PTR base, long nor)
{
  PTR p;
  register long i;
  for (p = base, i = 0; i < nor; i++, zsteprow(&p))
    zmulrow(p, F_ZERO);
  return;
}

/******************************************************************************/
void innerPreimages(nRgs_t *nRgs, PTR images, long num, group_t *group,
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
    tmp = gv->w;
    gv->w = ptrPlus(images, i * ngs->r);
    findLeadingMonomial(gv, ngs->r, group);
    gv->w = tmp;
    if (gv->dim == ZERO_BLOCK)
    {
      /* This image is zero, which of course has preimage zero */
      pushGeneralVector(ngs, gv);
    }
    else
    {
      memcpy(gv->w, ptrPlus(images, i * ngs->r), zsize(ngs->r));
      initializeRows(ptrPlus(gv->w, ngs->r), ngs->s);
      /* That gv->w is initialized is very likely, but not absolutely certain */
      uv = unreducedVector(ngs, gv);
      uv->index = i;
      insertUnreducedVector(ngs, uv);
    }
  }
  urbildAufnahme(nRgs, group, preimages);
  return;
}

/*******************************************************************************
* PTR preimages(nRgs_t *nRgs, PTR images, long num, group_t *group)
* ** Assumes urbildGB already loaded ** 
* ** images should be a block of length num * ngs->r **
* ** returns a block of length num * ngs->s **
* {
  * ngs_t *ngs = nRgs->ngs;
  * PTR preimages = zalloc(num * ngs->s);
  * ** Remember: zalloc initializes to zero **
  * if (!preimages) AllocationError("preimages"); 
  * innerPreimages(nRgs, images, num, group, preimages);
  * return preimages;
* }
*/

/******************************************************************************/
void makeThisDifferential(resol_t *resol, long n)
/* n must be at least two */
{
  group_t *G = resol->group;
  nRgs_t *nRgs = loadDifferential(resol, n-1);
  nFgs_t *ker = nRgs->ker;
  nRgsBuchberger(nRgs, G);
  // setRankProj(resol, n, countGenerators(ker));
  setRankProj(resol, n, numberOfHeadyVectors(ker->ngs));
  saveMinimalGenerators(ker, differentialFile(resol, n), G);
  saveUrbildGroebnerBasis(nRgs, urbildGBFile(resol, n-1), G);
  freeNRgs(nRgs);
  return;
}

/******************************************************************************/
static void makeThisCohringDifferential(resol_t *resol, long n)
/* Know resolving trivial mod, so can use makeFirstDifferential if n=1 */
{
  if (n == 1)
    makeFirstDifferential(resol);
  else
    makeThisDifferential(resol, n);
  return;
}

/******************************************************************************/
void readOrConstructThisProjective(resol_t *resol, long n)
{
  if (n != resol->numproj + 1)
    OtherError("readOrConstructThisProjective: invalid data");
  if (fileExists(differentialFile(resol, n)))
  {
    readThisProjective(resol, n);
  }
  else makeThisCohringDifferential(resol, n);
  return;
}

/******************************************************************************/
void ensureThisProjectiveKnown(resol_t *resol, long n)
{
  long d;
  while ((d = resol->numproj + 1) <= n)
    readOrConstructThisProjective(resol, d);
  return;
}

/******************************************************************************/
void ensureThisUrbildGBKnown(resol_t *resol, long n)
{
  if (n < 1 || n > resol->numproj)
    OtherError("ensureThisUrbildGBKnown: invalid data");
  if (fileExists(urbildGBFile(resol, n))) return;
  makeThisDifferential(resol, n+1);
  return;
}


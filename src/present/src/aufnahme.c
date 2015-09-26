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
*  aufnahme.c : Aufnahme is Subalgorithm of Buchberger
*  Author: David J Green
*  First version: 14 March 2000 from incorporate.c
*/

#include "nDiag.h"
#include "slice_decls.h"
#include "urbild_decls.h"
#include "meataxe.h"

/******************************************************************************/
static modW_t *wordForestEntry(ngs_t *ngs, gV_t *gv)
{
  return ngs->proot[gv->block - 1] + (gv->col - 1);
}

/******************************************************************************/
static void subtract(PTR ptr1, PTR ptr2, long nor)
/* writes ptr1 - ptr2 to ptr1 */
{
  register long i;
  PTR p1 = ptr1, p2 = ptr2;
  for (i = 0; i < nor; i++)
  {
    zsubrow(p1,p2);
    zsteprow(&p1); zsteprow(&p2);
  }
  return;
}

/******************************************************************************/
static void submul(PTR ptr1, PTR ptr2, FEL f, long nor)
/* writes ptr1 - f.ptr2 to ptr1 */
{
  register long i;
  register FEL g = zsub(F_ZERO, f);
  PTR p1 = ptr1, p2 = ptr2;
  for (i = 0; i < nor; i++)
  {
    zaddmulrow(p1,p2, g);
    zsteprow(&p1); zsteprow(&p2);
  }
  return;
}

/******************************************************************************/
static void demoteReducedVector(ngs_t *ngs, rV_t *rv)
/* rv used to be reduced, but we've just found something it reduces over */
{
  unlinkReducedVector(ngs, rv);
  insertNewUnreducedVector(ngs, rv->gv);
  rv->gv = NULL;
  freeReducedVector(rv, ngs);
  return;
}

/******************************************************************************/
static void markNodeMultiples(ngs_t *ngs, rV_t *rv, modW_t *node,
  boolean alreadyFound, path_t *ext, group_t *group)
{
  /* node != NULL guaranteed */
  /* know: node represents tip(rv) * ext */
  register long a;
  rV_t *v = node->divisor;
  boolean aF = alreadyFound;
  if (!alreadyFound && v != NULL)
  {
    /* printf("markNodeMultiples: spurious generator expelled\n"); */
    demoteReducedVector(ngs, v);
    aF = true;
  }
  node->divisor = rv;
  node->qi = ext->index;
  node->status = (ext->index == 0) ? SCALAR_MULTIPLE : NONSCALAR_MULTIPLE;
  if (ext->index == 0) node->parent = NULL;
  if (!aF) ngs->pnontips--;
  for (a = 0; a < group->arrows; a++)
  {
    if (!node->child[a]) continue;
    node->child[a]->parent = node;
    markNodeMultiples(ngs, rv, node->child[a], aF, ext->child[a], group);
  }
  return;
}

/*****
 * 1 on error
 **************************************************************************/
int nRgsAssertReducedVectors(nRgs_t *nRgs, PTR mat, long num, group_t *group)
/* mat should be a block of length num * nor */
{
  ngs_t *ngs = nRgs->ngs;
  register gV_t *gv;
  register rV_t *rv;
  modW_t *ptn;
  register long i;
  long nor = ngs->r + ngs->s;
  for (i = 0; i < num; i++)
  {
    gv = popGeneralVector(ngs);
    memcpy(gv->w, ptrPlus(mat, i * nor), zsize(nor));
    findLeadingMonomial(gv, ngs->r, group);
    ptn = wordForestEntry(ngs, gv);
    rv = reducedVector(gv, group);
    rv->node = ptn;
    insertReducedVector(ngs, rv);
    markNodeMultiples(ngs, rv, ptn, false, group->root, group);
  }
  if (ngs->unreducedHeap)
  { MTX_ERROR("nRgsAssertRV: Theoretical error");
    return 1;
  }
  return 0;
}

/******************************************************************************/
static void promoteUnreducedVector(ngs_t *ngs, uV_t *uv, group_t *group)
{
  modW_t *ptn = wordForestEntry(ngs, uv->gv);
  rV_t *rv;
  rv = reducedVector(uv->gv, group);
  rv->node = ptn;
  uv->gv = NULL;
  freeUnreducedVector(uv);
  insertReducedVector(ngs, rv);
  markNodeMultiples(ngs, rv, ptn, false, group->root, group);
  return;
}

/******************************************************************************/
void possiblyNewKernelGenerator(nRgs_t *nRgs, PTR pw, group_t *group)
{
  PTR pm = pw;
  zadvance(&pm, nRgs->ngs->r);
  processNewFlaggedGenerator (nRgs->ker, pm, group);
  return;
}

/******************************************************************************/
static void nFgsProcessModifiedUnreducedVector(nFgs_t *nFgs, uV_t *uv,
  group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  gV_t *gv = uv->gv;
  findLeadingMonomial(gv, ngs->r, group);
  if (gv->dim == ZERO_BLOCK)
    freeUnreducedVector(uv);
  else
  {
    makeVectorMonic(ngs, gv);
    insertUnreducedVector(ngs, uv);
  }
  return;
}

/******************************************************************************/
static void nRgsProcessModifiedUnreducedVector(nRgs_t *nRgs, uV_t *uv, group_t *group)
{
  ngs_t *ngs = nRgs->ngs;
  register gV_t *gv = uv->gv;
  findLeadingMonomial(gv, ngs->r, group);
  if (gv->dim == ZERO_BLOCK)
  {
    possiblyNewKernelGenerator(nRgs, gv->w, group);
    freeUnreducedVector(uv);
  }
  else
  {
    makeVectorMonic(ngs, gv);
    insertUnreducedVector(ngs, uv);
  }
  return;
}

/******************************************************************************/
static void urbildProcessModifiedUnreducedVector(nRgs_t *nRgs, uV_t *uv,
  group_t *group, PTR result)
{
  ngs_t *ngs = nRgs->ngs;
  register long r = ngs->r;
  register long s = ngs->s;
  PTR src, dest;
  gV_t *gv = uv->gv;
  findLeadingMonomial(gv, r, group);
  if (gv->dim == ZERO_BLOCK)
  {
    src = ptrPlus(gv->w, r);
    dest = ptrPlus(result, uv->index * s);
    memcpy(dest, src, zsize(s));
    freeUnreducedVector(uv);
  }
  else insertUnreducedVector(ngs, uv);
  return;
}

/******************************************************************************/
static void nFgsPerformLinearReductions(nFgs_t *nFgs, gV_t *gv0, group_t *group)
{
  register ngs_t *ngs = nFgs->ngs;
  register long nor = ngs->r + ngs->s;
  register gV_t *gv;
  register uV_t *uv;
  while ((uv = unreducedSuccessor(ngs, NULL)) && (gv = uv->gv)->col == gv0->col
    && gv->block == gv0->block)
  {
    unlinkUnreducedVector(ngs, uv);
    subtract(gv->w, gv0->w,nor);
    nFgsProcessModifiedUnreducedVector(nFgs, uv, group);
  }
  return;
}

/******************************************************************************/
static void nRgsPerformLinearReductions(nRgs_t *nRgs, gV_t *gv0, group_t *group)
{
  register ngs_t *ngs = nRgs->ngs;
  register long nor = ngs->r + ngs->s;
  register gV_t *gv;
  register uV_t *uv;
  while ((uv = unreducedSuccessor(ngs, NULL)) && (gv = uv->gv)->col == gv0->col
    && gv->block == gv0->block)
  {
    unlinkUnreducedVector(ngs, uv);
    subtract(gv->w, gv0->w,nor);
    nRgsProcessModifiedUnreducedVector(nRgs, uv, group);
  }
  return;
}

/******************************************************************************/
static boolean shouldReduceTip(ngs_t *ngs, gV_t *gv)
/* Includes test for swapping reduced heady with unreduced radical */
{
  modW_t *node = wordForestEntry(ngs, gv) ;
  if (!node->divisor) return false;
  if (node->qi == 0 && !node->divisor->gv->radical && gv->radical)
  {
    return false;
  }
  return true;
}

/******************************************************************************/
static void reduceMonicTipOnce(ngs_t *ngs, gV_t *gv, group_t *group)
{
  /* modW_t *node = wordForestEntry(ngs, gv); */
  /* PTR w = nodeVector(ngs, group, node); */
  /* long nor = ngs->r + ngs->s; */
  modW_t *node;
  PTR w;
  long nor;
  node = wordForestEntry(ngs, gv);
  w = nodeVector(ngs, group, node);
  nor = ngs->r + ngs->s;
  subtract(gv->w, w, nor);
  return;
}

/******************************************************************************/
static void reduceTipOnce(ngs_t *ngs, gV_t *gv, group_t *group)
{
  /* modW_t *node = wordForestEntry(ngs, gv); */
  /* PTR w = nodeVector(ngs, group, node); */
  /* long nor = ngs->r + ngs->s; */
  modW_t *node;
  PTR w;
  long nor;
  node = wordForestEntry(ngs, gv);
  w = nodeVector(ngs, group, node);
  nor = ngs->r + ngs->s;
  submul(gv->w, w, gv->coeff, nor);
  return;
}

/******************************************************************************/
static void tidyUpAfterAufnahme(ngs_t *ngs)
{
  destroyCurrentDimensionIfAny(ngs);
  return;
}

/******************************************************************************/
void nFgsAufnahme(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  register uV_t *uv;
  register gV_t *gv;
  long sweepDim;
  if (!ngs->unreducedHeap)
  {
    tidyUpAfterAufnahme(ngs);
    return;
  }
  sweepDim = ngs->unreducedHeap->gv->dim;
  selectNewDimension(ngs, group, sweepDim);
  for (; sweepDim <= group->maxlength; sweepDim++)
  {
    while ((uv = unreducedSuccessor(ngs, NULL)) && uv->gv->dim == sweepDim)
    {
      unlinkUnreducedVector(ngs, uv);
      gv = uv->gv;
      nFgsPerformLinearReductions(nFgs, gv, group);
      if (shouldReduceTip(ngs, gv))
      {
        reduceMonicTipOnce(ngs, gv, group);
        nFgsProcessModifiedUnreducedVector(nFgs, uv, group);
      }
      else
      {
        promoteUnreducedVector(ngs, uv, group);
      }
    }
    if (!uv) break; /* All unreduced vectors processed */
    else incrementSlice(ngs, group);
  }
  tidyUpAfterAufnahme(ngs);
  return;
}

/*****
 * 1 on error
 **************************************************************************/
int urbildAufnahme(nRgs_t *nRgs, group_t *group, PTR result)
{
  register ngs_t *ngs = nRgs->ngs;
  register uV_t *uv;
  register gV_t *gv;
  register long sweepDim;
  if (!ngs->unreducedHeap)
  {
    tidyUpAfterAufnahme(ngs);
    return 0;
  }
  sweepDim = ngs->unreducedHeap->gv->dim;
  selectNewDimension(ngs, group, sweepDim);
  for (; sweepDim <= group->maxlength; sweepDim++)
  {
    while ((uv = unreducedSuccessor(ngs, NULL)) && uv->gv->dim == sweepDim)
    {
      unlinkUnreducedVector(ngs, uv);
      gv = uv->gv;
      if (shouldReduceTip(ngs, gv))
      {
        reduceTipOnce(ngs, gv, group);
        urbildProcessModifiedUnreducedVector(nRgs, uv, group, result);
      }
      else
      {
        MTX_ERROR1("vector doesn't lie in image : %E", MTX_ERR_INCOMPAT);
      }
    }
    if (!uv) break; /* All unreduced vectors processed */
    else incrementSlice(ngs, group);
  }
  tidyUpAfterAufnahme(ngs);
  return 0;
}

/******************************************************************************/
void nRgsAufnahme(nRgs_t *nRgs, group_t *group)
{
  register ngs_t *ngs = nRgs->ngs;
  register uV_t *uv;
  register gV_t *gv;
  long sweepDim;
  if (!ngs->unreducedHeap)
  {
    tidyUpAfterAufnahme(ngs);
    return;
  }
  sweepDim = ngs->unreducedHeap->gv->dim;
  selectNewDimension(ngs, group, sweepDim);
  for (; sweepDim <= group->maxlength; sweepDim++)
  {
    while ((uv = unreducedSuccessor(ngs, NULL)) && uv->gv->dim == sweepDim)
    {
      unlinkUnreducedVector(ngs, uv);
      gv = uv->gv;
      nRgsPerformLinearReductions(nRgs, gv, group);
      if (shouldReduceTip(ngs, gv))
      {
        reduceMonicTipOnce(ngs, gv, group);
        nRgsProcessModifiedUnreducedVector(nRgs, uv, group);
      }
      else
      {
        promoteUnreducedVector(ngs, uv, group);
      }
    }
    if (!uv) break; /* All unreduced vectors processed */
    else incrementSlice(ngs, group);
  }
  tidyUpAfterAufnahme(ngs);
  return;
}

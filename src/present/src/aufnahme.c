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
*  aufnahme.c : Aufnahme is Subalgorithm of Buchberger
*  Author: David J Green
*  First version: 14 March 2000 from incorporate.c
*/

#include "nDiag.h"
#include "slice_decls.h"
#include "urbild_decls.h"
#include "meataxe.h"
#include "aufnahme.h"

MTX_DEFINE_FILE_INFO

/******************************************************************************/
static modW_t *wordForestEntry(ngs_t *ngs, gV_t *gv)
{
  return ngs->proot[gv->block] + (gv->col);
}

/******************************************************************************/
static void subtract(PTR ptr1, PTR ptr2, long nor)
/* writes ptr1 - ptr2 to ptr1 */
{
  register long i;
  register PTR p1 = ptr1, p2 = ptr2;
  for (i = 0; i < nor; i++, p1+=FfCurrentRowSize, p2+=FfCurrentRowSize)
  {
    FfSubRow(p1,p2);
    /*FfStepPtr(&p1); FfStepPtr(&p2);*/
  }
  return;
}

/******************************************************************************/
static void submul(PTR ptr1, PTR ptr2, FEL f, long nor)
/* writes ptr1 - f.ptr2 to ptr1 */
{
  register long i;
  register FEL g = FfNeg(f);
  PTR p1 = ptr1, p2 = ptr2;
  for (i = 0; i < nor; i++, p1+=FfCurrentRowSize, p2+=FfCurrentRowSize)
  {
    FfAddMulRow(p1,p2, g);
    /*FfStepPtr(&p1); FfStepPtr(&p2);*/
  }
  return;
}

/****
 * 1 on error
 ***************************************************************************/
static int demoteReducedVector(ngs_t *ngs, rV_t *rv)
/* rv used to be reduced, but we've just found something it reduces over */
{
  unlinkReducedVector(ngs, rv);
  if (insertNewUnreducedVector(ngs, rv->gv)) return 1;
  rv->gv = NULL;
  freeReducedVector(rv, ngs);
  return 0;
}

/*****
 * 1 on error
 *************************************************************************/
static int markNodeMultiples(ngs_t *ngs, rV_t *rv, modW_t *node,
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
    if (demoteReducedVector(ngs, v)) return 1;
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
    if (markNodeMultiples(ngs, rv, node->child[a], aF, ext->child[a], group)) return 1;
  }
  return 0;
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
    if (!gv) return 1;
    memcpy(gv->w, FfGetPtr(mat, i * nor), (FfCurrentRowSize*nor));
    findLeadingMonomial(gv, ngs->r, group);
    ptn = wordForestEntry(ngs, gv);
    rv = reducedVector(gv, group);
    if (!rv) return 1;
    rv->node = ptn;
    if (insertReducedVector(ngs, rv)) return 1;
    if (markNodeMultiples(ngs, rv, ptn, false, group->root, group)) return 1;
  }
  if (ngs->unreducedHeap)
  { MTX_ERROR("nRgsAssertRV: Theoretical error");
    return 1;
  }
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
static int promoteUnreducedVector(ngs_t *ngs, uV_t *uv, group_t *group)
{
  modW_t *ptn = wordForestEntry(ngs, uv->gv);
  rV_t *rv;
  rv = reducedVector(uv->gv, group);
  if (!rv) return 1;
  rv->node = ptn;
  uv->gv = NULL;
  freeUnreducedVector(uv);
  if (insertReducedVector(ngs, rv)) return 1;
  return markNodeMultiples(ngs, rv, ptn, false, group->root, group);
}

/******************************************************************************/
void possiblyNewKernelGenerator(nRgs_t *nRgs, PTR pw, group_t *group)
{
  PTR pm = pw;
  pm = FfGetPtr(pm, nRgs->ngs->r);
  processNewFlaggedGenerator (nRgs->ker, pm, group);
  return;
}

/*****
 * 1 on error
 **************************************************************************/
static int nFgsProcessModifiedUnreducedVector(nFgs_t *nFgs, uV_t *uv,
  group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  gV_t *gv = uv->gv;
  findLeadingMonomial(gv, ngs->r, group);
  if (gv->dim == ZERO_BLOCK)
    freeUnreducedVector(uv);
  else
  {
    if (makeVectorMonic(ngs, gv)) return 1;
    insertUnreducedVector(ngs, uv);
  }
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
static int nRgsProcessModifiedUnreducedVector(nRgs_t *nRgs, uV_t *uv, group_t *group)
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
    if (makeVectorMonic(ngs, gv)) return 1;
    insertUnreducedVector(ngs, uv);
  }
  return 0;
}

/******
 * 1 on error
 *************************************************************************/
static int urbildProcessModifiedUnreducedVector(nRgs_t *nRgs, uV_t *uv,
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
    src = FfGetPtr(gv->w, r);
    dest = FfGetPtr(result, uv->index * s);
    memcpy(dest, src, (FfCurrentRowSize*s));
    freeUnreducedVector(uv);
  }
  else insertUnreducedVector(ngs, uv);
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
static int nFgsPerformLinearReductions(nFgs_t *nFgs, gV_t *gv0, group_t *group)
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
    if (nFgsProcessModifiedUnreducedVector(nFgs, uv, group)) return 1;
  }
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
static int nRgsPerformLinearReductions(nRgs_t *nRgs, gV_t *gv0, group_t *group)
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
    if (nRgsProcessModifiedUnreducedVector(nRgs, uv, group)) return 1;
  }
  return 0;
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

/*****
 * 1 on error
 **************************************************************************/
static int reduceMonicTipOnce(ngs_t *ngs, gV_t *gv, group_t *group)
{
  /* modW_t *node = wordForestEntry(ngs, gv); */
  /* PTR w = nodeVector(ngs, group, node); */
  /* long nor = ngs->r + ngs->s; */
  modW_t *node;
  PTR w;
  long nor;
  node = wordForestEntry(ngs, gv);
  w = nodeVector(ngs, group, node);
  if (!w) return 1;
  nor = ngs->r + ngs->s;
  subtract(gv->w, w, nor);
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
static int reduceTipOnce(ngs_t *ngs, gV_t *gv, group_t *group)
{
  /* modW_t *node = wordForestEntry(ngs, gv); */
  /* PTR w = nodeVector(ngs, group, node); */
  /* long nor = ngs->r + ngs->s; */
  modW_t *node;
  PTR w;
  long nor;
  node = wordForestEntry(ngs, gv);
  w = nodeVector(ngs, group, node);
  if (!w) return 1;
  nor = ngs->r + ngs->s;
  submul(gv->w, w, gv->coeff, nor);
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
static int tidyUpAfterAufnahme(ngs_t *ngs)
{
  return destroyCurrentDimensionIfAny(ngs);
}

/*****
 * 1 on error
 **************************************************************************/
int nFgsAufnahme(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  register uV_t *uv;
  register gV_t *gv;
  long sweepDim;
  if (!ngs->unreducedHeap)
  {
    tidyUpAfterAufnahme(ngs);
    return 0;
  }
  sweepDim = ngs->unreducedHeap->gv->dim;
  if (selectNewDimension(ngs, group, sweepDim)) return 1;
  for (; sweepDim <= group->maxlength; sweepDim++)
  { uv = unreducedSuccessor(ngs, NULL);
    while ((uv != NULL) && uv->gv->dim == sweepDim)
    {
      unlinkUnreducedVector(ngs, uv);
      gv = uv->gv;
      if (nFgsPerformLinearReductions(nFgs, gv, group)) return 1;
      if (shouldReduceTip(ngs, gv))
      {
        if (reduceMonicTipOnce(ngs, gv, group)) return 1;
        if (nFgsProcessModifiedUnreducedVector(nFgs, uv, group)) return 1;
      }
      else
      {
        if (promoteUnreducedVector(ngs, uv, group)) return 1;
      }
      uv = unreducedSuccessor(ngs, NULL);
    }
    if (!uv) break; /* All unreduced vectors processed */
    else if (incrementSlice(ngs, group)) return 1;
  }
  tidyUpAfterAufnahme(ngs);
  return 0;
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
  if (selectNewDimension(ngs, group, sweepDim)) return 1;
  for (; sweepDim <= group->maxlength; sweepDim++)
  {
    while ((uv = unreducedSuccessor(ngs, NULL)) && uv->gv->dim == sweepDim)
    {
      unlinkUnreducedVector(ngs, uv);
      gv = uv->gv;
      if (shouldReduceTip(ngs, gv))
      {
        if (reduceTipOnce(ngs, gv, group)) return 1;
        if (urbildProcessModifiedUnreducedVector(nRgs, uv, group, result)) return 1;
      }
      else
      {
        return MTX_ERROR1("vector doesn't lie in image : %E", MTX_ERR_INCOMPAT),1;
      }
    }
    if (!uv) break; /* All unreduced vectors processed */
    else if (incrementSlice(ngs, group)) return 1;
  }
  tidyUpAfterAufnahme(ngs);
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int nRgsAufnahme(nRgs_t *nRgs, group_t *group)
{
  register ngs_t *ngs = nRgs->ngs;
  register uV_t *uv;
  register gV_t *gv;
  long sweepDim;
  if (!ngs->unreducedHeap)
  {
    tidyUpAfterAufnahme(ngs);
    return 0;
  }
  sweepDim = ngs->unreducedHeap->gv->dim;
  if (selectNewDimension(ngs, group, sweepDim)) return 1;
  for (; sweepDim <= group->maxlength; sweepDim++)
  {
    while ((uv = unreducedSuccessor(ngs, NULL)) && uv->gv->dim == sweepDim)
    {
      unlinkUnreducedVector(ngs, uv);
      gv = uv->gv;
      if (nRgsPerformLinearReductions(nRgs, gv, group)) return 1;
      if (shouldReduceTip(ngs, gv))
      {
        if (reduceMonicTipOnce(ngs, gv, group)) return 1;
        if (nRgsProcessModifiedUnreducedVector(nRgs, uv, group)) return 1;
      }
      else
      {
        if (promoteUnreducedVector(ngs, uv, group)) return 1;
      }
    }
    if (!uv) break; /* All unreduced vectors processed */
    else if (incrementSlice(ngs, group)) return 1;
  }
  tidyUpAfterAufnahme(ngs);
  return 0;
}

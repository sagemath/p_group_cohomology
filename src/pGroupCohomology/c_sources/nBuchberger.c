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
*  nBuchberger.c : Buchberger Algorithm variants
*  Author: David J Green
*  First version: 15 March 2000 from buchberger.c
*
* expDim info: rv->expDim = n is the assertion that all expansions of rv
*              have been performed which have dimension n or less.
* ngs->expDim should basically be the minimum of all rv->expDim's.
* The exception is during expansion, where ngs->expDim is incremented first,
* and then all rv's are brought up to this level.
*  If no Buchberger required, set ngs->expDim to NO_BUCHBERGER_REQUIRED. By
* default, ngs->expDim takes value NOTHING_TO_EXPAND, signifying no rv's
* have yet been recorded. If expDim takes neither of these values, than
* can assume the expDim slice has been precalculated, but cannot assume
* it is currently loaded.
*   Should probably unload and destroy current sweep slice at end of Aufnahme.
*/

#include "nDiag.h"
#include "slice_decls.h"
#include "urbild_decls.h"
#include "aufnahme_decls.h"


/******************************************************************************/
static void initializeCommonBuchStatus(ngs_t *ngs)
{
  ngs->prev_pnon = ngs->pnontips;
  ngs->unfruitful = 0;
  return;
}

/******************************************************************************
Simon King (2008-12): Try to define inline
static void recordCurrentSizeOfVisibleKernel(nRgs_t *nRgs)
{
  nRgs->prev_ker_pnon = nRgs->ker->ngs->pnontips;
  return;
}

******************************************************************************/
/******************************************************************************/
inline void recordCurrentSizeOfVisibleKernel(nRgs_t *nRgs) { nRgs->prev_ker_pnon = nRgs->ker->ngs->pnontips; return; }

/******************************************************************************/
static void updateCommonBuchStatus(ngs_t *ngs, group_t *group)
{
  if (ngs->pnontips < ngs->prev_pnon)
  {
    ngs->prev_pnon = ngs->pnontips;
    ngs->unfruitful = 0;
  }
  else ngs->unfruitful++;
  return;
}

/******************************************************************************/
static void nFgsExpandThisLevel(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  register long nor = ngs->r + ngs->s;
  register long pat, blo, a;
  register long dim = ngs->expDim;
  modW_t *node;
  path_t *ext;
  register PTR w;
  register rV_t *rv;
  register gV_t *gv;
  for (blo = 0; blo < ngs->r; blo++)
  {
    for (pat = group->dS[dim]; pat < group->dS[dim+1]; pat++)
    {
      node = ngs->proot[blo] + pat;
      if (node->status == NO_DIVISOR) continue;
      if (node->divisor->expDim > dim) continue; /* has already been expanded */
      ext = group->root + node->qi;
      for (a = 0; a < group->arrows; a++)
      {
        if (!ext->child[a] || node->child[a]) continue;
        w = nodeVector(ngs, group, node);
        gv = popGeneralVector(ngs);
        multiply(w, group->action[a], gv->w, nor);
        findLeadingMonomial(gv, ngs->r, group);
        if (gv->coeff != F_ZERO)
        {  
          makeVectorMonic(ngs, gv);
          insertNewUnreducedVector(ngs,gv); /* gv->radical true */
        }  
        else pushGeneralVector(ngs, gv);
      }
    }
  }
  for (rv = ngs->firstReduced; rv; rv = rv->next)
    if (rv->expDim == dim) rv->expDim++;
  ngs->expDim++;
  return;
}

/******************************************************************************/
static void nRgsExpandThisLevel(nRgs_t *nRgs, group_t *group)
{
  ngs_t *ngs = nRgs->ngs;
  long nor = ngs->r + ngs->s;
  register long pat;
  long blo;
  register long a;
  long dim = ngs->expDim;
  modW_t *node;
  path_t *ext;
  register PTR w;
  register gV_t *gv;
  register rV_t *rv;
  for (blo = 0; blo < ngs->r; blo++)
  {
    for (pat = group->dS[dim]; pat < group->dS[dim+1]; pat++)
    {
      node = ngs->proot[blo] + pat;
      if (node->status == NO_DIVISOR) continue;
      if (node->divisor->expDim > dim) continue; /* has already been expanded */
      ext = group->root + node->qi;
      for (a = 0; a < group->arrows; a++)
      {
        if (!ext->child[a] || node->child[a]) continue;
        w = nodeVector(ngs, group, node);
        gv = popGeneralVector(ngs);
        multiply(w, group->action[a], gv->w, nor);
        findLeadingMonomial(gv, ngs->r, group);
        if (gv->coeff != F_ZERO)
        {  
          makeVectorMonic(ngs, gv);
          insertNewUnreducedVector(ngs,gv);
        }  
        else
        {  
          possiblyNewKernelGenerator(nRgs, gv->w, group);
          pushGeneralVector(ngs, gv);
        }  
      }
    }
  }
  for (rv = ngs->firstReduced; rv; rv = rv->next)
    if (rv->expDim == dim) rv->expDim++;
  ngs->expDim++;
  return;
}

/******************************************************************************/
static boolean easyCorrectRank(ngs_t *ngs, group_t *group)
{
  if (ngs->targetRank == RANK_UNKNOWN) return false;
  return (ngs->targetRank + ngs->pnontips == ngs->r * group->nontips) ?
    true : false;
}

/******************************************************************************/
static boolean allExpansionsDone(ngs_t *ngs, group_t *group)
{
  if (ngs->expDim == NO_BUCHBERGER_REQUIRED)
    OtherError("allExp: invalid expDim");
  if (ngs->expDim == NOTHING_TO_EXPAND)
    return true;
  return (ngs->expDim <= group->maxlength) ? false : true;
}

/******************************************************************************/
static boolean hardCorrectRank(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  if (easyCorrectRank(ngs, group)) return true;
  if (nFgs->nRgsUnfinished) return false;
  if (ngs->unreducedHeap) return false;
  return allExpansionsDone(ngs, group);
}

/******************************************************************************/
static boolean nFgsBuchbergerFinished(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  return (hardCorrectRank(nFgs, group) &&
    dimensionOfDeepestHeady(ngs) <= ngs->expDim) ? true : false;
}

/******************************************************************************/
static boolean appropriateToPerformHeadyBuchberger(nRgs_t *nRgs, group_t *group)
{
  register ngs_t *ngs = nRgs->ngs;
  register nFgs_t *ker = nRgs->ker;
  if (!easyCorrectRank(ngs, group)) return false;
  if (!ker->nRgsUnfinished || ngs->unfruitful == nRgs->overshoot) return true;
  if (ngs->unfruitful < nRgs->overshoot) return false;
  return (ker->ngs->pnontips < nRgs->prev_ker_pnon) ? true : false;
}

/******************************************************************************/
static void checkRanksCorrect(nRgs_t *nRgs)
{
  ngs_t *ngs = nRgs->ngs;
  ngs_t *ker_ngs = nRgs->ker->ngs;
  if (ngs->targetRank == RANK_UNKNOWN) return;
  if (ker_ngs->pnontips != ngs->targetRank)
  {
    OtherError("Theoretical error: rank differs from expected value.");
  }
  return;
}

/******************************************************************************/
static void assertMinimalGeneratorsFound(nFgs_t *nFgs)
{
  nFgs->finished = true;
  return;
}

/******************************************************************************/
static inline boolean shouldFetchMoreGenerators(nFgs_t *nFgs, group_t *group)
{
  ngs_t *ngs = nFgs->ngs;
  if (!nFgs->nRgsUnfinished) return false;
  if (ngs->unfruitful < nFgs->max_unfruitful) return false;
  if (easyCorrectRank(ngs, group)) return false;
  // return (headyDim(nFgs) <= ngs->expDim) ? true : false;
  return (dimensionOfDeepestHeady(nFgs->ngs) <= ngs->expDim) ? true : false;
}

/******************************************************************************/
void nFgsBuchberger(nFgs_t *nFgs, group_t *group)
{
  register ngs_t *ngs = nFgs->ngs;
  nFgsAufnahme (nFgs, group);
  initializeCommonBuchStatus(ngs);
  if (nFgsBuchbergerFinished(nFgs, group)) /* Can happen on reentry */
    assertMinimalGeneratorsFound(nFgs);
  else while (!allExpansionsDone(ngs, group))
  {
    /* Can assume expDim slice precalculated; cannot assume preloaded */
    loadExpansionSlice(ngs, group);
    nFgsExpandThisLevel(nFgs, group); /* increments ngs->expDim */
    incrementSlice(ngs, group);
    nFgsAufnahme (nFgs, group);
    updateCommonBuchStatus(ngs, group);
    if (nFgsBuchbergerFinished(nFgs, group))
    {
      assertMinimalGeneratorsFound(nFgs);
      break;
    }
    if (shouldFetchMoreGenerators(nFgs, group))
    {
      break;
    }
  }
  if (nFgs->finished) destroyExpansionSliceFile(ngs);
  return;
}

/******************************************************************************/
void nRgsBuchberger(nRgs_t *nRgs, group_t *group)
{
  register ngs_t *ngs = nRgs->ngs;
  register nFgs_t *ker = nRgs->ker;
  ker->nRgsUnfinished = true;
  nRgsAufnahme (nRgs, group);
  initializeCommonBuchStatus(ngs);
  while (!allExpansionsDone(ngs, group))
  {
    recordCurrentSizeOfVisibleKernel(nRgs);
    /* Can assume expDim slice precalculated; cannot assume preloaded */
    loadExpansionSlice(ngs, group);
    nRgsExpandThisLevel(nRgs, group); /* increments ngs->expDim */
    incrementSlice(ngs, group);
    nRgsAufnahme (nRgs, group); /* Now certain no slice loaded */
    if (allExpansionsDone(ngs, group)) ker->nRgsUnfinished = false;
    updateCommonBuchStatus(ngs, group);
    nFgsAufnahme (ker, group);
    if (appropriateToPerformHeadyBuchberger(nRgs, group))
    {
      nFgsBuchberger(ker, group);
      if (ker->finished) break;
    }
  }
  /* If targetRank known, then nFgsBuchberger guaranteed already finished. */
  /* So next line should only apply if unknown. NB nRgsUnfinished now false. */
  if (!ker->finished) nFgsBuchberger(ker, group);
  checkRanksCorrect(nRgs);
  destroyExpansionSliceFile(ngs);
  return;
}

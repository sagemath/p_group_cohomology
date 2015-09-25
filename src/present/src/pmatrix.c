/* ========================== Present =============================
   pmatrix.c : Routines for handling matrices

   (C) Copyright 1999-2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"

void *InnerRightProduct(const matrix_t *dest, const matrix_t *src, PTR scratch)
/* Assembles dest * src at scratch. */
/* src should be square, scratch should point to enough space. */
{
  register long i;
  PTR this_dest = dest->d;
  PTR this_scratch = scratch;
  if (src->fl != dest->fl || src->nor != dest->noc || src->nor != src->noc)
  {
    MTXFAIL(ERR_INCOMPAT,NULL);
  }
  zsetlen(src->noc);
  for (i = dest->nor; i != 0; --i)
  {
    zmaprow(this_dest,src->d,src->nor,this_scratch);
    zsteprow(&this_scratch);
    zsteprow(&this_dest);
  }
  return;
}

matrix_t *RightProduct(const matrix_t *dest, const matrix_t *src)
{
  matrix_t *result = matalloc(src->fl, dest->nor, src->noc);
  if (!result) AllocationError("RightProduct");
  InnerRightProduct(dest,src,result->d);
  return result;
}

matrix_t *InnerRightAction(matrix_t *dest, const matrix_t *src, PTR scratch)
/* Guaranteed not to alter dest->d */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  InnerRightProduct(dest,src,scratch);
  memcpy(dest->d, scratch, zsize(dest->nor));
  return dest;
}

matrix_t *InnerLeftAction(const matrix_t *src, matrix_t *dest, PTR scratch)
/* Guaranteed not to alter dest->d */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  register long i;
  PTR this_src = src->d;
  PTR this_scratch = scratch;
  if (src->fl != dest->fl || src->noc != dest->nor || src->nor != src->noc)
  {
    MTXFAIL(ERR_INCOMPAT,NULL);
  }
  zsetlen(dest->noc);
  for (i = dest->nor; i != 0; --i)
  {
    zmaprow(this_src,dest->d,dest->nor,this_scratch);
    zsteprow(&this_scratch);
    zsteprow(&this_src);
  }
  memcpy(dest->d, scratch, zsize(dest->nor));
  return dest;
}

matrix_t *RightAction(matrix_t *dest, const matrix_t *src)
/* Guaranteed not to alter dest->d */
{
  PTR scratch;
  zsetlen(src->noc);
  scratch = zalloc(dest->nor);
  if (!scratch)
  {
    MTXFAIL(ERR_NOMEM,NULL);
  }
  InnerRightAction(dest, src, scratch);
  free(scratch);
  return dest;
}

/******************************************************************************/void innerBasisChangeNontips2Reg(group_t *group, matrix_t **matlist,
  long num, PTR workspace)
  /* Alters matrices in matlist */
  /* workspace points to group->nontips rows scratch space */
{
  register long i;
  matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    InnerLeftAction(wb, matlist[i], workspace);
    InnerRightAction(matlist[i], bw, workspace);
  }
  return;
}

/******************************************************************************/void innerBasisChangeReg2Nontips(group_t *group, matrix_t **matlist,
  long num, PTR workspace)
/* Alters matrices in matlist */
/* workspace points to group->nontips rows scratch space */
{
  register long i;
  matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    InnerLeftAction(bw, matlist[i], workspace);
    InnerRightAction(matlist[i], wb, workspace);
  }
  return;
}

/******************************************************************************/void basisChangeReg2Nontips(group_t *group, matrix_t **matlist, long num)
/* Alters matrices in matlist */
{
  PTR workspace = zalloc(group->nontips);
  if (!workspace) AllocationError("basisChangeReg2Nontips");
  innerBasisChangeReg2Nontips(group, matlist, num, workspace);
  free(workspace);
  return;
}

/******************************************************************************/void changeActionMatricesReg2Nontips(group_t *group)
{
  PTR workspace;
  workspace = zalloc(group->nontips);
  if (!workspace) AllocationError("changeActionMatricesReg2Nontips: workspace");  innerBasisChangeReg2Nontips(group, group->action, group->arrows, workspace);
  free(workspace);
  return;
}

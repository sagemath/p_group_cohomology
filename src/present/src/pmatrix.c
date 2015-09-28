/* ========================== Present =============================
   pmatrix.c : Routines for handling matrices

   (C) Copyright 1999-2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
MTX_DEFINE_FILE_INFO

/**
 * NULL on error
 ****/
Matrix_t *InnerRightProduct(const Matrix_t *dest, const Matrix_t *src, PTR scratch)
/* Assembles dest * src at scratch. */
/* src should be square, scratch should point to enough space. */
{
  register long i;
  PTR this_dest = dest->Data;
  PTR this_scratch = scratch;
  if (src->Field != dest->Field || src->Nor != dest->Noc || src->Nor != src->Noc)
  {
    MTX_ERROR1("%E", MTX_ERR_INCOMPAT);
    return NULL;
  }
  FfSetNoc(src->Noc);
  for (i = dest->Nor; i != 0; --i)
  {
    FfMapRow(this_dest,src->Data,src->Nor,this_scratch);
    FfStepPtr(&this_scratch);
    FfStepPtr(&this_dest);
  }
  return dest;
}

/**
 * NULL on error
 ****/
Matrix_t *InnerRightAction(Matrix_t *dest, const Matrix_t *src, PTR scratch)
/* Guaranteed not to alter dest->Data */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  if (!InnerRightProduct(dest,src,scratch)) return NULL;
  memcpy(dest->Data, scratch, (FfCurrentRowSize*dest->Nor));
  return dest;
}

/**
 * NULL on error
 ****/
Matrix_t *InnerLeftAction(const Matrix_t *src, Matrix_t *dest, PTR scratch)
/* Guaranteed not to alter dest->Data */
/* Result will be assembled at scratch, then copied to dest */
/* This routine allocates NO memory */
{
  register long i;
  PTR this_src = src->Data;
  PTR this_scratch = scratch;
  if (src->Field != dest->Field || src->Noc != dest->Nor || src->Nor != src->Noc)
  {
    MTX_ERROR1("%E", MTX_ERR_INCOMPAT);
    return NULL;
  }
  FfSetNoc(dest->Noc);
  for (i = dest->Nor; i != 0; --i)
  {
    FfMapRow(this_src,dest->Data,dest->Nor,this_scratch);
    FfStepPtr(&this_scratch);
    FfStepPtr(&this_src);
  }
  memcpy(dest->Data, scratch, (FfCurrentRowSize*dest->Nor));
  return dest;
}

/*****
 * 1 on error
 **************************************************************************/
int innerBasisChangeNontips2Reg(group_t *group, Matrix_t **matlist,
  long num, PTR workspace)
  /* Alters matrices in matlist */
  /* workspace points to group->nontips rows scratch space */
{
  register long i;
  Matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    if (!InnerLeftAction(wb, matlist[i], workspace)) return 1;
    if (!InnerRightAction(matlist[i], bw, workspace)) return 1;
  }
  return 0;
}

/******************************************************************************/
int innerBasisChangeReg2Nontips(group_t *group, Matrix_t **matlist,
  long num, PTR workspace)
/* Alters matrices in matlist */
/* workspace points to group->nontips rows scratch space */
{
  register long i;
  Matrix_t *bw = group->bch[0], *wb = group->bch[1];
  for (i = 0; i < num; i++)
  {
    if (!InnerLeftAction(bw, matlist[i], workspace)) return 1;
    if (!InnerRightAction(matlist[i], wb, workspace)) return 1;
  }
  return;
}

/******************************************************************************/
int basisChangeReg2Nontips(group_t *group, Matrix_t **matlist, long num)
/* Alters matrices in matlist */
{
  PTR workspace = FfAlloc(group->nontips);
  if (!workspace)
  { MTX_ERROR1("%E", MTX_ERROR_NOMEM);
    return 1;
  }
  int r = innerBasisChangeReg2Nontips(group, matlist, num, workspace);
  free(workspace);
  return r;
}

/******************************************************************************/
int changeActionMatricesReg2Nontips(group_t *group)
{
  PTR workspace;
  workspace = FfAlloc(group->nontips);
  if (!workspace)
  { MTX_ERROR1("%E", MTX_ERROR_NOMEM);
    return 1;
  }
  int r = innerBasisChangeReg2Nontips(group, group->action, group->arrows, workspace);
  free(workspace);
  return r;
}

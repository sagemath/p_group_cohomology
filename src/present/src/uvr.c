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
/* uvr.c : Routines for vector subspaces (Untervektorraeume) */
/* Author: David J. Green */
/* First version: 12 September 2000 */

#include "pgroup.h"
#include "uvr.h"
#include "pgroup_decls.h"

/* Need: error routines, FfGetPtr */

/******
 * NULL on error
 *************************************************************************/
uvr_t *newBoundedUvr(long Vdim, long Udim)
{
  uvr_t *U = (uvr_t *) malloc(sizeof(uvr_t));
  if (!U)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  PTR basis = NULL;
  long *piv = (long *) malloc((Udim + 1) * sizeof(long));
  if (!piv)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  FfSetNoc(Vdim);
  if (Udim > 0)
  { basis = FfAlloc(Udim);
    if (!basis)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  }
  piv[0] = 0;
  U->basis = basis;
  U->piv = piv;
  U->Vdim = Vdim;
  U->Udim = Udim;
  return U;
}

/*****
 * NULL on error
 **************************************************************************/
uvr_t *newUvr(long Vdim)
{
  return newBoundedUvr(Vdim, Vdim);
}

/******
 * NULL on error
 *************************************************************************/
uvr_t *ambientVr(long Vdim)
{
  long i;
  uvr_t *V = newBoundedUvr(Vdim, Vdim);
  if (!V) return NULL;
  PTR row;
  row = V->basis;
  for (i = 1; i <= Vdim; i++)
  {
    /* row = FfGetPtr(V->basis, i-1);*/
    FfInsert(row, i, FF_ONE);
    V->piv[i] = i;
    FfStepPtr(&row);
  }
  V->piv[0] = Vdim;
  return V;
}

/******************************************************************************/
void freeUvr(uvr_t *uvr)
{
  if (uvr->basis) free(uvr->basis);
  if (uvr->piv) free(uvr->piv);
  free(uvr);
  return;
}

/******************************************************************************/
long uvrDimension(uvr_t *uvr)
{
  return uvr->piv[0];
}

/******************************************************************************/
static long uvrAmbientDimension(uvr_t *uvr)
{
  return uvr->Vdim;
}

/******************************************************************************/
static long uvrDimensionBound(uvr_t *uvr)
{
  return uvr->Udim;
}

/******************************************************************************/
boolean isAmbientSpace(uvr_t *uvr)
{
  return (uvr->piv[0] == uvr->Vdim) ? true : false;
}

/****
 * 1 on error
 ***************************************************************************/
static int uvrCopy(uvr_t *dest, uvr_t *src)
/* FfNoc = Vdim assumed */
{
  long dim = uvrDimension(src);
  long Vdim = uvrAmbientDimension(src);
  if (uvrAmbientDimension(dest) != Vdim)
  { MTX_ERROR1("ambient spaces differ: %E", MTX_ERR_INCOMPAT);
    return 1;
  }
  if (dim > uvrDimensionBound(dest))
  { MTX_ERROR2("dest too small for dimension %d: %E", dim, MTX_ERR_RANGE);
    return 1;
  }
  memcpy(dest->piv, src->piv, (dim+1) * sizeof(long));
  if (dim > 0) memcpy(dest->basis, src->basis, (FfCurrentRowSize*dim));
  return 0;
}

/*****
 * NULL on error
 **************************************************************************/
static uvr_t *duplicateUvr(uvr_t *old)
{
  uvr_t *new = newBoundedUvr(old->Vdim, old->Udim);
  if (!new) return NULL;
  if (uvrCopy(new, old))
  { freeUvr(new);
    return NULL;
  }
  return new;
}

/******
 * NULL on error
 *************************************************************************/
PTR duplicateUvrBasis(uvr_t *uvr)
{
  uvr_t *dup = duplicateUvr(uvr);
  if (!dup) return NULL;
  PTR basis = dup->basis;
  dup->basis = NULL;
  freeUvr(dup);
  return basis;
}

/******************************************************************************/
static void cleanBirow(PTR row1, PTR row2, PTR mat1, PTR mat2, long nor,
  long *piv)
{
  long i;
  PTR x1, x2;
  for (i=1, x1 = mat1, x2 = mat2; i<=nor;
  ++i, FfStepPtr(&x1), FfStepPtr(&x2))
  {
    FEL f = FfExtract(row1,piv[i]);
    if (f == FF_ZERO) continue;
    f = FfDiv(f,FfExtract(x1,piv[i]));
    FfAddMulRow(row1,x1,FfNeg(f));
    FfAddMulRow(row2,x2,FfNeg(f));
  }
  return;
}

/******************************************************************************/
static long mkBiechelon(PTR mat1, PTR mat2, long nor, long *piv, PTR core,
  long *cpiv)
{
  PTR x1, x2;
  PTR new1 = mat1, new2 = mat2, cnew = core;
  long i, rank = 0, crank = 0;
  for (i = 0; i < nor; ++i)
  {
    long newpiv;
    FEL f;
    x1 = FfGetPtr(mat1, i);
    x2 = FfGetPtr(mat2, i);
    if (rank < i)
    {
      memcpy(new1, x1, FfCurrentRowSize);
      memcpy(new2, x2, FfCurrentRowSize);
    }
    cleanBirow(new1, new2, mat1, mat2, rank, piv);
    newpiv = FfFindPivot(new1,&f);
    if (newpiv == 0)
    {
      memcpy(cnew, new2, FfCurrentRowSize);
      zcleanrow(cnew, core, crank, cpiv);
      newpiv = FfFindPivot(cnew, &f);
      if (newpiv != 0)
      {
        cpiv[++crank] = newpiv;
        FfStepPtr(&cnew);
      }
    }
    {
      ++rank;
      piv[rank] = newpiv;
      FfStepPtr(&new1);
      FfStepPtr(&new2);
    }
  }
  piv[0] = rank;
  cpiv[0] = crank;
  return crank;
}

/****
 * -1 on error
 ***************************************************************************/
static long innerIntersectUvrs(uvr_t *A, uvr_t *B, uvr_t *dest, long dimA,
  long dimB, long nor)
{
  PTR mat1 = FfAlloc(nor);
  if (!mat1)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return -1;
      }
  PTR mat2 = FfAlloc(nor);
  if (!mat2)
      {
          SysFree(mat1);
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return -1;
      }
  long crank;
  long *piv = (long *) malloc((nor+1) * sizeof(long));
  if (!piv)
      {
          SysFree(mat1);
          SysFree(mat2);
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return -1;
      }
  memcpy(mat1, A->basis, (FfCurrentRowSize*dimA));
  memcpy(mat2, A->basis, (FfCurrentRowSize*dimA));
  memcpy(FfGetPtr(mat1, dimA), B->basis, (FfCurrentRowSize*dimB));
  crank = mkBiechelon(mat1, mat2, nor, piv, dest->basis, dest->piv);
  free(mat1); free(mat2); free(piv);
  return crank;
}

/****
 * -1 on error
 ***************************************************************************/
static long intersectUvrs(uvr_t *A, uvr_t *B, uvr_t *dest)
{
  long dimA = uvrDimension(A);
  long dimB = uvrDimension(B);
  long Vdim = uvrAmbientDimension(A);
  long nor = dimA + dimB;
  if (dimA == 0 || dimB == 0)
  {
    dest->piv[0] = 0;
    return 0;
  }
  if (dimA == Vdim)
  {
    if (uvrCopy(dest, B)) return -1;
    return dimB;
  }
  if (dimB == Vdim)
  {
    if (uvrCopy(dest, A)) return -1;
    return dimA;
  }
  return innerIntersectUvrs(A, B, dest, dimA, dimB, nor);
}

/******
 * NULL on error
 *************************************************************************/
uvr_t *uvrIntersection(uvr_t *A, uvr_t *B)
{
  long Vdim = uvrAmbientDimension(A);
  long Udim = minlong(uvrDimension(A), uvrDimension(B));
  uvr_t *C = newBoundedUvr(Vdim, Udim);
  if (!C) return NULL;
  if (intersectUvrs(A,B,C)==-1) return NULL;
  return C;
}

/***
 * 1 on error
 ****************************************************************************/
static int uvrSwap(uvr_t *A, uvr_t *B)
/* A, B must have same Vdim, and Udim=Vdim */
{
  PTR basis = A->basis;
  long *piv = A->piv;
  long Vdim = A->Vdim;
  if (B->Vdim != Vdim || A->Udim != Vdim || B->Udim != Vdim)
  {
      MTX_ERROR1("%E", MTX_ERR_INCOMPAT);
      return 1;
  }
  A->basis = B->basis; B->basis = basis;
  A->piv = B->piv; B->piv = piv;
  return 0;
}

/*****
 * -1 on error
 **************************************************************************/
long repeatIntersectUvrs(uvr_t *dest, uvr_t *src, uvr_t *tmp)
/* dest, src and tmp must all have same Vdim and all have Udim = Vdim */
/* Not checked here: responsibility of calling routine */
{
  if (uvrSwap(dest, tmp)) return -1;
  return intersectUvrs(tmp, src, dest);
}

/******************************************************************************/
static long innerUvrClean(uvr_t *dest, uvr_t *src)
{
  long dimBig = uvrDimension(dest);
  long dimSmall = uvrDimension(src);
  long i, dimCom;
  PTR row;
  if (dimBig == 0) return 0;
  if (dimSmall == 0) return dimBig;
  for (i = 0; i < dimBig; i++)
  {
    row = FfGetPtr(dest->basis, i);
    zcleanrow(row, src->basis, dimSmall, src->piv);
  }
  dimCom = zmkechelon(dest->basis, dimBig, dest->piv);
  return dimCom;
}

/****
 * 1 on error
 ***************************************************************************/
static int innerUvrComplement(uvr_t *dest, uvr_t *src)
/* src must be a subspace of dest */
/* On return, dest is a complement of src in the original dest */
{
  long dimBig = uvrDimension(dest);
  long dimSmall = uvrDimension(src);
  long dimCom;
  dimCom = innerUvrClean(dest, src);
  if (dimBig != dimSmall + dimCom)
  { MTX_ERROR1("src not a subspace of dest: %E", MTX_ERR_INCOMPAT);
    return 1;
  }
  return 0;
}

/*******
 * NULL on error
 ************************************************************************/
uvr_t *uvrComplement(uvr_t *big, uvr_t *small)
{
  uvr_t *com = duplicateUvr(big);
  if (!com) return NULL;
  if (innerUvrComplement(com, small)) return NULL;
  return com;
}

/*****
 * NULL on error
 **************************************************************************/
uvr_t *uvrAmbientComplement(uvr_t *A)
{
  long Vdim = uvrAmbientDimension(A);
  uvr_t *V = ambientVr(Vdim);
  if (!V) return NULL;
  uvr_t *B = uvrComplement(V, A);
  freeUvr(V);
  return B;
}

/******
 * NULL on error
 *************************************************************************/
uvr_t *uvrSum(uvr_t *A, uvr_t *B)
{
  uvr_t *tmp = duplicateUvr(B);
  if (!tmp) return NULL;
  long d = innerUvrClean(tmp, A);
  long dimA = uvrDimension(A);
  long *dest, *src;
  uvr_t *sum = newUvr(uvrAmbientDimension(A));
  if (!sum) return NULL;
  /* uvrAdd requires Udim = Vdim */
  if (dimA > 0)
  {
    memcpy(sum->basis, A->basis, (FfCurrentRowSize*dimA));
    dest = sum->piv + 1; src = A->piv + 1;
    memcpy(dest, src, dimA * sizeof(long));
  }
  if (d > 0)
  {
    memcpy(FfGetPtr(sum->basis, dimA), tmp->basis, (FfCurrentRowSize*d));
    dest = sum->piv + dimA + 1; src = tmp->piv + 1;
    memcpy(dest, src, d * sizeof(long));
  }
  freeUvr(tmp);
  sum->piv[0] = dimA + d;
  return sum;
}

/*****
 * 1 on error
 **************************************************************************/
int uvrAdd(uvr_t *dest, uvr_t *src)
{
  uvr_t *sum = uvrSum(dest, src);
  if (!sum) return 1;
  if (uvrSwap(sum, dest)) return 1;
  freeUvr(sum);
  return 0;
}

/*******
 * NULL on error
 ************************************************************************/
uvr_t *uvrComplementOfIntersection(uvr_t *A, uvr_t *B)
/* Returns C in A such that A = C \oplus (A \cap B) */
{
  uvr_t *cap = uvrIntersection(A, B);
  if (!cap) return NULL;
  uvr_t *C = uvrComplement(A, cap);
  freeUvr(cap);
  return C;
}

/******************************************************************************/
static void pairCleanrow(PTR rowB, PTR matB, long nor, long *piv, long nocB,
  PTR rowA, PTR matA, long nocA, PTR row2)
/* Cleans rowB by matB, then does same operations on rowA using matA */
/* Uses zcleanrow2, whence row2 : which caller responsible for initialising */
/* FfNoc immaterial at start, nocA at end */
{
  long i;
  int idx;
  FEL f;
  PTR this;
  FfSetNoc(nocB);
  zcleanrow2(rowB, matB, nor, piv, row2);
  FfSetNoc(nocA);
  this = matA;
  idx = 0;
  for (i = 1; i <= nor; i++)
  {
    f = FfExtract(row2,i);
    if (f == FF_ZERO) continue;
    /* this = FfGetPtr(matA, i-1); */
    FfAddMulRow(rowA, this, FfNeg(f));
    FfStepPtr(&this);
  }
  return;
}

/*****
 * 1 on error
 **************************************************************************/
int pairCleanmat(PTR matD, long norD, PTR matB, long norB, long *pivB,
  long nocB, PTR matC, PTR matA, long nocA)
/* Cleans matD by matB, then does same operations on matC using matA */
/* FfNoc immaterial at start, indeterminate at end */
{
  PTR rowD, rowC;
  long i;
  PTR row2;
  if (norB == 0) return;
  FfSetNoc(norB);
  row2 = FfAlloc(1);
  if (!row2)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return 1;
      }
  for (i = 0; i < norD; i++)
  {
    FfSetNoc(norB); FfMulRow(row2, FF_ZERO);
    FfSetNoc(nocB); rowD = FfGetPtr(matD, i);
    FfSetNoc(nocA); rowC = FfGetPtr(matC, i);
    pairCleanrow(rowD, matB, norB, pivB, nocB, rowC, matA, nocA, row2);
  }
  free(row2);
  return 0;
}

/******************************************************************************/
long pairMkechelon(PTR matB, long nor, long *piv, long nocB,
  PTR matA, long nocA)
/* Return value is rank of matB */
/* FfNoc immaterial at beginning, indeterminate at end */
{
  PTR rowA, rowB, row2;
  long rankB = 0, nullityB = 0, newpiv;
  FEL f;
  if (nor == 0)
  {
    piv[0] = 0;
    return 0;
  }
  rowA = matA; rowB = matB;
  FfSetNoc(nor);
  row2 = FfAlloc(1);
  while (rankB + nullityB < nor)
  {
    FfSetNoc(nocB); rowB = FfGetPtr(matB, rankB);
    FfSetNoc(nocA); rowA = FfGetPtr(matA, rankB);
    FfSetNoc(nor); FfMulRow(row2, FF_ZERO);
    pairCleanrow(rowB, matB, rankB, piv, nocB, rowA, matA, nocA, row2);
    FfSetNoc(nocB);
    newpiv = FfFindPivot(rowB, &f);
    if (newpiv == 0)
    {
      nullityB++;
      if (rankB + nullityB < nor)
      {
        PTR swapA, swapB;
        FfSetNoc(nocB);
        swapB = FfGetPtr(matB, nor - nullityB);
        FfSwapRows(rowB, swapB);
        FfSetNoc(nocA);
        swapA = FfGetPtr(matA, nor - nullityB);
        FfSwapRows(rowA, swapA);
      }
    }
    else
    {
      rankB++;
      piv[rankB] = newpiv;
    }
  }
  free(row2);
  piv[0] = rankB;
  return rankB;
}

/******************************************************************************/
long orderedMkechelon(PTR mat, long nor, long *piv)
/* Return value is rank of mat */
/* get noc from FfNoc */
{
  PTR x, dest, src;
  long l[2], i, rank = 0;
  long n = nor;
  for (i = 1; i <= n; i++)
  {
    FEL f;
    long a = 0, b, newpiv = 0, oldpiv = FfNoc + 1;
    for (b = i; b <= n;)
    {
      x = FfGetPtr(mat, b-1);
      newpiv = FfFindPivot(x, &f);
      if (newpiv == 0)
      {
        long c;
        n--;
        for (c = b; c <= n; c++)
        {
          dest = FfGetPtr(mat, c-1);
          src = FfGetPtr(mat, c);
          memcpy(dest, src, FfCurrentRowSize);
        }
        continue;
      }
      if (newpiv < oldpiv)
      {
        oldpiv = newpiv;
        a = b;
      }
      b++;
    }
    if (a == 0) break;
    if (a > i)
    {
      dest = FfGetPtr(mat, i-1);
      src = FfGetPtr(mat, a-1);
      FfSwapRows(dest, src);
    }
    piv[++rank] = oldpiv;
    x = FfGetPtr(mat, i-1);
    l[0]=1, l[1] = oldpiv;
    for (b = i+1; b <= n; b++)
    {
      PTR y = FfGetPtr(mat, b-1);
      zcleanrow(y, x, 1, l);
    }
  }
  piv[0] = rank;
  return rank;
}

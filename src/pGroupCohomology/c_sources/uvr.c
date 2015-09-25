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
//#include "report_decls.h"

/* Need: error routines, ptrPlus */

/******************************************************************************/
uvr_t *newBoundedUvr(long Vdim, long Udim)
{
  uvr_t *U = (uvr_t *) malloc(sizeof(uvr_t));
  PTR basis = NULL;
  long *piv = (long *) malloc((Udim + 1) << LONGSH);
  zsetlen(Vdim);
  if (Udim > 0) basis = zalloc(Udim);
  if (!U || !piv || ((Udim > 0) && !basis))
    AllocationError("newBoundedUvr");
  piv[0] = 0;
  U->basis = basis;
  U->piv = piv;
  U->Vdim = Vdim;
  U->Udim = Udim;
  return U;
}

/******************************************************************************/
uvr_t *newUvr(long Vdim)
{
  return newBoundedUvr(Vdim, Vdim);
}

/******************************************************************************/
uvr_t *ambientVr(long Vdim)
{
  long i;
  uvr_t *V = newBoundedUvr(Vdim, Vdim);
  PTR row;
  row = V->basis;
  for (i = 1; i <= Vdim; i++)
  {
    /* row = ptrPlus(V->basis, i-1);*/
    zinsert(row, i, F_ONE);
    V->piv[i] = i;
    zsteprow(&row);
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

/******************************************************************************/
static void uvrCopy(uvr_t *dest, uvr_t *src)
/* znoc = Vdim assumed */
{
  long dim = uvrDimension(src);
  long Vdim = uvrAmbientDimension(src);
  if (uvrAmbientDimension(dest) != Vdim)
    OtherError("uvrCopy: ambient spaces differ");
  if (dim > uvrDimensionBound(dest)) OtherError("uvrCopy: dest too small");
  memcpy(dest->piv, src->piv, (dim+1) << LONGSH);
  if (dim > 0) memcpy(dest->basis, src->basis, zsize(dim));
  return;
}

/******************************************************************************/
static uvr_t *duplicateUvr(uvr_t *old)
{
  uvr_t *new = newBoundedUvr(old->Vdim, old->Udim);
  uvrCopy(new, old);
  return new;
}

/******************************************************************************/
PTR duplicateUvrBasis(uvr_t *uvr)
{
  uvr_t *dup = duplicateUvr(uvr);
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
  ++i, zsteprow(&x1), zsteprow(&x2))
  {
    FEL f = zextract(row1,piv[i]);
    if (f == F_ZERO) continue;
    f = zdiv(f,zextract(x1,piv[i]));
    zaddmulrow(row1,x1,zneg(f));
    zaddmulrow(row2,x2,zneg(f));
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
    x1 = ptrPlus(mat1, i);
    x2 = ptrPlus(mat2, i);
    if (rank < i)
    {
      zmoverow(new1, x1);
      zmoverow(new2, x2);
    }
    cleanBirow(new1, new2, mat1, mat2, rank, piv);
    newpiv = zfindpiv(new1,&f);
    if (newpiv == 0)
    {
      zmoverow(cnew, new2);
      zcleanrow(cnew, core, crank, cpiv);
      newpiv = zfindpiv(cnew, &f);
      if (newpiv != 0)
      {
        cpiv[++crank] = newpiv;
        zsteprow(&cnew);
      }
    }
    {
      ++rank;
      piv[rank] = newpiv;
      zsteprow(&new1);
      zsteprow(&new2);
    }
  }
  piv[0] = rank;
  cpiv[0] = crank;
  return crank;
}

/******************************************************************************/
static long innerIntersectUvrs(uvr_t *A, uvr_t *B, uvr_t *dest, long dimA,
  long dimB, long nor)
{
  PTR mat1 = zalloc(nor), mat2 = zalloc(nor);
  long crank, *piv = (long *) malloc((nor+1) << LONGSH);
  if (!mat1 || !mat2 || !piv) AllocationError("innerIntersectUvrs");
  memcpy(mat1, A->basis, zsize(dimA));
  memcpy(mat2, A->basis, zsize(dimA));
  memcpy(ptrPlus(mat1, dimA), B->basis, zsize(dimB));
  crank = mkBiechelon(mat1, mat2, nor, piv, dest->basis, dest->piv);
  free(mat1); free(mat2); free(piv);
  return crank;
}

/******************************************************************************/
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
    uvrCopy(dest, B);
    return dimB;
  }
  if (dimB == Vdim)
  {
    uvrCopy(dest, A);
    return dimA;
  }
  return innerIntersectUvrs(A, B, dest, dimA, dimB, nor);
}

/******************************************************************************/
uvr_t *uvrIntersection(uvr_t *A, uvr_t *B)
{
  long Vdim = uvrAmbientDimension(A);
  long Udim = minlong(uvrDimension(A), uvrDimension(B));
  uvr_t *C = newBoundedUvr(Vdim, Udim);
  intersectUvrs(A,B,C);
  return C;
}

/******************************************************************************/
static void uvrSwap(uvr_t *A, uvr_t *B)
/* A, B must have same Vdim, and Udim=Vdim */
{
  PTR basis = A->basis;
  long *piv = A->piv;
  long Vdim = A->Vdim;
  if (B->Vdim != Vdim || A->Udim != Vdim || B->Udim != Vdim)
    OtherError("uvrSwap: unsuitable data");
  A->basis = B->basis; B->basis = basis;
  A->piv = B->piv; B->piv = piv;
  return;
}

/******************************************************************************/
long repeatIntersectUvrs(uvr_t *dest, uvr_t *src, uvr_t *tmp)
/* dest, src and tmp must all have same Vdim and all have Udim = Vdim */
/* Not checked here: responsibility of calling routine */
{
  uvrSwap(dest, tmp);
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
    row = ptrPlus(dest->basis, i);
    zcleanrow(row, src->basis, dimSmall, src->piv);
  }
  dimCom = zmkechelon(dest->basis, dimBig, dest->piv);
  return dimCom;
}

/******************************************************************************/
static void innerUvrComplement(uvr_t *dest, uvr_t *src)
/* src must be a subspace of dest */
/* On return, dest is a complement of src in the original dest */
{
  long dimBig = uvrDimension(dest);
  long dimSmall = uvrDimension(src);
  long dimCom;
  dimCom = innerUvrClean(dest, src);
  if (dimBig != dimSmall + dimCom)
    OtherError("innerUvrComplement: src not a subspace of dest");
  return;
}

/******************************************************************************/
uvr_t *uvrComplement(uvr_t *big, uvr_t *small)
{
  uvr_t *com = duplicateUvr(big);
  innerUvrComplement(com, small);
  return com;
}

/******************************************************************************/
uvr_t *uvrAmbientComplement(uvr_t *A)
{
  long Vdim = uvrAmbientDimension(A);
  uvr_t *V = ambientVr(Vdim);
  uvr_t *B = uvrComplement(V, A);
  freeUvr(V);
  return B;
}

/******************************************************************************/
uvr_t *uvrSum(uvr_t *A, uvr_t *B)
{
  uvr_t *tmp = duplicateUvr(B);
  long d = innerUvrClean(tmp, A);
  long dimA = uvrDimension(A);
  long *dest, *src;
  uvr_t *sum = newUvr(uvrAmbientDimension(A));
  /* uvrAdd requires Udim = Vdim */
  if (dimA > 0)
  {
    memcpy(sum->basis, A->basis, zsize(dimA));
    dest = sum->piv + 1; src = A->piv + 1;
    memcpy(dest, src, dimA << LONGSH);
  }
  if (d > 0)
  {
    memcpy(ptrPlus(sum->basis, dimA), tmp->basis, zsize(d));
    dest = sum->piv + dimA + 1; src = tmp->piv + 1;
    memcpy(dest, src, d << LONGSH);
  }
  freeUvr(tmp);
  sum->piv[0] = dimA + d;
  return sum;
}

/******************************************************************************/
void uvrAdd(uvr_t *dest, uvr_t *src)
{
  uvr_t *sum = uvrSum(dest, src);
  uvrSwap(sum, dest);
  freeUvr(sum);
  return;
}

/******************************************************************************
// apparently not used -- S. King
static uvr_t *uvrDirectSum(uvr_t *A, uvr_t *B)
{
  uvr_t *sum = uvrSum(A, B);
  if (uvrDimension(sum) != uvrDimension(A) + uvrDimension(B))
    OtherError("uvrDirectSum: sum not direct");
  return sum;
}

******************************************************************************/
uvr_t *uvrComplementOfIntersection(uvr_t *A, uvr_t *B)
/* Returns C in A such that A = C \oplus (A \cap B) */
{
  uvr_t *cap = uvrIntersection(A, B);
  uvr_t *C = uvrComplement(A, cap);
  freeUvr(cap);
  return C;
}

/******************************************************************************/
static void pairCleanrow(PTR rowB, PTR matB, long nor, long *piv, long nocB,
  PTR rowA, PTR matA, long nocA, PTR row2)
/* Cleans rowB by matB, then does same operations on rowA using matA */
/* Uses zcleanrow2, whence row2 : which caller responsible for initialising */
/* znoc immaterial at start, nocA at end */
{
  long i;
  int idx;
  FEL f;
  PTR this, byteptr;
  zsetlen(nocB);
  zcleanrow2(rowB, matB, nor, piv, row2);
  zsetlen(nocA);
  this = matA;
  byteptr = row2;
  idx = 0;
  for (i = 1; i <= nor; i++)
  {
    f = zextract_step(&byteptr,&idx); /*row2, i);*/
    if (f == F_ZERO) continue;
    /* this = ptrPlus(matA, i-1); */
    zaddmulrow(rowA, this, zneg(f));
    zsteprow(&this);
  }
  return;
}

/******************************************************************************/
void pairCleanmat(PTR matD, long norD, PTR matB, long norB, long *pivB,
  long nocB, PTR matC, PTR matA, long nocA)
/* Cleans matD by matB, then does same operations on matC using matA */
/* znoc immaterial at start, indeterminate at end */
{
  PTR rowD, rowC;
  long i;
  PTR row2;
  if (norB == 0) return;
  zsetlen(norB);
  row2 = zalloc(1);
  if (!row2) AllocationError("pairCleanMat");
  for (i = 0; i < norD; i++)
  {
    zsetlen(norB); zmulrow(row2, F_ZERO);
    zsetlen(nocB); rowD = ptrPlus(matD, i);
    zsetlen(nocA); rowC = ptrPlus(matC, i);
    pairCleanrow(rowD, matB, norB, pivB, nocB, rowC, matA, nocA, row2);
  }
  free(row2);
  return;
}

/******************************************************************************/
long pairMkechelon(PTR matB, long nor, long *piv, long nocB,
  PTR matA, long nocA)
/* Return value is rank of matB */
/* znoc immaterial at beginning, indeterminate at end */
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
  zsetlen(nor);
  row2 = zalloc(1);
  while (rankB + nullityB < nor)
  {
    zsetlen(nocB); rowB = ptrPlus(matB, rankB);
    zsetlen(nocA); rowA = ptrPlus(matA, rankB);
    zsetlen(nor); zmulrow(row2, F_ZERO);
    pairCleanrow(rowB, matB, rankB, piv, nocB, rowA, matA, nocA, row2);
    zsetlen(nocB);
    newpiv = zfindpiv(rowB, &f);
    if (newpiv == 0)
    {
      nullityB++;
      if (rankB + nullityB < nor)
      {
        PTR swapA, swapB;
        zsetlen(nocB);
        swapB = ptrPlus(matB, nor - nullityB);
        zswaprow(rowB, swapB);
        zsetlen(nocA);
        swapA = ptrPlus(matA, nor - nullityB);
        zswaprow(rowA, swapA);
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
/* get noc from znoc */
{
  PTR x, dest, src;
  long l[2], i, rank = 0;
  long n = nor;
  for (i = 1; i <= n; i++)
  {
    FEL f;
    long a = 0, b, newpiv = 0, oldpiv = znoc + 1;
    for (b = i; b <= n;)
    {
      x = ptrPlus(mat, b-1);
      newpiv = zfindpiv(x, &f);
      if (newpiv == 0)
      {
        long c;
        n--;
        for (c = b; c <= n; c++)
        {
          dest = ptrPlus(mat, c-1);
          src = ptrPlus(mat, c);
          zmoverow(dest, src);
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
      dest = ptrPlus(mat, i-1);
      src = ptrPlus(mat, a-1);
      zswaprow(dest, src);
    }
    piv[++rank] = oldpiv;
    x = ptrPlus(mat, i-1);
    l[0]=1, l[1] = oldpiv;
    for (b = i+1; b <= n; b++)
    {
      PTR y = ptrPlus(mat, b-1);
      zcleanrow(y, x, 1, l);
    }
  }
  piv[0] = rank;
  return rank;
}

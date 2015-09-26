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
/* uvr_decls.h : declarations from  uvr.c */
/* Author: David J. Green */
/* First version: 12 September 2000 */

#if !defined(__UVR_DECLS_INCLUDED)	/* Include only once */
#define __UVR_DECLS_INCLUDED

uvr_t *newBoundedUvr(long Vdim, long Udim);
uvr_t *newUvr(long Vdim);
uvr_t *ambientVr(long Vdim);
void freeUvr(uvr_t *uvr);
long uvrDimension(uvr_t *uvr);
boolean isAmbientSpace(uvr_t *uvr);
PTR duplicateUvrBasis(uvr_t *uvr);
uvr_t *uvrIntersection(uvr_t *A, uvr_t *B);
long repeatIntersectUvrs(uvr_t *dest, uvr_t *src, uvr_t *tmp);
/* dest, src and tmp must all have same Vdim and all have Udim = Vdim */
/* Not checked here: responsibility of calling routine */
uvr_t *uvrComplement(uvr_t *big, uvr_t *small);
uvr_t *uvrComplementOfIntersection(uvr_t *A, uvr_t *B);
/* Returns C in A such that A = C \oplus (A \cap B) */
uvr_t *uvrSum(uvr_t *A, uvr_t *B);
int *uvrAdd(uvr_t *dest, uvr_t *src);
uvr_t *uvrAmbientComplement(uvr_t *A);

int pairCleanmat(PTR matD, long norD, PTR matB, long norB, long *pivB,
  long nocB, PTR matC, PTR matA, long nocA);
/* Cleans matD by matB, then does same operations on matC using matA */
/* znoc immaterial at start, indeterminate at end */
long pairMkechelon(PTR matB, long nor, long *piv, long nocB,
  PTR matA, long nocA);
/* Return value is rank of matB */
/* znoc immaterial at beginning, indeterminate at end */
long orderedMkechelon(PTR mat, long nor, long *piv);

#endif

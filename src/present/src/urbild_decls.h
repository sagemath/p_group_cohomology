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
/* This is C code
*  urbild_decls.h : Header file listing declarations in urbild.c
*  Author: David J Green
*  First version: 13 March 2000
*/

#if !defined(__URBILD_DECLS_INCLUDED)   /* Include only once */
#define __URBILD_DECLS_INCLUDED

nFgs_t *nFgsAllocation(group_t *group, long r, char *stem);
nRgs_t *nRgsAllocation(group_t *group, long r, long s, char *stem);
void freeNFgs(nFgs_t *nFgs);
void freeNRgs(nRgs_t *nRgs);

int saveMinimalGenerators(nFgs_t *nFgs, char *outfile, group_t *group);
int saveUrbildGroebnerBasis(nRgs_t *nRgs, char *outfile, group_t *group);

Matrix_t *getMinimalGenerators(nFgs_t *nFgs, group_t *group);

/* The following function just returns numberOfHeadVectors.
   Remove it! (Simon King 2008-12)
*/
// long countGenerators(nFgs_t *nFgs);
void processNewFlaggedGenerator(nFgs_t *nFgs, PTR w, group_t *group);

void unlinkReducedVector(ngs_t *ngs, rV_t *rv);
// long headyDim(nFgs_t *nFgs);
void insertUnreducedVector(ngs_t *ngs, uV_t *uv);
uV_t *unreducedSuccessor(ngs_t *ngs, uV_t *uv);
void freeReducedVector(rV_t *rv, ngs_t *ngs);
rV_t *reducedVector(gV_t *gv, group_t *group);
inline long numberOfHeadyVectors(ngs_t *ngs);
long dimensionOfDeepestHeady(ngs_t *ngs);
int insertNewUnreducedVector(ngs_t *ngs, gV_t *gv);
int insertReducedVector(ngs_t *ngs, rV_t *rv);
gV_t *duplicate_gVtmp(ngs_t *ngs, boolean radical);
void unlinkUnreducedVector(ngs_t *ngs, uV_t *uv);
void freeUnreducedVector(uV_t *uv);
uV_t *unreducedVector(ngs_t *ngs, gV_t *gv);

int nRgsInitializeVectors(nRgs_t *nRgs, PTR im, PTR pre, long n,
  group_t *group);
int nFgsInitializeVectors(nFgs_t *nFgs, PTR mat, long n, group_t *group);

#endif

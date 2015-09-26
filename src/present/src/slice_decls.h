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
*  slice_decls.h : Header file listing declarations in slice.c
*  Author: David J Green
*  First version: 16 March 2000
*/

#if !defined(__SLICE_DECLS_INCLUDED)    /* Include only once */
#define __SLICE_DECLS_INCLUDED

PTR nodeVector(ngs_t *ngs, group_t *group, modW_t *node);
void freeGeneralVector(gV_t *gv);
// gV_t *popGeneralVector(ngs_t *ngs);
void pushGeneralVector(ngs_t *ngs, gV_t *gv);
inline int makeVectorMonic(ngs_t *ngs, gV_t *gv);
inline void multiply(PTR row, matrix_t *mat, PTR result, long r);
int createWordForest(ngs_t *ngs, group_t *group);
// void freeWordForest(ngs_t *ngs);
int destroyCurrentDimension(ngs_t *ngs);
int destroyCurrentDimensionIfAny(ngs_t *ngs);
void destroyExpansionSliceFile(ngs_t *ngs);
int selectNewDimension(ngs_t *ngs, group_t *group, long dim);
int loadExpansionSlice(ngs_t *ngs, group_t *group);
int incrementSlice(ngs_t *ngs, group_t *group);

void findLeadingMonomial(gV_t *gV, long r, group_t *group);

#endif

/*****************************************************************************
       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>

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
int makeVectorMonic(ngs_t *ngs, gV_t *gv);
int multiply(PTR row, Matrix_t *mat, PTR result, long r);
int createWordForest(ngs_t *ngs, group_t *group);
// void freeWordForest(ngs_t *ngs);
int destroyCurrentDimension(ngs_t *ngs);
int destroyCurrentDimensionIfAny(ngs_t *ngs);
int destroyExpansionSliceFile(ngs_t *ngs);
int selectNewDimension(ngs_t *ngs, group_t *group, long dim);
int loadExpansionSlice(ngs_t *ngs, group_t *group);
int incrementSlice(ngs_t *ngs, group_t *group);

void findLeadingMonomial(gV_t *gV, long r, group_t *group);

#endif

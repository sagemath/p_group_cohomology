/*****************************************************************************
       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>
       Copyright (C) 2018 Simon A. King <simon.king@uni-jena.de>

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
*  aufnahme.h : Header file listing declarations in aufnahme.c
*  Author: David J Green
*  First version: 15 March 2000
*/

#if !defined(__AUFNAHME_DECLS_INCLUDED) /* Include only once */
#define __AUFNAHME_DECLS_INCLUDED

int nFgsAufnahme(nFgs_t *nFgs, group_t *group);
int nRgsAufnahme(nRgs_t *nRgs, group_t *group);
int urbildAufnahme(nRgs_t *nRgs, group_t *group, PTR result);
int nRgsAssertReducedVectors(nRgs_t *nRgs, PTR mat, long num, group_t *group);
void possiblyNewKernelGenerator(nRgs_t *nRgs, PTR pw, group_t *group);

#endif

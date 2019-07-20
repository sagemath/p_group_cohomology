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
*  fp_decls.h : Header file listing declarations in fileplus.c
*  Author: David J Green
*  First version: 29 July 1996
*
*/

#if !defined(__FP_DECLS_INCLUDED)	/* Include only once */
#define __FP_DECLS_INCLUDED

FILE *os_fopenplus(char *name, int mode);
int alterhdrplus(FILE *fp, long nor);
FILE *writehdrplus(char *name, long fl, long nor, long noc);
FILE *readhdrplus(char *name, long *fl, long *nor, long *noc);
/* Opens existing file for read/write */
/* Assigns to fl, nor, noc, unless NULL */
void PrintMatrixFile(char *matname);
long numberOfRowsStored(char *name);

#endif

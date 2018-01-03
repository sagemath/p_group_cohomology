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
/*
* This is C code
* aufloesung_decls.h : Header file listing declarations in aufloesung.c
* Author: David J Green
* First version: 15 March 2000 from resol_decls.h
*/

#if !defined(__AUFLOESUNG_DECLS_INCLUDED)   /* Include only once */
#define __AUFLOESUNG_DECLS_INCLUDED

#include "meataxe.h"

char *resolStem(long Gsize, char *Gname);
char *resolDir(long Gsize);
resol_t *newResolutionRecord(void);

long rankProj(resol_t *resol, long n);
long dimIm(resol_t *resol, long n);
void setRankProjCoverForModule(resol_t *resol, long rkP0, long dimM);

void initializeDateCommand(char *stem);

char *numberedFile(long n, char *stem, char *ext);
/* String returned must be used at once, never reused, never freed. */
/* extension WITHOUT dot */

nRgs_t *loadDifferential(resol_t *resol, long n);

void readKnownResolution(resol_t *resol, long N);

/* PTR preimages(nRgs_t *nRgs, PTR images, long noi, group_t *group); */

int makeThisDifferential(resol_t *resol, long n);
/* n must be at least two */
int readOrConstructThisProjective(resol_t *resol, long n);
int ensureThisProjectiveKnown(resol_t *resol, long n);
int ensureThisUrbildGBKnown(resol_t *resol, long n);

#endif

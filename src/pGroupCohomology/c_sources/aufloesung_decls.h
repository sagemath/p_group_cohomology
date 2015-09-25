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
/*
* This is C code
* aufloesung_decls.h : Header file listing declarations in aufloesung.c
* Author: David J Green
* First version: 15 March 2000 from resol_decls.h
*/

#if !defined(__AUFLOESUNG_DECLS_INCLUDED)	/* Include only once */
#define __AUFLOESUNG_DECLS_INCLUDED

#include "meataxe.h"

char *differentialFile(resol_t *resol, long n);
/* String returned must be used at once, never reused, never freed. */
/* Represents d_n : P_n -> P_{n-1} */
char *urbildGBFile(resol_t *resol, long n);
/* String returned must be used at once, never reused, never freed. */
/* Represents urbild Groebner basis for d_n : P_n -> P_{n-1} */

nRgs_t *nRgsStandardSetup(resol_t *resol, long n, PTR mat);
/* mat should be a block of length rankProj(resol, n-1) x rankProj(resol, n) */

char *resolStem(long Gsize, char *Gname);
char *resolDir(long Gsize);
resol_t *newResolutionRecord(void);
resol_t *newResolWithGroupLoaded (char *RStem, char *GStem, long N);
void freeResolutionRecord(resol_t *resol);

long rankProj(resol_t *resol, long n);
long dimIm(resol_t *resol, long n);
void setRankProj(resol_t *resol, long n, long r);
void setRankProjCoverForModule(resol_t *resol, long rkP0, long dimM);

void initializeDateCommand(char *stem);

char *numberedFile(long n, char *stem, char *ext);
/* String returned must be used at once, never reused, never freed. */
/* extension WITHOUT dot */

matrix_t *makeFirstDifferential(resol_t *resol);
nRgs_t *loadDifferential(resol_t *resol, long n);
nRgs_t *loadUrbildGroebnerBasis(resol_t *resol, long n);

void readKnownResolution(resol_t *resol, long N);

void innerPreimages(nRgs_t *nRgs, PTR images, long noi, group_t *group,
  PTR preimages);
/* PTR preimages(nRgs_t *nRgs, PTR images, long noi, group_t *group); */

void makeThisDifferential(resol_t *resol, long n);
/* n must be at least two */
void readOrConstructThisProjective(resol_t *resol, long n);
void ensureThisProjectiveKnown(resol_t *resol, long n);
void ensureThisUrbildGBKnown(resol_t *resol, long n);

#endif

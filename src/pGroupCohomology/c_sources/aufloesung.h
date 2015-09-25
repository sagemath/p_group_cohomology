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
*  aufloesung.h : Header file for aufloesung.c
*  Author: David J Green
*  First version: 15 March 2000 from resol.h
*/

#if !defined(__AUFLOESUNG_INCLUDED)	/* Include only once */
#define __AUFLOESUNG_INCLUDED

#include "nDiag.h"
#include "urbild_decls.h"
#include "aufnahme_decls.h"
#include "nBuchberger_decls.h"
#include "slice_decls.h"

#define NUMPROJ_BASE 10
#define NUMPROJ_INCREMENT 5

struct resolutionRecord
{
  group_t *group;
  char *stem;
  char *moduleStem;
  long numproj, numproj_alloc;
  long *projrank; /* projrank[n] = free rank of nth projective */
  long *Imdim; /* Imdim[n] = dim of Im d_n (which is a submod of P_{n-1}) */
};
typedef struct resolutionRecord resol_t;

#endif

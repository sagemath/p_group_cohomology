/*****************************************************************************
       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>
       Copyright (C) 2015 Simon A. King <simon.king@uni-jena.de>

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
*  nDiag.h : Type definitions for urbild.c etc
*  Author: David J Green
*  First version: 15 March 2000 from diag.h
*/

#if !defined(__NDIAG_INCLUDED)  /* Include only once */
#define __NDIAG_INCLUDED

#include "pcommon.h"
#include "meataxe.h"
#include "pgroup.h"
#include "pgroup_decls.h"

#define RANK_UNKNOWN -1
#define ZERO_BLOCK -1
#define NONE -1

/* For dimLoaded */
#define NOTHING_TO_EXPAND -1
#define NO_BUCHBERGER_REQUIRED -2

/* Status of modW_t's */
#define NO_DIVISOR -1
#define SCALAR_MULTIPLE -2
#define NONSCALAR_MULTIPLE -3

#ifndef PGROUP_LOADED
typedef int boolean;
static const boolean true = 1;
static const boolean false = 0;
#endif

struct generalVector;
typedef struct generalVector gV_t;

struct generalVector
{
  PTR w;
  FEL coeff;
  long dim;
  long len;
  long block;
  int col;
  boolean radical;
};

struct unreducedVector;
typedef struct unreducedVector uV_t;

struct unreducedVector
{
  gV_t *gv;
  long index;
  uV_t *prev, *next;
};

struct moduleWord;
typedef struct moduleWord modW_t;

struct reducedVector;
typedef struct reducedVector rV_t;

struct reducedVector
{
  gV_t *gv;
  modW_t *node;
  rV_t *next, *prev;
  long expDim;
};

struct moduleWord
{
  modW_t *parent, **child;
  rV_t *divisor;
  long qi;     /* index of quotient path */
  long status;
};

struct newCommonGeneratingSet;
typedef struct newCommonGeneratingSet ngs_t;

struct newCommonGeneratingSet
{
  long r, s; /* r is rank of ambient free, s rank of preimage (0 for fgs) */
  rV_t *firstReduced;
  rV_t *lastReduced;
  uV_t *unreducedHeap;
  modW_t **proot;
  gV_t *gVwaiting;
  long pnontips; /* present guess at the number of nontips */
  long expDim;
  long targetRank;
  long dimLoaded;
  long blockLoaded;
  long nops; /* number of products */
  PTR thisBlock;
  PTR w;
  PTR theseProds;
  long blockSize;
  char stem[MAXLINE];
  long prev_pnon, unfruitful;
};

struct newFlaggedGeneratingSet
{
  boolean finished;
  boolean nRgsUnfinished;
  ngs_t *ngs;
  long max_unfruitful;
};

typedef struct newFlaggedGeneratingSet nFgs_t;

struct newResentfulGeneratingSet
{
  nFgs_t *ker; /* ker is the hgs for the known part of kernel */
  ngs_t *ngs;
  long prev_ker_pnon, overshoot;
};

typedef struct newResentfulGeneratingSet nRgs_t;

// some macros related with gV_t
#if !defined(NULL)
#define NULL NULL
#endif
extern gV_t *generalVectorTemplate(long nor);

#if !defined(popGeneralVector)
#define popGeneralVector(ngs) ({gV_t *GV_; ((ngs)->gVwaiting) ? ({ GV_ = (ngs)->gVwaiting; (ngs)->gVwaiting = NULL; GV_;}) : ({ GV_ = generalVectorTemplate((ngs)->r + (ngs)->s); GV_;});})
#endif


#endif

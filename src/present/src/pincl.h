/* ========================== Present =============================
   pincl.h : Header file for pincl.c; defines important types

   (C) Copyright 2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#ifndef PGROUP_LOADED
#include "pgroup.h"
#include "pgroup_decls.h"
#endif

struct subgroupInclusion
{
  group_t *H, *G; /* G the group, H the subgroup */
  char *stem;
  matrix_t *ima; /* Inclusion matrix */
};

typedef struct subgroupInclusion inclus_t;

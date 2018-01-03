/*****************************************************************************
   pincl.h : Header file for pincl.c; defines important types

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

#if !defined(__PINCL_INCLUDED)  /* Include only once */
#define __PINCL_INCLUDED

#ifndef PGROUP_LOADED
#include "pgroup.h"
#include "pgroup_decls.h"
#endif

struct subgroupInclusion
{
  group_t *H, *G; /* G the group, H the subgroup */
  char *stem;
  Matrix_t *ima; /* Inclusion matrix */
};

typedef struct subgroupInclusion inclus_t;

#endif

/*****************************************************************************
   pincl.h : Header file for pincl.c; defines important types

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

#if !defined(__PINCL_INCLUDED)	/* Include only once */
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

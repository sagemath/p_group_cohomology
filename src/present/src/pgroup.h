/*****************************************************************************
   pgroup.h : Header file for pgroup.c; defines important types

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

#if !defined(__PGROUP_INCLUDED) /* Include only once */
#define __PGROUP_INCLUDED

#include "pcommon.h"
#include "meataxe.h"

typedef int boolean;
static const boolean true = 1;
static const boolean false = 0;
#define PGROUP_LOADED

typedef long yesno;
static const yesno yes = 1;
static const yesno no = -1;
static const yesno unknown = 0;

struct pathnode;
typedef struct pathnode path_t;

struct pathnode
{
  long index;
  char *path;
  path_t **child;
  path_t *parent;
  long lastArrow;
  long depth; /* depth of node in tree, i.e. length of path */
  long dim;   /* Dimension of path, for Jennings case */
};

struct groupRecord
{
  char *stem;
  long arrows;
  long nontips;
  long maxlength;
  long mintips;
  long p;
  char ordering;
  char **nontip;
  path_t *root;
  path_t *lroot;
  Matrix_t **action;
  Matrix_t **laction;
  Matrix_t **bch;
  long *dim;
  long *dS;           /* depth Steps: for resolution only */
};

typedef struct groupRecord group_t;

struct JenningsWord
{
  char *path;
  long length;
  long dimension;
};

typedef struct JenningsWord JenningsWord_t;

#endif

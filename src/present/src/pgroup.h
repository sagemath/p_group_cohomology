/*****************************************************************************
   pgroup.h : Header file for pgroup.c; defines important types

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

#if !defined(__PGROUP_INCLUDED)	/* Include only once */
#define __PGROUP_INCLUDED

#include "pcommon.h"
#include "meataxe.h"
#include "perror_decls.h"

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
  matrix_t **action;
  matrix_t **laction;
  matrix_t **bch;
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

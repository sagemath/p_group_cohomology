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
/* module.h : header file for module.c; defines module_t */

#if !defined(__MODULE_INCLUDED)	/* Include only once */
#define __MODULE_INCLUDED

#ifndef PGROUP_LOADED
#include "pgroup.h"
#endif
#include "pgroup_decls.h"

struct moduleRecord
{
  char *stem;
  long dim;
  Matrix_t **action;
};

typedef struct moduleRecord module_t;

#endif

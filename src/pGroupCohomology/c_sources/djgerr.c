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
*  djgerr.c : Error handling routines for my p-group cohomology programs
*  Author: David J Green
*  First version: 18 June 1996 from existing Error routines in pr.c
*/

#include "pcommon.h"
#include "meataxe.h"

void AllocationError(const char *s)
{
  printf("Allocation Error in %s.\n", s);
  exit(1);
}

void OtherError(const char *s)
{
  printf("Error: %s.\n", s);
  exit(1);
}

void MatrixLoadingError(const char *s)
{
  printf("Matrix Loading Error: %s.\n", s);
  exit(1);
}

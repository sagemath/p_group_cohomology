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
*  uvr.h : Header file for uvr.c
*  Author: David J Green
*  First version: 12 September 2000
*/

#if !defined(__UVR_INCLUDED)	/* Include only once */
#define __UVR_INCLUDED

struct vectorSubspace
{
  PTR basis;
  long *piv;
  long Vdim, Udim;
};
typedef struct vectorSubspace uvr_t;

#endif

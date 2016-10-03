/*****************************************************************************
       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>
       Copyright (C) 2018 Simon A. King <simon.king@uni-jena.de>

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
*  nBuchberger_decls.h : Header file listing declarations in nBuchberger.c
*  Author: David J Green
*  First version: 15 March 2000
*/

#if !defined(__NBUCHBERGER_DECLS_INCLUDED)  /* Include only once */
#define __NBUCHBERGER_DECLS_INCLUDED

int nFgsBuchberger(nFgs_t *nFgs, group_t *group);
int nRgsBuchberger(nRgs_t *nRgs, group_t *group);

#endif

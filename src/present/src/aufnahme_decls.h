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
*  aufnahme_decls.h : Header file listing declarations in aufnahme.c
*  Author: David J Green
*  First version: 15 March 2000
*/

#if !defined(__AUFNAHME_DECLS_INCLUDED)	/* Include only once */
#define __AUFNAHME_DECLS_INCLUDED

int nFgsAufnahme(nFgs_t *nFgs, group_t *group);
int nRgsAufnahme(nRgs_t *nRgs, group_t *group);
int urbildAufnahme(nRgs_t *nRgs, group_t *group, PTR result);
int nRgsAssertReducedVectors(nRgs_t *nRgs, PTR mat, long num, group_t *group);
void possiblyNewKernelGenerator(nRgs_t *nRgs, PTR pw, group_t *group);

#endif

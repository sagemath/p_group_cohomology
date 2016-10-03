/*****************************************************************************
   pincl_decls.h : Header files listing declarations in pincl.c

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

#if !defined(__PINCL_DECLS_INCLUDED)    /* Include only once */
#define __PINCL_DECLS_INCLUDED

inclus_t *newInclusionRecord(group_t *G, group_t *H, const char *stem);
void freeInclusionRecord(inclus_t *inclus);

int makeInclusionMatrix(inclus_t *inclus);
int saveInclusionMatrix(inclus_t *inclus);
int loadInclusionMatrix(inclus_t *inclus);

#endif

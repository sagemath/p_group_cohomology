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
#if !defined(__UNF_DECLS_INCLUDED)	/* Include only once */
#define __UNF_DECLS_INCLUDED

matrix_t *unfoldMatrix(matrix_t *matSrc, long r);
matrix_t *foldedMatrix(matrix_t *matSrc, long r);
matrix_t *allImages(group_t *group, matrix_t *genIms, long r);
matrix_t *allImagesOfUnfolded(group_t *group, matrix_t *genIms);
matrix_t *fullMatrixOfDifferential(group_t *group, char *nameD, long r);
void makeFullMatrixOfDifferential(group_t *group, char *nameD, char *nameDest,
long r);
void makeUnfoldedMatrix(group_t *group, char *nameSrc, char *nameDest, long r);
void matclean(matrix_t *dirt, matrix_t *brush, long *piv);

#endif

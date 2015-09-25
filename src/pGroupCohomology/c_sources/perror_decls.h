/*****************************************************************************
   perror_decls.h : Header file listing declarations in perror.c

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

#if !defined(__PERROR_DECLS_INCLUDED)	/* Include only once */
#define __PERROR_DECLS_INCLUDED

void AllocationError(const char *s);
void OtherError(const char *s);
void MatrixLoadingError(const char *s);

#endif

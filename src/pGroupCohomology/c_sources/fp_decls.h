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
*  fp_decls.h : Header file listing declarations in fileplus.c
*  Author: David J Green
*  First version: 29 July 1996
*
*/

#if !defined(__FP_DECLS_INCLUDED)	/* Include only once */
#define __FP_DECLS_INCLUDED

FILE *os_fopenplus(char *name, int mode);
int alterhdrplus(FILE *fp, long nor);
FILE *writehdrplus(char *name, long fl, long nor, long noc);
FILE *readhdrplus(char *name, long *fl, long *nor, long *noc);
/* Opens existing file for read/write */
/* Assigns to fl, nor, noc, unless NULL */
void PrintMatrixFile(char *matname);
long numberOfRowsStored(char *name);

#endif

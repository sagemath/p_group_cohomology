/*****************************************************************************
   pcommon.h : header file common to most programs

       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>
       Copyright (C) 2018 Simon A. King <simon.king@uni-jena.de>

    This file is part of p_group_cohomology.

    p_group_cohomoloy is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 2 of the License, or
    (at your option) any later version.

    p_group_cohomoloy is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.
*****************************************************************************/

#if !defined(__PCOMMON_INCLUDED)    /* Include only once */
#define __PCOMMON_INCLUDED

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define DJG_DEBUG

#define MAXLINE 240
#define MAXLENGTH 3200 /* paths of this length assumed to be zero */
#define INVALID -1
#define NOT_EVEN_INVALID -2

#define ARROWNAMES "abcdefghijklmnopqrstuvwxyz"
#define MAXARROW 26

#define AUL_DEGREE 4 /* Use autolifting to determine preimages up to
                        this degree */

/* #define CHAR_ODD */
/* #define BIG_MACHINE */

/* Consequences of char_odd and big_machine */
#ifdef BIG_MACHINE
  #define BLOCK_SIZE 2048
#else
  #define BLOCK_SIZE 2048
#endif

#ifdef CHAR_ODD
  #define MAX_UNFRUITFUL 1
  #define MAX_OVERSHOOT 5
#else
  #define MAX_UNFRUITFUL 2
  #define MAX_OVERSHOOT 1
#endif

#endif

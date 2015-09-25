/* ======================== Coho progs ============================
   pcommon.h : header file common to most programs
               parameters I may often want to tweak

   (C) Copyright 1999-2006 David J. Green <green@minet.uni-jena.de>
   Department of Mathematics, University of Jena,
   D-07737 Jena, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#if !defined(__PCOMMON_INCLUDED)	/* Include only once */
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

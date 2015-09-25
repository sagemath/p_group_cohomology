/* ========================== Present =============================
   wgb.h : Header file for wgb.c

   (C) Copyright 1999 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"
#define TERMS_PER_LINE 10

struct wgbFolder
{
  group_t *group;
  char **mintip;
  PTR ptr;
  long mintips;
  long *index;
  JenningsWord_t **jenny;
  long so_far;
};

typedef struct wgbFolder wgbFolder_t;

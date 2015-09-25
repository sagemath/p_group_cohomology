/* ========================== Present =============================
   pincl_decls.h : Header files listing declarations in pincl.c

   (C) Copyright 2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

inclus_t *newInclusionRecord(group_t *G, group_t *H, char *stem);
void freeInclusionRecord(inclus_t *inclus);

void makeInclusionMatrix(inclus_t *inclus);
void saveInclusionMatrix(inclus_t *inclus);
void loadInclusionMatrix(inclus_t *inclus);

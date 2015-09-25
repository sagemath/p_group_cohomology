/* ========================== Present =============================
   pincl.c : routines for group inclusions

   (C) Copyright 2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pincl.h"

/******************************************************************************/
inclus_t *newInclusionRecord(group_t *G, group_t *H, char *stem)
{
  inclus_t *inclus = (inclus_t *) malloc(sizeof(inclus_t));
  if (!inclus) AllocationError("newInclusionRecord");
  inclus->G = G;
  inclus->H = H;
  inclus->stem = djg_strdup(stem);
  inclus->ima = NULL;
  return inclus;
}

/******************************************************************************/
void freeInclusionRecord(inclus_t *inclus)
{
  if (inclus->stem) free(inclus->stem);
  if (inclus->ima) matfree(inclus->ima);
  free(inclus);
  return;
}

/******************************************************************************/
void makeInclusionMatrix(inclus_t *inclus)
/* Sets znoc = G->nontips */
{
  group_t *G = inclus->G, *H = inclus->H;
  long Hnum = H->arrows;
  long Hsize = H->nontips, Gsize = G->nontips;
  char name[MAXLINE];
  long a, i;
  PTR prev, this;
  path_t *p;
  matrix_t **Hgens = allocateMatrixList(G, Hnum);
  matrix_t *ima = matalloc(zfl, Hsize, Gsize);
  if (!ima) AllocationError("makeInclusionMatrix");
  if (!G->bch) OtherError("makeInclusionMatrix: G->bch not loaded");
  strext(name, inclus->stem, ".irg");
  loadGeneralRegularActionMatrices(G, Hgens, name, Hnum);
  basisChangeReg2Nontips(G, Hgens, Hnum);
  zinsert(ima->d, 1, F_ONE);
  for (i = 1; i < Hsize; i++)
  {
    p = H->root + i;
    prev = ptrPlus(ima->d, p->parent->index);
    this = ptrPlus(ima->d, i);
    a = p->lastArrow;
    zmaprow(prev, Hgens[a]->d, Gsize, this);
  }
  freeMatrixList(Hgens);
  inclus->ima = ima;
  return;
}

/******************************************************************************/
void saveInclusionMatrix(inclus_t *inclus)
{
  char name[MAXLINE];
  strext(name, inclus->stem, ".ima");
  if (matsave(inclus->ima,name) != 0)
    OtherError("Saving in saveInclusionMatrix");
  return;
}

/******************************************************************************/
void loadInclusionMatrix(inclus_t *inclus)
{
  matrix_t *ima;
  char name[MAXLINE];
  strext(name, inclus->stem, ".ima");
  ima = matload(name);
  if (!ima)
    OtherError("Loading in loadInclusionMatrix");
  if (ima->nor != inclus->H->nontips)
    OtherError("loadInclusionMatrix: wrong number of rows");
  if (ima->noc != inclus->G->nontips)
    OtherError("loadInclusionMatrix: wrong number of cols");
  inclus->ima = ima;
  return;
}

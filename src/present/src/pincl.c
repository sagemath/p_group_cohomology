/*****************************************************************************
  pincl.c : routines for group inclusions

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

#include "pincl.h"
#include "meataxe.h"

/******************************************************************************/
static char *inclusionMatrixFile(inclus_t *inclus)
/* String returned must be used at once, never reused, never freed. */
{
  static char buffer[MAXLINE];
  sprintf(buffer, "%s.ima", inclus->stem);
  return buffer;
}

/****
 * NULL on error
 ***************************************************************************/
inclus_t *newInclusionRecord(group_t *G, group_t *H, char *stem)
{
  inclus_t *inclus = (inclus_t *) malloc(sizeof(inclus_t));
  if (!inclus)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return NULL;
      }
  inclus->G = G;
  inclus->H = H;
  if (inclus->stem = djg_strdup(stem) == NULL)
  { free(inclus);
    return NULL;
  }
  inclus->ima = NULL;
  return inclus;
}

/******************************************************************************/
void freeInclusionRecord(inclus_t *inclus)
{
  if (inclus->stem) free(inclus->stem);
  if (inclus->ima) MatFree(inclus->ima);
  free(inclus);
  return;
}

/*****
 * 1 on error
 **************************************************************************/
int makeInclusionMatrix(inclus_t *inclus)
/* Sets FfNoc = G->nontips */
{
  group_t *G = inclus->G, *H = inclus->H;
  long Hnum = H->arrows;
  long Hsize = H->nontips, Gsize = G->nontips;
  char name[MAXLINE];
  long a, i;
  PTR prev, this;
  path_t *p;
  Matrix_t **Hgens = allocateMatrixList(G, Hnum);
  if (!Hgens) return 1;
  Matrix_t *ima = MatAlloc(FfOrder, Hsize, Gsize);
  if (!ima)
      {
          freeMatrixList(Hgens);
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return 1;
      }
  if (!G->bch)
  {
      MatFree(ima);
      freeMatrixList(Hgens);
      MTX_ERROR("G->bch not loaded");
      return 1;
  }
  strext(name, inclus->stem, ".irg");
  if (loadGeneralRegularActionMatrices(G, Hgens, name, Hnum))
  { freeMatrixList(Hgens);
    MatFree(ima);
    return 1;
  }
  if (basisChangeReg2Nontips(G, Hgens, Hnum)) return 1;
  FfInsert(ima->d, 0, FF_ONE);
  for (i = 1; i < Hsize; i++)
  {
    p = H->root + i;
    prev = FfGetPtr(ima->d, p->parent->index);
    this = FfGetPtr(ima->d, i);
    a = p->lastArrow;
    FfMapRow(prev, Hgens[a]->d, Gsize, this);
  }
  freeMatrixList(Hgens);
  inclus->ima = ima;
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int saveInclusionMatrix(inclus_t *inclus)
{
  if (MatSave(inclus->ima, inclusionMatrixFile(inclus))) return 1;
  return 0;
}

/***
 * 1 on error
 ****************************************************************************/
int loadInclusionMatrix(inclus_t *inclus)
{
  Matrix_t *ima;
  ima = MatLoad(inclusionMatrixFile(inclus));
  if (!ima) return 1;
  if (ima->nor != inclus->H->nontips)
  {
      MatFree(ima);
      MTX_ERROR1("wrong number of rows: %E", MTX_ERR_INCOMPAT);
      return 1;
  }
  if (ima->noc != inclus->G->nontips)
  {
      MatFree(ima);
      MTX_ERROR1("wrong number of cols: %E", MTX_ERR_INCOMPAT);
      return 1;
  }
  inclus->ima = ima;
  return 0;
}

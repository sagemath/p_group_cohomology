/* ========================== Present =============================
   mnt.c : Make Nontips file .nontips

   (C) Copyright 1999 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   Copyright (C) 2015 Simon A. King <simon.king@uni-jena.de>

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
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"
MTX_DEFINE_FILE_INFO

static MtxApplicationInfo_t AppInfo = {
    "makeNontips",

    "Makes .nontips file using regular representation",

    "Reads <stem>.reg\n"
    "Writes <stem>.nontips\n"
    "\n"
    "SYNTAX\n"
    "    makeNontips -O <Ordering> <p> <stem>\n"
    "\n"
    "ARGUMENTS\n"
    "    <p> .................... the underlying prime\n"
    "    <stem> ................. label of a prime power group\n"
    "\n"
    "OPTIONS\n"
    "    -O <Ordering> should be one of\n"
    "           LL  for LengthLex\n"
    "           RLL for ReverseLengthLex (default)\n"
    "           (J for Jennings is currently not supported)\n"
    MTX_COMMON_OPTIONS_DESCRIPTION
    "\n"
};

static MtxApplication_t *App = NULL;

/***
 * control variables
 ****/

static group_t *group = NULL;


/****
 * 1 on error
 ***************************************************************************/
int Init(int argc, const char *argv[])
{
  App = AppAlloc(&AppInfo,argc,argv);
  if (App == NULL)
    return 1;

  group = newGroupRecord();
  if (!group)
  { MTX_ERROR1("Cannot allocate group: %E", MTX_ERR_NOMEM);
    return 1;
  }

  const char * ord_text = AppGetTextOption(App, "-O", "RLL");
  if (strcmp(ord_text,"LL") == 0)
    group->ordering = 'L';
  else if (strcmp(ord_text,"RLL") == 0)
    group->ordering = 'R';
  else if (strcmp(ord_text, "J") == 0)
  { group->ordering = 'J';
    MTX_ERROR1("Jennings order is currently not supported: %E", MTX_ERR_BADARG);
    return 1;
  }
  else
  { MTX_ERROR2("Unkown order %s: %E", ord_text, MTX_ERR_BADARG);
    return 1;
  }

  if (AppGetArguments(App, 2, 2) < 0)
    return 1;

  group->p = atoi(App->ArgV[0]);
  if (FfSetField(group->p)<0) return 1;

  if ((group->stem = mtx_strdup(App->ArgV[1])) == NULL) return 1;
  /* printf("%s: chosen order is %c\n", pinfo.name, group->ordering); */
  return 0;
}

static void Cleanup()
{
    if (App != NULL)
        AppFree(App);
    freeGroupRecord(group);
}


/******************************************************************************/
static path_t *rightFactor(path_t *root, path_t *parent, long *aa)
/* Know parent has length >= 1 */
{
  path_t *p;
  long pl = parent->depth;
  long i;
  if (pl > MAXLENGTH)
  {
    MTX_ERROR1(
      "Path of length > %d found. Increase value of MAXLENGTH in pcommon.h",
      MAXLENGTH);
    return NULL;
  }
  for (p = parent, i = pl; i >= 2; i--, p = p->parent)
    aa[i-2] = p->lastArrow;
  for (i = 0, p = root; i < pl - 1; p = p->child[aa[i++]]);
  return p;
}

/******************************************************************************/
static FILE *writeNontipsHeader(group_t *group)
{
  FILE *fp;
  char ntpfile[MAXLINE];
  strext(ntpfile, group->stem, ".nontips");
  fp = fopen(ntpfile, "w");
  if (!fp)
  { MTX_ERROR("writeNontipsHeader: opening file");
    return NULL;
  }
  fprintf (fp, "%ld %ld %ld %ld %ld %c\n", group->arrows, group->nontips,
    group->maxlength, group->mintips, group->p, group->ordering);
  return fp;
}

/******************************************************************************/
static int writeOutNontips(group_t *group, long *index)
/* initially, group->mintips set, group->maxlength not */
{
  FILE *fp;
  long nontips = group->nontips;
  path_t *root = group->root;
  long i;
  group->maxlength = group->root[nontips-1].depth;
  fp = writeNontipsHeader(group);
  if (!fp) return 1;
  for (i = 0; i < nontips; i++)
    fprintf(fp, "%s;\n", root[index[i]].path);
  fclose(fp);
  return 0;
}

/******************************************************************************/
static int writeOutJenningsNontips(group_t *group, JenningsWord_t **word)
/* initially, group->maxlength set, group->mintips not */
{
  FILE *fp;
  long arrows = group->arrows;
  long nontips = group->nontips;
  long i;
  group->mintips = (arrows * (arrows + 1)) / 2;
  fp = writeNontipsHeader(group);
  if (!fp) return 1;
  for (i = 0; i < nontips; i++)
    fprintf(fp, "%s;\n", word[i]->path);
  fclose(fp);
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
int constructNontips_LengthLex(group_t *group)
/* sets mintips but not maxlength */
{
  long arrows = group->arrows;
  long nontips = group->nontips;
  path_t *root = group->root;
  Matrix_t **action = group->action;
  char newname;
  long aa[MAXLENGTH];
  long *index;
  Matrix_t *ptr = MatAlloc(FfOrder, nontips+1, FfNoc);
  Matrix_t *rec = MatAlloc(FfOrder, nontips+1, FfNoc);

  PTR rec_parent, rec_child, ptr_child;
  long pl, prev_starts, this_starts, so_far, mintips;
  long i, a;
  path_t *p, *parent, *q;
  FEL f;
  index = (long *) malloc(nontips * sizeof(long));
  if (!ptr || !index || !rec)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return 1;
  }
  FfInsert(ptr->Data,0,FF_ONE);
  FfInsert(rec->Data,0,FF_ONE);
  if (!(ptr->PivotTable = NREALLOC(ptr->PivotTable, int, ptr->Noc)))
    {
        MTX_ERROR1("Cannot allocate pivot table (size %d)",ptr->Noc);
        return -1;
    }
  ptr->PivotTable[0] = 0;
  this_starts = 0; so_far = 1; mintips = 0;
  for (pl = 1; so_far > this_starts; pl++)
  {
    prev_starts = this_starts;
    this_starts = so_far;
    for (i = prev_starts; i < this_starts; i++)
    {
      parent = root + i;
      rec_parent = MatGetPtr(rec, parent->index);
      if (pl > 1)
      {
        /* parent has length >= 1, so factors as b.q, b arrow, q path
           for each a want to check if q.a reduces */
        q = rightFactor(root, parent, aa);
        if (!q) return 1;
      }
      for (a = 0; a < arrows; a++)
      {
        if (pl > 1 && q->child[a] == NULL) continue;
        rec_child = MatGetPtr(rec, so_far);
        ptr_child = MatGetPtr(ptr, so_far);
        FfMapRow(rec_parent, action[a]->Data, nontips, rec_child);
        memcpy(ptr_child, rec_child, FfCurrentRowSize);
        FfCleanRow(ptr_child, ptr->Data, so_far, ptr->PivotTable);
        ptr->PivotTable[so_far] = FfFindPivot(ptr_child, &f);
        if (ptr->PivotTable[so_far] == -1)
        {
          /* New mintip found */
          mintips++;
        }
        else
        {
          /* New nontip found */
          p = root + so_far;
          p->parent = parent;
          p->lastArrow = a;
          p->depth = pl;
          parent->child[a] = p;
          p->path = (char *) malloc((pl+1) * sizeof(char));
          if (!p->path)
          { MTX_ERROR1("%E", MTX_ERR_NOMEM);
            return 1;
          }
          if (pl > 1) strcpy(p->path, parent->path);
          newname = arrowName(a);
          if (newname == ' ') return 1;
          p->path[pl-1] = newname;
          p->path[pl] = '\0';
          so_far++;
        }
      }
    }
  }
  MatFree(ptr);
  MatFree(rec);
  for (i = 0; i < nontips; i++) index[i] = i;
  group->mintips = mintips;
  if (writeOutNontips(group, index)) return 1;
  free(index);
  return 0;
}

/*****
 * 1 on error
 **************************************************************************/
int constructNontips_ReverseLengthLex(group_t *group)
/* sets mintips but not maxlength */
{
  long nontips = group->nontips;
  long arrows = group->arrows;
  path_t *root = group->root;
  Matrix_t **action = group->action;
  long aa[MAXLENGTH];
  long *index;
  char newname;
  PTR rec_parent, rec_child, ptr_child;
  Matrix_t *rad;
  PTR dest;
  Matrix_t *rec;
  long pl, prev_starts, this_starts, so_far, mintips;
  long i, a, raddim, offset;
  path_t *p, *parent, *q;
  FEL f;
  index = (long *) malloc(nontips * sizeof(long));
  rad = MatAlloc(FfOrder, nontips * arrows, FfNoc);
  rec = MatAlloc(FfOrder, nontips + 1, FfNoc);
  if (!index || !rad || !rec)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return 1;
  }
  memcpy(rad->Data, action[0]->Data, (rad->RowSize*arrows * nontips));
  if ((raddim = MatEchelonize(rad))<0) return 1;

  /* Below, we will stack the images of rad under action of arrows.
   * For that purpose, we need some scratch space.
   */
  PTR scratch = FfAlloc(arrows * nontips);
  if (!scratch)
  { MTX_ERROR1("%E",MTX_ERR_NOMEM);
    return 1;
  }

  index[0] = 0;
  FfInsert(rec->Data,0,FF_ONE);
  this_starts = 0; so_far = 1; mintips = 0;
  for (pl = 1; so_far > this_starts; pl++)
  {
    prev_starts = this_starts;
    this_starts = so_far;
    if (raddim > 0)
    {
      for (a = 0, dest = scratch; a < arrows; a++, dest = FfGetPtr(dest, raddim))
      { if (innerRightProduct(rad, action[a], dest)) return 1; }
      /* now, for the next round, transfer the scratch space to rad->Data,
       * so that we can newly echelonise.
       */
      rad->Nor = arrows*raddim;
      rad->Data = SysRealloc(rad->Data, rad->RowSize*rad->Nor);
      if (!rad->Data)
      {
          MTX_ERROR1("%E", MTX_ERR_NOMEM);
          return 1;
      }
      memcpy(rad->Data, scratch, rad->RowSize*rad->Nor);
      raddim = MatEchelonize(rad);
    }
    /* In the following loop, we will append up to
     * (this_starts-prev_starts)*arrows rows. Hence,
     * we need to reallocate.
     */
    rad->Data = SysRealloc(rad->Data, rad->RowSize*(raddim + (this_starts-prev_starts)*arrows));
    for (i = prev_starts; i < this_starts; i++)
    {
      parent = root + i;
      rec_parent = MatGetPtr(rec, parent->index);
      if (pl > 1)
      {
        /* parent has length >= 1, so factors as b.q, b arrow, q path
           for each a want to check if q.a reduces */
        q = rightFactor(root, parent, aa);
        if (!q) return 1;
      }
      for (a = arrows-1; a >= 0; a--)
      {
        if (pl > 1 && q->child[a] == NULL) continue;
        offset = raddim + so_far - this_starts;
        rec_child = MatGetPtr(rec, so_far);
        ptr_child = MatGetPtr(rad, offset);
        FfMapRow(rec_parent, action[a]->Data, nontips, rec_child);
        memcpy(ptr_child, rec_child, FfCurrentRowSize);
        FfCleanRow(ptr_child, rad->Data, offset, rad->PivotTable);
        rad->PivotTable[offset] = FfFindPivot(ptr_child, &f);
        rad->Nor = offset+1;
        if (rad->PivotTable[offset] == -1)
        {
          /* New mintip found */
          mintips++;
        }
        else
        {
          /* New nontip found */
          p = root + so_far;
          p->parent = parent;
          p->lastArrow = a;
          p->depth = pl;
          parent->child[a] = p;
          p->path = (char *) malloc((pl+1) * sizeof(char));
          if (!p->path)
          { MTX_ERROR1("%E", MTX_ERR_NOMEM);
            return 1;
          }
          if (pl > 1) strcpy(p->path, parent->path);
          newname = arrowName(a);
          if (newname==' ') return 1;
          p->path[pl-1] = newname;
          p->path[pl] = '\0';
          so_far++;
        }
      }
    }
    for (i = this_starts; i < so_far; i++)
      index[i] = so_far - 1 - i + this_starts;
  }
  MatFree(rad);
  MatFree(rec);
  group->mintips = mintips;
  if (writeOutNontips(group, index)) return 1;
  free(index);
  return 0;
}

/******************************************************************************/
static void swapJenningsWords(JenningsWord_t **word, long i1, long i2)
{
  JenningsWord_t *tmp = word[i1];
  word[i1] = word[i2];
  word[i2] = tmp;
  return;
}

/******************************************************************************/
static void sortJenningsWords(group_t *group, JenningsWord_t **word)
{
  long gap, i, j;
  long nontips = group->nontips;
  for (gap = nontips/2; gap > 0; gap /= 2)
    for (i = gap; i < nontips; i++)
      for (j = i - gap; j >= 0 && smallerJenningsWord(word[j], word[j+gap]);
           j -= gap)
        swapJenningsWords(word, j, j+gap);
  return;
}

/****
 * NULL on error
 ***************************************************************************/
static char *newPath(long a, char *prev)
{
  char *this;
  long l = strlen(prev) + 2;
  if (prev[0] == '(') l = 2; /* prev is (1), length zero */
  this = (char *) malloc(l * sizeof(char));
  if (!this)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  this[0] = arrowName(a);
  if (this[0]==' ') return NULL;
  this[1] = '\0';
  if (l > 2) strcat(this,prev);
  return this;
}

/****
 * 1 on error
 ***************************************************************************/
int constructNontips_Jennings(group_t *group)
/* sets maxlength but not mintips */
{
  long arrows, nontips;
  long lastTime, *dim;
  long p = group->p;
  long i, a, offset, j;
  JenningsWord_t **word, *words, *w, *parent;
  if (loadDimensions(group)) return 1;
  dim = group->dim;
  arrows = dim[0];
  group->arrows = arrows;
  for (nontips = 1, i = 0; i < arrows; nontips *= p, i++);
  group->nontips = nontips;
  FfSetNoc(nontips);
  group->maxlength = (p-1) * arrows;
  word = (JenningsWord_t **)
    malloc(nontips * sizeof(JenningsWord_t *));
  words = (JenningsWord_t *)
    malloc(nontips * sizeof(JenningsWord_t));
  if (!words || !word)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return 1;
  }
  for (i = 0, w = words; i < nontips; i++, w++)
    word[i] = w;
  word[0]->path = "(1)";
  word[0]->length = 0;
  word[0]->dimension = 0;
  lastTime = 1;
  for (a = 0, lastTime = 1; a < arrows; a++, lastTime *= p)
  {
    for (i = 0, offset = 0; i < p-1; i++, offset += lastTime)
    {
      for (j = 0; j < lastTime; j++)
      {
        parent = word[j + offset];
        w = word[j + offset + lastTime];
        w->path = newPath(a, parent->path);
        if (!w->path) return 1;
        w->length = parent->length + 1;
        w->dimension = parent->dimension + dim[a+1];
      }
    }
  }
  sortJenningsWords(group, word);
  return writeOutJenningsNontips(group, word);
}

/******************************************************************************/
int main(int argc, const char *argv[])
{
  if (Init(argc, argv))
  { MTX_ERROR("Error parsing command line. Try --help");
    exit(1);
  }

  if (group->ordering == 'J')
  { if (constructNontips_Jennings(group)) exit(1); }
  else
  {
    if (readRegFileHeader(group)) exit(1);
    if (loadRegularActionMatrices(group)) exit(1);
    group->root = allocatePathTree(group);
    if (!group->root) exit(1);
    if (group->ordering == 'L')
    { if (constructNontips_LengthLex(group)) exit(1); }
    else
    { if (constructNontips_ReverseLengthLex(group)) exit(1); }
  }
  Cleanup();
  exit(0);
}

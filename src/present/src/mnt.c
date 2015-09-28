/* ========================== Present =============================
   mnt.c : Make Nontips file .nontips

   (C) Copyright 1999 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"
MTX_DEFINE_FILE_INFO

static char *helptext[] = {
"SYNTAX",
"   makeNontips -O <Ordering> <p> <stem>",
"",
"   Reads <stem>.reg, writes <stem>.nontips",
"   <p> is the underlying prime",
"   Option -O is obligatory; <Ordering> should be one of",
"       LL  for LengthLex",
"       RLL for ReverseLengthLex",
"       J   for Jennings (also reads file <stem>.dims)",
"",
"DESCRIPTION",
"   Makes .nontips file from regular representation.",
NULL};

static proginfo_t pinfo =
  { "makeNontips", "Makes .nontips file using regular representation",
    "$Revision: 30_April_1998", helptext };

/****
 * 1 on error
 ***************************************************************************/
int InterpretCommandLine(int argc, char *argv[], group_t *group)
{
  //register int i;
  char *this;
  initargs(argc,argv,&pinfo);
  if (zgetopt("O:") != 'O')
    { MTX_ERROR1("%E", MTX_ERR_BADARG);
      return 1;
    }
  if (strcmp(opt_text,"LL") == 0)
    group->ordering = 'L';
  else if (strcmp(opt_text,"RLL") == 0)
    group->ordering = 'R';
  else if (strcmp(opt_text, "J") == 0)
    group->ordering = 'J';
  else
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
  zgetopt("");
  if (opt_ind != argc - 2)
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
  this = argv[opt_ind++];
  group->p = atoi(this);
  FfSetField(group->p);
  this = argv[opt_ind++];
  if ((group->stem = mtx_strdup(this)) == NULL) return 1;
  /* printf("%s: chosen order is %c\n", pinfo.name, group->ordering); */
  return 0;
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
  long *piv, *index;
  /*
  PTR ptr = FfAlloc(nontips + 1);
  PTR rec = FfAlloc(nontips + 1);
  */
  Matrix_t *ptr = MatAlloc(FfOrder, nontips+1, FfNoc);
  Matrix_t *rec = MatAlloc(FfOrder, nontips+1, FfNoc);
  
  PTR rec_parent, rec_child, ptr_child;
  long pl, prev_starts, this_starts, so_far, mintips;
  long i, a;
  path_t *p, *parent, *q;
  FEL f;
  /*piv = (long *) malloc((nontips + 2) * sizeof(long));*/
  index = (long *) malloc(nontips * sizeof(long));
  /*if (!ptr || !piv || !index || !rec)*/
  if (!ptr || !index || !rec)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return 1;
  }
  FfInsert(ptr->Data,0,FF_ONE);
  FfInsert(rec->Data,0,FF_ONE);
  MatPivotize(ptr);
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
          if (newname==" ") return 1;
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
  /*Matrix_t *ptr = MatAlloc(FfOrder, nontips + 1, FfNoc); /* Initializes */
  PTR rec_parent, rec_child, ptr_child;
  Matrix_t *rad;
  PTR dest;
  Matrix_t *rec;
  /*Matrix_t mat;  /* NOT just a pointer to a matrix! */
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
  /*mat.Field = FfOrder; mat.Noc = nontips; mat.Data = ptr;*/
  memcpy(rad->Data, action[0]->Data, (FfCurrentRowSize*arrows * nontips));
  raddim = MatEchelonize(rad);
  index[0] = 0;
  FfInsert(rec->Data,0,FF_ONE);
  this_starts = 0; so_far = 1; mintips = 0;
  for (pl = 1; so_far > this_starts; pl++)
  {
    prev_starts = this_starts;
    this_starts = so_far;
    if (raddim > 0)
    {
      for (a = 0, dest = rad->Data; a < arrows; a++, dest = FfGetPtr(dest, raddim))
      { if (innerRightProduct(rad, action[a], dest)) return 1; }
      raddim = MatEchelonize(rad);
    }
    for (i = prev_starts; i < this_starts; i++)
    {
      parent = root + i;
      rec_parent = FfGetPtr(rec, parent->index);
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
          if (newname==" ") return 1;
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
  if (this[0]==" ") return NULL;
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
  return (writeOutJenningsNontips(group, word);
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  group_t *group;
  MtxInitLibrary();
  group = newGroupRecord();
  if (!group) exit(1);
  if (InterpretCommandLine(argc, argv, group)) exit(1);
  if (group->ordering == 'J')
    if (constructNontips_Jennings(group)) exit(1);
  else
  {
    if (readRegFileHeader(group)) exit(1);
    if (loadRegularActionMatrices(group)) exit(1);
    group->root = allocatePathTree(group);
    if (!group->root) exit(1);
    if (group->ordering == 'L')
      if (constructNontips_LengthLex(group)) exit(1);
    else
      if (constructNontips_ReverseLengthLex(group)) exit(1);
  }
  freeGroupRecord(group);
  exit(0);
}

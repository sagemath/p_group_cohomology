/* ========================== Present =============================
   wgb.c : Write Groebner Basis

   (C) Copyright 1999 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "wgb.h"
MTX_DEFINE_FILE_INFO

static boolean mintipsOnly;

static char *helptext[] = {
"SYNTAX",
"   writeGroebnerBasis [-t] <Stem>",
"",
"   Reads <Stem>.gens, <Stem>.nontips; writes <Stem>.groebner",
"   With option -t, writes mintips only, to file <Stem>.mintips",
"",
"DESCRIPTION",
"   Write out the Groebner basis.",
NULL};

static proginfo_t pinfo =
  { "writeGroebnerBasis", "Write out Groebner basis",
    "$Revision: 30_April_1998", helptext };

/*****
 * 1 on error
 **************************************************************************/
int InterpretCommandLine(int argc, char *argv[], group_t *group)
{
  //register int i;
  char *this;
  initargs(argc,argv,&pinfo);
  sprintf(invalid,
    "Invalid command line. Issue \"%s -help\" for more details", pinfo.name);
  mintipsOnly = false;
  while (zgetopt("t") != OPT_END)
    mintipsOnly = true;
  if (opt_ind != argc - 1)
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
  this = argv[opt_ind++];
  if (group->stem = djg_strdup(this) == NULL) return 1;
  return 0;
}

/******************************************************************************/
wgbFolder_t *newDmsFolder(group_t *group)
{
  wgbFolder_t *folder;
  long i;
  long mintips = group->mintips;
  char *mintip0;
  JenningsWord_t **jenny, *jenny0;
  folder = (wgbFolder_t *) malloc(sizeof(wgbFolder_t));
  if (!folder)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  folder->mintips = mintips;
  if (mintipsOnly)
    folder->ptr = NULL;
  else
  {
    folder->ptr = zalloc(mintips);
    if (!folder->ptr)
      { free(folder);
        MTX_ERROR1("%E", MTX_ERR_NOMEM);
        return NULL;
      }
  }
  folder->index = (long *) malloc(mintips * sizeof(long));
  mintip0 = (char *) malloc((group->maxlength + 2) * mintips * sizeof(char));
  folder->mintip = (char **) malloc(mintips * sizeof(char *));
  if (!folder->index || !mintip0 || !folder->mintip)
  { free(folder);
    MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  for (i = 0; i < mintips; i++)
  {
    folder->index[i] = i;
    folder->mintip[i] = mintip0 + i * (group->maxlength + 2);
  }
  if (group->ordering == 'J')
  {
    jenny0 = (JenningsWord_t *) malloc(mintips * sizeof(JenningsWord_t));
    jenny = (JenningsWord_t **) malloc(mintips * sizeof(JenningsWord_t *));
    if (!jenny0 || !jenny)
      { free(folder);
        MTX_ERROR1("%E", MTX_ERR_NOMEM);
        return NULL;
      }
    for (i = 0; i < mintips; i++) jenny[i] = jenny0 + i;
    folder->jenny = jenny;
  }
  folder->so_far = 0;
  return folder;
}

/******************************************************************************/
void freeDmsFolder(wgbFolder_t *folder)
{
  free(folder->mintip[0]);
  free(folder->mintip);
  if (!mintipsOnly) free(folder->ptr);
  free(folder->index);
  if (folder->group->ordering == 'J')
  {
    free(folder->jenny[0]);
    free(folder->jenny);
  }
  free(folder);
  return;
}

/*******************************************************************************
* static void writeMinusValue(group_t *group, FILE *fp, PTR minusValue)
* {
  register long j, i;
  int thisline;
  long coeff;
  long p = group->p;
  long nontips = group->nontips;
  boolean isLL = (group->ordering == 'L');
  thisline = 1;
  for (i = 0; i < nontips; i++)
  {
    j = isLL ? nontips - i - 1 : i;
    coeff = FfToInt(FfExtract(minusValue, j+1));
    if (coeff == 0) continue;
    coeff = (2 * coeff > p) ? coeff - p : coeff;
    if (thisline++ == TERMS_PER_LINE)
    {
      fprintf(fp,"\n");
      thisline = 1;
    }
    fprintf(fp," ");
    if (coeff < 0)
    {
      fprintf(fp,"- ");
      coeff *= -1;
    }
    else fprintf(fp,"+ ");
    if (coeff != 1) fprintf(fp, "%d ", coeff);
    fprintf(fp,"%s", group->root[j].path);
  }
  return;
}
*/

/******************************************************************************/
static void writeMinusValue(group_t *group, FILE *fp, PTR minusValue)
{
  register long j, i;
  int thisline;
  long coeff;
  //long p = group->p;
  long nontips = group->nontips;
  boolean isLL = (group->ordering == 'L');
  thisline = 1;
  for (i = 0; i < nontips; i++)
  {
    j = isLL ? nontips - i - 1 : i;
    coeff = FfToInt(FfExtract(minusValue, j+1));
    if (coeff == 0) continue;
    if (thisline++ == TERMS_PER_LINE)
    {
      fprintf(fp,"\n");
      thisline = 1;
    }
    fprintf(fp," ");
    fprintf(fp,"+ ");
    if (coeff != 1) fprintf(fp, "%ld ", coeff);
    fprintf(fp,"%s", group->root[j].path);
  }
  return;
}

/****
 * 1 on error
 ***************************************************************************/
int recordThisMintip(wgbFolder_t *folder, path_t *p, long a)
{
  group_t *group = folder->group;
  FEL m_one = zsub(FF_ZERO, FF_ONE);
  long this = folder->so_far++;
  char newname
  char *mintip = folder->mintip[this];
  strcpy(mintip, p->path);         /* N.B. Even if p has length zero, these  */
  newname = arrowName(a);          /* lines ensure path p.a written to */
  if (newname==" ") return 1;
  mintip[p->depth + 1] = '\0';     /* mintip. No corruption problems either. */
  if (!mintipsOnly)
  {
    PTR src = FfGetPtr(group->action[a]->d, p->index);
    PTR dest = FfGetPtr(folder->ptr, this);
    zmoverow(dest, src);
    zmulrow(dest, m_one);
  }
  if (group->ordering == 'J')
  {
    JenningsWord_t *jenny = folder->jenny[this];
    jenny->path = mintip;
    jenny->length = p->depth + 1;
    jenny->dimension = pathDimension(group, p) + group->dim[a+1];
  }
  return 0;
}

/******************************************************************************/
int writeGB(wgbFolder_t *folder)
{
  FILE *fp;
  char mshfile[MAXLINE];
  group_t *group = folder->group;
  long i, this;
  char *mintip;
  PTR minusValue;
  strext(mshfile, group->stem, mintipsOnly ? ".mintips" : ".groebner");
  fp = fopen(mshfile,"w");
  if (!fp)
  { MTX_ERROR("Cannot open file");
    return 1;
  }
  fprintf(fp, "%s for stem %s\n",
    mintipsOnly ? "Mintips" : "Groebner basis", group->stem);
  for (i = 0; i < folder->mintips; i++)
  {
    this = folder->index[i];
    mintip = folder->mintip[this];
    fprintf(fp, "%s", mintip);
    if (!mintipsOnly)
    {
      minusValue = FfGetPtr(folder->ptr, this);
      writeMinusValue(group, fp, minusValue);
    }
    fprintf(fp, ";\n");
  }
  fclose(fp);
  return 0;
}

/****
 * 1 on error
 ***************************************************************************/
int findGB(wgbFolder_t *folder)
{
  group_t *group = folder->group;
  path_t *root = group->root;
  path_t *lroot = group->lroot;
  long arrows = group->arrows;
  long nontips = group->nontips;
  long i, a, b;
  path_t *p, *lp, *q, *lq; //, *r;
  for (i = 1; i < nontips; i++)
  {
    p = root + i;
    for (a = 0; a < arrows; a++)
    {
      if (p->child[a] != NULL) continue; /* p.a a nontip */
      /* p.a a tip */
      if (p->depth != 0)
      /* if p does have depth 0, arrow a is itself a (nec. minimal) tip */
      {
        /* usual case */
        lp = lroot + i; /* lp is p from left path tree */
        b = lp->lastArrow;
        lq = lp->parent; /* p = b.lq, lq in left path tree */
        q = root + lq->index; /* q is lq from (right) path tree */
        if (!q->child[a]) continue; /* q.a a tip, so p.a not minimal */
      }
      /* p.a a mintip */
      if (recordThisMintip(folder, p, a)) return 1;
    }
  }
  return 0;
}

/******************************************************************************/
static void swapIndices(long *index, long i1, long i2)
{
  long tmp = index[i1];
  index[i1] = index[i2];
  index[i2] = tmp;
  return;
}

/******************************************************************************/
static void sortGBJennings(wgbFolder_t *folder)
{
  JenningsWord_t **jenny = folder->jenny;
  long *index = folder->index;
  long gap, i, j;
  long mintips = folder->mintips;
  for (gap = mintips/2; gap > 0; gap /= 2)
    for (i = gap; i < mintips; i++)
      for (j = i - gap;
           j >= 0 && smallerJenningsWord(jenny[index[j]], jenny[index[j+gap]]);
           j -= gap)
        swapIndices(index, j, j+gap);
  return;
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  wgbFolder_t *folder;
  group_t *group;
  MtxInitLibrary();
  group = newGroupRecord();
  if (!group) exit(1);
  if (InterpretCommandLine(argc, argv, group)) exit(1);
  if (loadNonTips(group)) exit(1);
  if (group->ordering == 'J')
  { if (loadDimensions(group)) exit(1);
  }
  if (buildPathTree(group)) exit(1);
  if (buildLeftPathTree(group)) exit(1);
  if (!mintipsOnly)
  { if (loadActionMatrices(group)) exit(1);
  }
  folder = newDmsFolder(group);
  if (findGB(folder)) exit(1);
  if (group->ordering == 'J') sortGBJennings(folder);
  if (writeGB(folder)) exit(1);
  freeDmsFolder(folder);
  freeGroupRecord(group);
  exit(0);
}

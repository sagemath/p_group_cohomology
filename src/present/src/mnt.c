/* ========================== Present =============================
   mnt.c : Make Nontips file .nontips

   (C) Copyright 1999 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"

static char *helptext[] = {
"SYNTAX",
"	makeNontips -O <Ordering> <p> <stem>",
"",
"	Reads <stem>.reg, writes <stem>.nontips",
"	<p> is the underlying prime",
"	Option -O is obligatory; <Ordering> should be one of",
"		LL  for LengthLex",
"		RLL for ReverseLengthLex",
"		J   for Jennings (also reads file <stem>.dims)",
"",
"DESCRIPTION",
"	Makes .nontips file from regular representation.",
NULL};

static proginfo_t pinfo =
  { "makeNontips", "Makes .nontips file using regular representation",
    "$Revision: 30_April_1998", helptext };

/******************************************************************************/
void InterpretCommandLine(int argc, char *argv[], group_t *group)
{
  //register int i;
  char invalid[MAXLINE];
  char *this;
  sprintf(invalid,
    "Invalid command line. Issue \"%s -help\" for more details", pinfo.name);
  initargs(argc,argv,&pinfo);
  if (zgetopt("O:") != 'O')
    OtherError(invalid);
  if (strcmp(opt_text,"LL") == 0)
    group->ordering = 'L';
  else if (strcmp(opt_text,"RLL") == 0)
    group->ordering = 'R';
  else if (strcmp(opt_text, "J") == 0)
    group->ordering = 'J';
  else OtherError(invalid);
  zgetopt("");
  if (opt_ind != argc - 2)
    OtherError(invalid);
  this = argv[opt_ind++];
  group->p = atoi(this);
  zsetfield(group->p);
  this = argv[opt_ind++];
  group->stem = djg_strdup(this);
  /* printf("%s: chosen order is %c\n", pinfo.name, group->ordering); */
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
    char errstring[MAXLINE];
    sprintf(errstring,
      "Path of length > %d found. Increase value of MAXLENGTH in pcommon.h",
      MAXLENGTH);
    OtherError(errstring);
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
  if (!fp) OtherError("writeNontipsHeader: opening file");
  fprintf (fp, "%ld %ld %ld %ld %ld %c\n", group->arrows, group->nontips,
    group->maxlength, group->mintips, group->p, group->ordering);
  return fp;
}

/******************************************************************************/
static void writeOutNontips(group_t *group, long *index)
/* initially, group->mintips set, group->maxlength not */
{
  FILE *fp;
  long nontips = group->nontips;
  path_t *root = group->root;
  long i;
  group->maxlength = group->root[nontips-1].depth;
  fp = writeNontipsHeader(group);
  for (i = 0; i < nontips; i++)
    fprintf(fp, "%s;\n", root[index[i]].path);
  fclose(fp);
  return;
}

/******************************************************************************/
static void writeOutJenningsNontips(group_t *group, JenningsWord_t **word)
/* initially, group->maxlength set, group->mintips not */
{
  FILE *fp;
  long arrows = group->arrows;
  long nontips = group->nontips;
  long i;
  group->mintips = (arrows * (arrows + 1)) / 2;
  fp = writeNontipsHeader(group);
  for (i = 0; i < nontips; i++)
    fprintf(fp, "%s;\n", word[i]->path);
  fclose(fp);
  return;
}

/******************************************************************************/
void constructNontips_LengthLex(group_t *group)
/* sets mintips but not maxlength */
{
  long arrows = group->arrows;
  long nontips = group->nontips;
  path_t *root = group->root;
  matrix_t **action = group->action;
  long aa[MAXLENGTH];
  long *piv, *index;
  PTR ptr = zalloc(nontips + 1); /* Initializes */
  PTR rec = zalloc(nontips + 1); /* Initializes */
  PTR rec_parent, rec_child, ptr_child;
  long pl, prev_starts, this_starts, so_far, mintips;
  long i, a;
  path_t *p, *parent, *q;
  FEL f;
  piv = (long *) malloc((nontips + 2) * sizeof(long));
  index = (long *) malloc(nontips * sizeof(long));
  if (!ptr || !piv || !index || !rec)
    AllocationError("constructNontips_LengthLex");
  zinsert(ptr,1,F_ONE);
  zinsert(rec,1,F_ONE);
  zmkechelon(ptr, 1, piv);
  this_starts = 0; so_far = 1; mintips = 0;
  for (pl = 1; so_far > this_starts; pl++)
  {
    prev_starts = this_starts;
    this_starts = so_far;
    for (i = prev_starts; i < this_starts; i++)
    {
      parent = root + i;
      rec_parent = ptrPlus(rec, parent->index);
      if (pl > 1)
      {
        /* parent has length >= 1, so factors as b.q, b arrow, q path
           for each a want to check if q.a reduces */
        q = rightFactor(root, parent, aa);
      }
      for (a = 0; a < arrows; a++)
      {
        if (pl > 1 && q->child[a] == NULL) continue;
        rec_child = ptrPlus(rec, so_far);
        ptr_child = ptrPlus(ptr, so_far);
        zmaprow(rec_parent, action[a]->d, nontips, rec_child);
        zmoverow(ptr_child, rec_child);
        zcleanrow(ptr_child, ptr, so_far, piv);
        piv[so_far+1] = zfindpiv(ptr_child, &f);
        if (piv[so_far+1] == 0)
        {
          /* New mintip found */
          mintips++;
        }
        else
        {
          /* New nontip found */
          piv[0]++;
          p = root + so_far;
          p->parent = parent;
          p->lastArrow = a;
          p->depth = pl;
          parent->child[a] = p;
          p->path = (char *) malloc((pl+1) * sizeof(char));
          if (!p->path) AllocationError("cNLL: 2");
          if (pl > 1) strcpy(p->path, parent->path);
          p->path[pl-1] = arrowName(a); p->path[pl] = '\0';
          so_far++;
        }
      }
    }
  }
  free(piv);
  for (i = 0; i < nontips; i++) index[i] = i;
  group->mintips = mintips;
  writeOutNontips(group, index);
  free(index);
  return;
}

/******************************************************************************/
void constructNontips_ReverseLengthLex(group_t *group)
/* sets mintips but not maxlength */
{
  long nontips = group->nontips;
  long arrows = group->arrows;
  path_t *root = group->root;
  matrix_t **action = group->action;
  long aa[MAXLENGTH];
  long *piv, *index;
  PTR ptr = zalloc(nontips + 1); /* Initializes */
  PTR rec_parent, rec_child, ptr_child;
  PTR rad, dest, rec;
  matrix_t mat;
  long pl, prev_starts, this_starts, so_far, mintips;
  long i, a, raddim, offset;
  path_t *p, *parent, *q;
  FEL f;
  piv = (long *) malloc((arrows * nontips + 2) * sizeof(long));
  index = (long *) malloc(nontips * sizeof(long));
  rad = zalloc(nontips * arrows);
  rec = zalloc(nontips + 1);
  if (!ptr || !piv || !index || !rad || !rec)
    AllocationError("constructNontips_ReverseLengthLex");
  mat.fl = zfl; mat.noc = nontips; mat.d = ptr;
  memcpy(rad, action[0]->d, zsize(arrows * nontips));
  raddim = zmkechelon(rad, arrows * nontips, piv);
  if (raddim > 0) memcpy(ptr, rad, zsize(raddim));
  index[0] = 0;
  zinsert(rec,1,F_ONE);
  this_starts = 0; so_far = 1; mintips = 0;
  for (pl = 1; so_far > this_starts; pl++)
  {
    prev_starts = this_starts;
    this_starts = so_far;
    if (raddim > 0)
    {
      mat.nor = raddim;
      for (a = 0, dest = rad; a < arrows; a++, zadvance(&dest, raddim))
        innerRightProduct(&mat, action[a], dest);
      raddim = zmkechelon(rad, raddim * arrows, piv);
      if (raddim > 0) memcpy(ptr, rad, zsize(raddim));
    }
    for (i = prev_starts; i < this_starts; i++)
    {
      parent = root + i;
      rec_parent = ptrPlus(rec, parent->index);
      if (pl > 1)
      {
        /* parent has length >= 1, so factors as b.q, b arrow, q path
           for each a want to check if q.a reduces */
        q = rightFactor(root, parent, aa);
      }
      for (a = arrows-1; a >= 0; a--)
      {
        if (pl > 1 && q->child[a] == NULL) continue;
        offset = raddim + so_far - this_starts;
        rec_child = ptrPlus(rec, so_far);
        ptr_child = ptrPlus(ptr, offset);
        zmaprow(rec_parent, action[a]->d, nontips, rec_child);
        zmoverow(ptr_child, rec_child);
        zcleanrow(ptr_child, ptr, offset, piv);
        piv[offset+1] = zfindpiv(ptr_child, &f);
        if (piv[offset+1] == 0)
        {
          /* New mintip found */
          mintips++;
        }
        else
        {
          /* New nontip found */
          piv[0]++;
          p = root + so_far;
          p->parent = parent;
          p->lastArrow = a;
          p->depth = pl;
          parent->child[a] = p;
          p->path = (char *) malloc((pl+1) * sizeof(char));
          if (!p->path) AllocationError("cNRLL: 2");
          if (pl > 1) strcpy(p->path, parent->path);
          p->path[pl-1] = arrowName(a); p->path[pl] = '\0';
          so_far++;
        }
      }
    }
    for (i = this_starts; i < so_far; i++)
      index[i] = so_far - 1 - i + this_starts;
  }
  free(piv);
  group->mintips = mintips;
  writeOutNontips(group, index);
  free(index);
  return;
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

/******************************************************************************/
static char *newPath(long a, char *prev)
{
  char *this;
  long l = strlen(prev) + 2;
  if (prev[0] == '(') l = 2; /* prev is (1), length zero */
  this = (char *) malloc(l * sizeof(char));
  if (!this) AllocationError("newPath");
  this[0] = arrowName(a);
  this[1] = '\0';
  if (l > 2) strcat(this,prev);
  return this;
}

/******************************************************************************/
void constructNontips_Jennings(group_t *group)
/* sets maxlength but not mintips */
{
  long arrows, nontips;
  long lastTime, *dim;
  long p = group->p;
  long i, a, offset, j;
  JenningsWord_t **word, *words, *w, *parent;
  loadDimensions(group);
  dim = group->dim;
  arrows = dim[0];
  group->arrows = arrows;
  for (nontips = 1, i = 0; i < arrows; nontips *= p, i++);
  group->nontips = nontips;
  zsetlen(nontips);
  group->maxlength = (p-1) * arrows;
  word = (JenningsWord_t **)
    malloc(nontips * sizeof(JenningsWord_t *));
  words = (JenningsWord_t *)
    malloc(nontips * sizeof(JenningsWord_t));
  if (!words || !word) AllocationError("constructNontips_Jennings");
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
        w->length = parent->length + 1;
        w->dimension = parent->dimension + dim[a+1];
      }
    }
  }
  sortJenningsWords(group, word);
  writeOutJenningsNontips(group, word);
  return;
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  group_t *group;
  mtxinit();
  group = newGroupRecord();
  InterpretCommandLine(argc, argv, group);
  if (group->ordering == 'J')
    constructNontips_Jennings(group);
  else
  {
    readRegFileHeader(group);
    loadRegularActionMatrices(group);
    group->root = allocatePathTree(group);
    if (group->ordering == 'L')
      constructNontips_LengthLex(group);
    else
      constructNontips_ReverseLengthLex(group);
  }
  freeGroupRecord(group);
  exit(0);
}

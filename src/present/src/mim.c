/* ========================== Present =============================
   mim.c : Make Inclusion Matrix

   (C) Copyright 2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pincl.h"
#include "pincl_decls.h"
MTX_DEFINE_FILE_INFO

static char *helptext[] = {
"SYNTAX",
"   makeInclusionMatrix <Gstem> <Hstem> <incStem>",
"",
"   Reads <Gstem>.nontips, <Gstem>.gens, <Gstem>.bch,",
"   <Hstem>.nontips, <incStem>.irg",
"   Writes <incStem>.ima",
"",
"DESCRIPTION",
"   Make matrix for inclusion of H in G.",
NULL};

static proginfo_t pinfo =
  { "makeInclusionMatrix", "Make matrix for inclusion of subgroup",
    "$Revision: 06_June_2000", helptext };

/******************************************************************************/
struct controlVariables
{
  char Gstem[MAXLINE];
  char Hstem[MAXLINE];
  char incStem[MAXLINE];
};

typedef struct controlVariables control_t;

/******************************************************************************/
control_t *newController(void)
{
  control_t *control = (control_t *) malloc(sizeof(control_t));
  if (!control)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
  return control;
}

/******************************************************************************/
void freeController(control_t *control)
{
  free(control);
  return;
}

/******************************************************************************/
int InterpretCommandLine(int argc, char *argv[], control_t *control)
{
  //register int i;
  char *this;
  initargs(argc,argv,&pinfo);
  sprintf(invalid,
    "Invalid command line. Issue \"%s -help\" for more details", pinfo.name);
  while (zgetopt("") != OPT_END);
  if (opt_ind != argc - 3)
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
  this = argv[opt_ind++];
  strcpy(control->Gstem, this);
  this = argv[opt_ind++];
  strcpy(control->Hstem, this);
  this = argv[opt_ind++];
  strcpy(control->incStem, this);
  return 0;
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  group_t *G, *H;
  inclus_t *inclus;
  control_t *control;
  MtxInitLibrary();
  control = newController();
  if (InterpretCommandLine(argc, argv, control)) exit(1);
  G = namedGroupRecord(control->Gstem);
  H = namedGroupRecord(control->Hstem);
  inclus = newInclusionRecord(G, H, control->incStem);
  if (!inclus) exit(1);
  if (loadNonTips(G)) exit(1);
  buildPathTree(G);
  loadActionMatrices(G);
  loadBasisChangeMatrices(G);
  if (loadNonTips(H)) exit(1);
  buildPathTree(H);
  if (makeInclusionMatrix(inclus)) exit(1);
  if (saveInclusionMatrix(inclus)) exit(1);
  freeInclusionRecord(inclus);
  freeGroupRecord(G);
  freeGroupRecord(H);
  exit(0);
}

/* ========================== Present =============================
   mam.c : Make Action Matrices

   (C) Copyright 1999-2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"

static char *helptext[] = {
"SYNTAX",
"	makeActionMatrices [-q <q>] [-b] [-l] <stem>",
"",
"	Reads <stem>.nontips, <stem>.reg",
"	Writes <stem>.gens, <stem>.lgens, <stem>.bch",
"	With option -b, only writes <stem>.bch",
"	With option -l, only writes <stem>.lgens",
"	(-b -l writes .bch and .lgens)",
"	Option -q: Work over F_q rather than over F_p",
"",
"DESCRIPTION",
"	Make matrices for actions of generators.",
NULL};

static proginfo_t pinfo =
  { "makeActionMatrices", "Make matrices for actions of generators",
    "$Revision: 31_May_2001", helptext };

/******************************************************************************/
struct controlVariables
{
  char stem[MAXLINE];
  boolean bchOnly;
  boolean leftOnly;
  long q;
};

typedef struct controlVariables control_t;

/******************************************************************************/
control_t *newController(void)
{
  control_t *control = (control_t *) malloc(sizeof(control_t));
  if (!control) AllocationError("newController");
  control->bchOnly = false;
  control->leftOnly = false;
  control->q = -1;
  return control;
}

/******************************************************************************/
void freeController(control_t *control)
{
  free(control);
  return;
}

/******************************************************************************/
void InterpretCommandLine(int argc, char *argv[], control_t *control)
{
  char invalid[MAXLINE];
  char *this;
  initargs(argc,argv,&pinfo);
  sprintf(invalid,
    "Invalid command line. Issue \"%s -help\" for more details", pinfo.name);
  while (zgetopt("blq:") != OPT_END)
  {
    switch(opt_char)
    {
    case 'b':
      control->bchOnly = true;
      break;
    case 'l':
      control->leftOnly = true;
      break;
    case 'q':
      control->q = atoi(opt_text);
    default:
      break;
    }
  }
  if (opt_ind != argc - 1) OtherError(invalid);
  this = argv[opt_ind++];
  strcpy(control->stem, this);
  return;
}

/******************************************************************************
// apparently not used -- S. King
static void printSupport(PTR vec)
{
  long i;
  FEL f;
  printf("support:");
  for(i=0; i < znoc; i++)
  {
    f = zextract(vec,i+1);
    if (f != F_ZERO) printf(" %ld",i);
  }
  printf("\n");
  return;
}

******************************************************************************/
boolean leftActionMatricesRequired(control_t *control)
{
  if (control->leftOnly) return true;
  return (control->bchOnly) ? false : true;
}

/******************************************************************************/
boolean rightActionMatricesRequired(control_t *control)
{
  if (control->bchOnly) return false;
  return (control->leftOnly) ? false : true;
}

/******************************************************************************/
boolean rightActionMatricesNotYetKnown(control_t *control)
{
  if (control->bchOnly) return true;
  return (control->leftOnly) ? false : true;
}

/******************************************************************************/
boolean basisChangeMatricesNotYetKnown(control_t *control)
{
  if (control->bchOnly) return true;
  return (control->leftOnly) ? false : true;
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  group_t *group;
  control_t *control;
  mtxinit();
  control = newController();
  InterpretCommandLine(argc, argv, control);
  group = namedGroupRecord(control->stem);
  loadNonTips(group);
  if (control->q != -1)
  {
    zsetfield(control->q);
    if (zchar != group->p)
      OtherError("makeActionMatrices: invalid ground field");
  }
  buildPathTree(group);
  if (rightActionMatricesNotYetKnown(control))
    loadRegularActionMatrices(group);
  else
    loadActionMatrices(group);
  if (basisChangeMatricesNotYetKnown(control))
  {
    makeBasisChangeMatrices(group);
    saveBasisChangeMatrices(group);
  }
  else
    loadBasisChangeMatrices(group);
  if (rightActionMatricesRequired(control))
  {
    changeActionMatricesReg2Nontips(group);
    saveActionMatrices(group);
  }
  if (leftActionMatricesRequired(control))
  {
    makeLeftActionMatrices(group);
    saveLeftActionMatrices(group);
  }
  freeGroupRecord(group);
  exit(0);
}

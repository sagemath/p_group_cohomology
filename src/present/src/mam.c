/* ========================== Present =============================
   mam.c : Make Action Matrices

   (C) Copyright 1999-2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"
MTX_DEFINE_FILE_INFO

static char *helptext[] = {
"SYNTAX",
"   makeActionMatrices [-q <q>] [-b] [-l] <stem>",
"",
"   Reads <stem>.nontips, <stem>.reg",
"   Writes <stem>.gens, <stem>.lgens, <stem>.bch",
"   With option -b, only writes <stem>.bch",
"   With option -l, only writes <stem>.lgens",
"   (-b -l writes .bch and .lgens)",
"   Option -q: Work over F_q rather than over F_p",
"",
"DESCRIPTION",
"   Make matrices for actions of generators.",
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
  if (!control)
  { MTX_ERROR1("%E", MTX_ERR_NOMEM);
    return NULL;
  }
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
int InterpretCommandLine(int argc, char *argv[], control_t *control)
{
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
  if (opt_ind != argc - 1)
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
  this = argv[opt_ind++];
  strcpy(control->stem, this);
  return 0;
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
  MtxInitLibrary();
  control = newController();
  if (InterpretCommandLine(argc, argv, control)) exit(1);
  group = namedGroupRecord(control->stem);
  if (!group) exit(1);
  if (loadNonTips(group)) exit(1);
  if (control->q != -1)
  {
    FfSetField(control->q);
    if (FfChar != group->p)
      { MTX_ERROR("invalid ground field");
        exit(1);
      }
  }
  if (buildPathTree(group)) exit(1);
  if (rightActionMatricesNotYetKnown(control))
    if (loadRegularActionMatrices(group)) exit(1);
  else
    if (loadActionMatrices(group)) exit(1);
  if (basisChangeMatricesNotYetKnown(control))
  {
    if (makeBasisChangeMatrices(group)) exit(1);
    if (saveBasisChangeMatrices(group)) exit(1);
  }
  else
    if (loadBasisChangeMatrices(group)) exit(1);
  if (rightActionMatricesRequired(control))
  {
    if (changeActionMatricesReg2Nontips(group)) exit(1);
    if (saveActionMatrices(group)) exit(1);
  }
  if (leftActionMatricesRequired(control))
  {
    if (makeLeftActionMatrices(group)) exit(1);
    if (saveLeftActionMatrices(group)) exit(1);
  }
  freeGroupRecord(group);
  exit(0);
}

/* ================================================================
   mam.c : Make Action Matrices

   (C) Copyright 1999-2000 David J. Green <green@math.uni-wuppertal.de>
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
    "makeActionMatrices",

    "Make matrices for actions of generators",

    "Reads <stem>.nontips, <stem>.reg\n"
    "Writes <stem>.gens, <stem>.lgens, <stem>.bch\n"
    "\n"
    "SYNTAX\n"
    "    makeActionMatrices [-q <q>] [-b] [-l] <stem>\n"
    "\n"
    "ARGUMENTS\n"
    "    <stem> ................. label of a prime power group\n"
    "\n"
    "OPTIONS\n"
    MTX_COMMON_OPTIONS_DESCRIPTION
    "\n"
    "    -b ..................... only write <stem>.bch\n"
    "    -l ..................... only write <stem>.lgens\n"
    "    -b -l .................. write both .bch and .lgens\n"
    "    -q <q>: Work over GF(q) rather than over GF(p)\n"
    };

static MtxApplication_t *App = NULL;


/******************************************************************************
 * control variables
 ********************/

static char *stem = NULL;
static group_t *group = NULL;
static int bchOnly = 0;
static int leftOnly = 0;
static int Field = -1;


/******************************************************************************/
static int Init(int argc, const char *argv[])
{
  App = AppAlloc(&AppInfo,argc,argv);
  if (App == NULL)
    return 1;
  /*makeActionMatrices [-q <q>] [-b] [-l] <stem> */

  /* What field? */
  Field = AppGetIntOption(App, "-a", -1, -1, 255);
  bchOnly = AppGetOption(App, "-b");
  leftOnly = AppGetOption(App, "-l");
  if (AppGetArguments(App, 1, 1) < 0)
    return 1;

  stem = mtx_strdup(App->ArgV[0]);
  group = namedGroupRecord(stem);
  if (!group)
  { printf("Cannot create a group described by %s\n", stem);
    return 1;
  }
  if (loadNonTips(group))
  {
    printf("Cannot determine nontips for %s\n", stem);
    return 1;
  }
  if (Field != -1)
  {
    FfSetField(Field);
    if (FfChar != group->p)
      { printf("Expected a field of characteristic %d\n", FfChar);
        return 1;
      }
  }
  return 0;
}

static void Cleanup()
{
    if (App != NULL)
        AppFree(App);
    freeGroupRecord(group);
}

/******************************************************************************/
boolean leftActionMatricesRequired()
{
  if (leftOnly) return true;
  return (bchOnly) ? false : true;
}

/******************************************************************************/
boolean rightActionMatricesRequired()
{
  if (bchOnly) return false;
  return (leftOnly) ? false : true;
}

/******************************************************************************/
boolean rightActionMatricesNotYetKnown()
{
  if (bchOnly) return true;
  return (leftOnly) ? false : true;
}

/******************************************************************************/
boolean basisChangeMatricesNotYetKnown()
{
  if (bchOnly) return true;
  return (leftOnly) ? false : true;
}

/******************************************************************************/
int main(int argc, const char *argv[])
{
  if (Init(argc, argv))
  { MTX_ERROR("Error parsing command line. Try --help");
    exit(1);
  }

  if (buildPathTree(group))
  {
       printf("Error building path tree\n");
       exit(1);
  }

  if (rightActionMatricesNotYetKnown())
  {
    if (loadRegularActionMatrices(group))
      {
           printf("Error loading regular action matrices\n");
           exit(1);
      }
  }
  else
  {
    if (loadActionMatrices(group))
      {
           printf("Error loading action matrices\n");
           exit(1);
      }
  }

  if (basisChangeMatricesNotYetKnown())
  {
    if (makeBasisChangeMatrices(group))
      {
           printf("Error determining base change matrices\n");
           exit(1);
      }
    if (saveBasisChangeMatrices(group))
      {
           printf("Error saving base change matrices\n");
           exit(1);
      }
  }
  else
  {
    if (loadBasisChangeMatrices(group))
      {
           printf("Error loading base change matrices\n");
           exit(1);
      }
  }

  if (rightActionMatricesRequired())
  {
    if (changeActionMatricesReg2Nontips(group))
      {
           printf("Error changing action from regular basis to preferred basis\n");
           exit(1);
      }
    if (saveActionMatrices(group))
      {
           printf("Error saving action matrices\n");
           exit(1);
      }
  }

  if (leftActionMatricesRequired())
  {
    if (makeLeftActionMatrices(group))
      {
           printf("Error determining left action matrices\n");
           exit(1);
      }
    if (saveLeftActionMatrices(group))
      {
           printf("Error saving left action matrices\n");
           exit(1);
      }
  }
  Cleanup();
  exit(0);
}

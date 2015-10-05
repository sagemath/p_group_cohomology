/* ========================== Present =============================
   perm2Gap.c : Convert MeatAxe permutations to Gap code

   (C) Copyright 2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   Copyright (C) 2015 Simon A. King <simon.king@uni-koeln.de>
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"
#include "pmatrix_decls.h"
MTX_DEFINE_FILE_INFO

static MtxApplicationInfo_t AppInfo = {
    "perm2Gap",
    "Convert MeatAxe permutations to Gap code",

    "SYNTAX\n"
    "    perm2Gap <infile> <outfile>\n"
    "\n"
    "ARGUMENTS\n"
    "    <infile> ..... file to be read, containing a list of permutations\n"
    "                   in MeatAxe format\n"
    "    <outfile> .... file to be written, providing the permutations in Gap code\n"
    "\n"
    "OPTIONS\n"
    MTX_COMMON_OPTIONS_DESCRIPTION
    "\n"
};

static MtxApplication_t *App = NULL;

/******************************************************************************
 * Control variables
 ******************************************************************************/

const char *infile = NULL;
const char *outfile = NULL;

/******************************************************************************/
int Init(int argc, const char *argv[])
{
  App = AppAlloc(&AppInfo,argc,argv);
  if (App == NULL)
    return 1;
  if (AppGetArguments(App, 2, 2) < 0)
    return 1;
  infile = App->ArgV[0];
  outfile = App->ArgV[1];
  return 0;
}

/******************************************************************************/
int main(int argc, char const*argv[])
{

  if (Init(argc, argv))
  { MTX_ERROR("Error parsing command line. Try --help");
    exit(1);
  }
  if (convertPermutationsToAsci(infile, outfile)) exit(1);
  if (App != NULL)
      AppFree(App);
  exit(0);
}

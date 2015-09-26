/* ========================== Present =============================
   perm2Gap.c : Convert MeatAxe permutations to Gap code

   (C) Copyright 2000 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"
#include "pmatrix_decls.h"
MTX_DEFINE_FILE_INFO

static char *helptext[] = {
"SYNTAX",
"   perm2Gap <infile> <outfile>",
"",
"   Reads <infile>: list of permutations in MeatAxe format",
"   Translates to Gap code <outfile>",
"",
"DESCRIPTION",
"   Convert MeatAxe permutations to Gap code.",
NULL};

static proginfo_t pinfo =
  { "perm2Gap", "Convert MeatAxe permutations to Gap code",
    "$Revision: 01_June_2000", helptext };

/******************************************************************************/
int InterpretCommandLine(int argc, char *argv[], char *infile, char*outfile)
{
  //register int i;
  char *this;
  initargs(argc,argv,&pinfo);
  sprintf(invalid,
    "Invalid command line. Issue \"%s -help\" for more details", pinfo.name);
  while (zgetopt("") != OPT_END);
  if (opt_ind != argc - 2)
  { MTX_ERROR1("%E", MTX_ERR_BADARG);
    return 1;
  }
  this = argv[opt_ind++];
  strcpy(infile, this);
  this = argv[opt_ind++];
  strcpy(outfile, this);
  return 0;
}

/******************************************************************************/
int main(int argc, char *argv[])
{
  char infile[MAXLINE], outfile[MAXLINE];
  MtxInitLibrary();
  if (InterpretCommandLine(argc, argv, infile, outfile)) exit(1);
  if (convertPermutationsToAsci(infile, outfile)) exit(1);
  exit(0);
}

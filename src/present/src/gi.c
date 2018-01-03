/* ===============================================================
   gi.c : Print Group Information

   Copyright 1999 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   Copyright 2015 Simon A. King <simon.king@uni-jena.de>

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
    "groupInfo",

    "Print group statistics",

    "    Deciphers .nontips file header and prints group statistics.\n"
    "\n"
    "    Reads <stem>.nontips (<stem>.dims too if Jennings ordering used)\n"
    "\n"
    "SYNTAX\n"
    "    groupInfo <stem>\n"
    "\n"
    "ARGUMENTS\n"
    "    <stem> ................. label of a prime power group\n"
    "\n"
    "OPTIONS\n"
    MTX_COMMON_OPTIONS_DESCRIPTION
    "\n"
    };

static MtxApplication_t *App = NULL;

/**
 * Control variables
 **/

 group_t *group = NULL;


/*****
 * 1 on error
 **************************************************************************/
static int Init(int argc, const char *argv[])
{
  App = AppAlloc(&AppInfo,argc,argv);
  if (App == NULL)
    return 1;

  group = newGroupRecord();
  if (!group)
  {
      return 1;
  }

  if (AppGetArguments(App, 1, 1) < 0)
    return 1;

  if ((group->stem = mtx_strdup(App->ArgV[0])) == NULL) return 1;
  return 0;
}

static void Cleanup()
{
    if (App != NULL)
        AppFree(App);
    freeGroupRecord(group);
}

/******************************************************************************/
static long valuation(long p, long n)
{
  long nu = 0;
  long m = n;
  while (m % p == 0) { m = m/p;  nu++; }
  return nu;
}

/******************************************************************************/
int main(int argc, const char *argv[])
{
  int n;
  if (Init(argc, argv))
  { MTX_ERROR("Error parsing command line. Try --help");
    exit(1);
  }
  if (readHeader(group)) exit(1);
  if (group->ordering == 'J')
  {
      if (loadDimensions(group)) exit(1);
  }
  printf("Group name : %s\n", group->stem);
  printf("Group order: %ld^%ld\n", group->p, valuation(group->p, group->nontips));
  printf("Chosen ordering: %s\n", (group->ordering == 'R') ?
    "Reverse length lexicographical" : ((group->ordering == 'L') ?
    "Length lexicographical" : "Jennings"));
  printf("Number of generators  : %ld\n", group->arrows);
  printf("Size of Groebner basis: %ld\n",
    group->mintips);
  printf("Maximal nontip length : %ld\n", group->maxlength);
  if (group->ordering == 'J')
  {
    printf("Dimensions of Jennings generators: ");
    for (n = 1; n <= group->arrows; n++)
      printf((n < group->arrows) ? "%ld, " : "%ld\n", group->dim[n]);
  }

  Cleanup();
  exit(0);
}

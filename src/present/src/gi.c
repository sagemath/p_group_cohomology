/* ========================== Present =============================
   gi.c : Print Group Information

   (C) Copyright 1999 David J. Green <green@math.uni-wuppertal.de>
   Department of Mathematics, University of Wuppertal,
   D-42097 Wuppertal, Germany
   This program is free software; see the file COPYING for details.
   ================================================================ */

#include "pgroup.h"
#include "pgroup_decls.h"

static char *helptext[] = {
"SYNTAX",
"	groupInfo <Stem>",
"",
"	Reads <Stem>.nontips (<Stem>.dims too if Jennings ordering used)",
"",
"DESCRIPTION",
"	Deciphers .nontips file header and prints group statistics.",
NULL};

static proginfo_t pinfo =
  { "groupInfo", "Print group statistics",
    "$Revision: 19_April_1999", helptext };

/******************************************************************************/
void InterpretCommandLine(int argc, char *argv[], group_t *group)
{
  //register int i;
  char invalid[MAXLINE];
  char *this;
  initargs(argc,argv,&pinfo);
  sprintf(invalid,
    "Invalid command line. Issue \"%s -help\" for more details", pinfo.name);
  while(zgetopt("") != OPT_END);
  if (opt_ind != argc - 1) OtherError(invalid);
  this = argv[opt_ind++];
  group->stem = djg_strdup(this);
  return;
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
int main(int argc, char *argv[])
{
  int n;
  group_t *group;
  mtxinit();
  group = newGroupRecord();
  InterpretCommandLine(argc, argv, group);
  readHeader(group);
  if (group->ordering == 'J') loadDimensions(group);
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
  freeGroupRecord(group);
  exit(0);
}

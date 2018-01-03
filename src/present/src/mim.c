/* ========================== Present =============================
   mim.c : Make Inclusion Matrix

   (C) Copyright 2000 David J. Green <green@math.uni-wuppertal.de>
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

#include "pincl.h"
#include "pincl_decls.h"
MTX_DEFINE_FILE_INFO

static MtxApplicationInfo_t AppInfo = {
    "makeInclusionMatrix",
    "Make matrix for inclusion of subgroup",

    "Reads <Gstem>.nontips, <Gstem>.gens, <Gstem>.bch,\n"
    "      <Hstem>.nontips, <incStem>.irg\n"
    "Writes <incStem>.ima\n"
    "\n"
    "SYNTAX\n"
    "    makeInclusionMatrix <Gstem> <Hstem> <incStem>\n"
    "\n"
    "ARGUMENTS\n"
    "    <Gstem> ....... label of the ambient group\n"
    "    <Hstem> ....... label of the isomorphism type of the subgroup\n"
    "    <incStem> ..... label of the subgroup embedding\n"
    "\n"
    "OPTIONS\n"
    MTX_COMMON_OPTIONS_DESCRIPTION
    "\n",
};

static MtxApplication_t *App = NULL;

/******************************************************************************
 * control variables
 ******************************************************************************/

const char *Gstem=NULL;
const char *Hstem=NULL;
const char *incStem=NULL;
group_t *G;
group_t *H;
inclus_t *inclus;

/******************************************************************************/
int Init(int argc, const char *argv[])
{
    App = AppAlloc(&AppInfo,argc,argv);
    if (App == NULL)
        return 1;

    if (AppGetArguments(App, 3, 3) < 0)
        return 1;
    Gstem = App->ArgV[0];
    Hstem = App->ArgV[1];
    incStem = App->ArgV[2];

    G = namedGroupRecord(Gstem);
    if (!G) return 1;
    H = namedGroupRecord(Hstem);
    if (!H) return 1;
    inclus = newInclusionRecord(G, H, incStem);
    if (!inclus) return 1;
    return 0;
}

void Cleanup()
{
    if (App != NULL)
        AppFree(App);
    freeInclusionRecord(inclus);
    freeGroupRecord(G);
    freeGroupRecord(H);
}

/******************************************************************************/
int main(int argc, const char *argv[])
{
  if (Init(argc, argv))
  { MTX_ERROR("Error parsing command line. Try --help"); exit(1); }
  if (loadNonTips(G)) exit(1);
  if (buildPathTree(G)) exit(1);
  if (loadActionMatrices(G)) exit(1);
  if (loadBasisChangeMatrices(G)) exit(1);
  if (loadNonTips(H)) exit(1);
  if (buildPathTree(H)) exit(1);
  if (makeInclusionMatrix(inclus)) exit(1);
  if (saveInclusionMatrix(inclus)) exit(1);
  Cleanup();
  exit(0);
}

#*****************************************************************************
#  GAP subgroup structure routines
#
#       Copyright (C) 2009 David J. Green <david.green@uni-jena.de>
#       Copyright (C) 2020 Simon A. King  <simon.king@uni-jena.de>
#
#    This file is part of p_group_cohomology.
#
#    p_group_cohomoloy is free software: you can redistribute it and/or modify
#    it under the terms of the GNU General Public License as published by
#    the Free Software Foundation, either version 2 of the License, or
#    (at your option) any later version.
#
#    p_group_cohomoloy is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#    GNU General Public License for more details.
#
#    You should have received a copy of the GNU General Public License
#    along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.
#*****************************************************************************

# Original version was created 01 September 2000

# Modifications by Simon King:
# New folder structure 2008-05
# - Each group has its own folder (e.g., 128gp836/)
#   It contains the basic data and eventually the cohomology ring
# - In this folder are subfolders:
#   * sgp/ for all data concerning subgroups
#   * dat/ for the resolution and other relevant data
####################################################
# Further changes in the folder structure (2008-10)
# - The folder tree of a groop is rooted in a folder
#   whose name can be chosen by the user.
#   This is done by a parameter "fldr" that gives the
#   name of the root (NOT ending with "/"!).

# Simon King: Removing some unused functions (2008-12)
# Simon King: Adding makeInducedHomomorphismData (2009-05), canonicalIsomorphism, admissibleGroup (2009-06)
# Simon King: Adding conjugateIntoSylow (2009-12)
# Simon King: Adding OneIsomorphicSubgroup (2018-10)

###################
## Conventions:
# Gid:  id of a small group as returned by IdGroup
#   so: Gid = [N, n], N = |G|, G is <n>th small group of this size
# # Glabel = [Gsize, Gname]; Gsize = N = |G|, Gname = string used as name of G
# Changed by Simon King (2008-11):
# Glabel = [Gsize, Gname, folder]; Gsize = N = |G|, Gname = string used as name of G,
#                                  folder = the root of the folder tree for G

####################################################

maximalElabSubgroupTiers := function(G)
  local xxx, maxelTiers;
  xxx := elabClasses(G);
  maxelTiers := xxx[2];
  return maxelTiers;
end;

maximalElabSubgroups := function(G)
  local maxelTiers, maxels;
  maxelTiers := maximalElabSubgroupTiers(G);
  maxels := Flat(List(maxelTiers, xxx -> xxx[1]));
  return maxels;
end;

ensureDirectoryExists := function(dir);
  Exec(Concatenation("mkdir -p ", dir));
  return;
end;

GroupStem := function(Glabel)
  # All files referring to that group start with GroupStem,
  # which also includes the folder in which these files reside
  if Size(Glabel[3])>0 then
    return Concatenation(Glabel[3], "/", Glabel[2], "/", Glabel[2]);
  else
    return Concatenation(Glabel[2], "/", Glabel[2]);
  fi;
end;

ResolStem := function(Glabel)
  if Size(Glabel[3])>0 then
    return Concatenation(Glabel[3], "/", Glabel[2], "/res/Res", Glabel[2]);
  else
    return Concatenation(Glabel[2], "/res/Res", Glabel[2]);
  fi;
end;

grpDir := function(q,i)
  return Concatenation(String(q),"gp",String(i),"/");
end;

datDir := function(q,i)
  return Concatenation(grpDir(q,i),"dat/");
end;

datDirByName := function(Gname)
  return Concatenation(Gname,"/dat/");
end;

sgpDir := function(q,i)
  return Concatenation(grpDir(q,i),"sgp/");
end;


###########################################

sgsFile := function(Glabel)
  local Gsize, Gname;
  Gsize := String(Glabel[1]);
  Gname := Glabel[2];
  if Size(Glabel[3])>0 then
    return Concatenation(Glabel[3],"/",Gname, "/sgp/", Gname, ".sgs");
  else
    return Concatenation(Gname, "/sgp/", Gname, ".sgs");
  fi;
end;

descFile := function(Glabel)
  local Gsize, Gname;
  Gsize := String(Glabel[1]);
  Gname := Glabel[2];
  if Size(Glabel[3])>0 then
    return Concatenation(Glabel[3],"/",Gname, "/", Gname, ".desc");
  else
    return Concatenation(Gname, "/", Gname, ".desc");
  fi;
end;

loadGroup := function(Glabel)
  local Gstem, regfile, tmpfile, pl, G;
  Gstem := GroupStem(Glabel);
  # Print(Gstem);
  # Print("\nTrying\n");
  regfile := Concatenation(Gstem, ".reg");
  tmpfile := Concatenation(Gstem, ".trg");
  pl := mtxPermList(regfile, tmpfile);
  G := Group(pl);
  return G;
end;

Gid2GStem := function(Gid)
  local Gname, Gsize;
  Gsize := Gid[1];
  Gname := Concatenation(String(Gsize), "gp", String(Gid[2]));
  return Gname;
end;

Gid2Glabel := function(Gid,fldr)
  local Gsize, Gname;
  Gsize := Gid[1];
  Gname := Gid2GStem(Gid);
  return [Gsize, Gname, fldr];
end;

################################################################################
# Test whether the first generators of the input G form a minimal generating set,
# and return an isomorphism from G to a permutation group whose generators
# correspond to that minimal generating set.
admissibleGroup := function(G)
  local s, gens, H, phi, psi, HPerm;
  s := RankPGroup(G);
  gens := List([1..s], x -> GeneratorsOfGroup(G)[x]);
  H := Subgroup(G, gens);
  if Size(H) <> Size(G) then
    return fail;
  fi;
  psi := GroupHomomorphismByImages(G, H, gens, gens);
  if psi = fail then
    return fail;
  fi;
  phi := IsomorphismPermGroup(H);
  if phi = fail then
    return fail;
  fi;
  return GroupHomomorphismByImages(G, Range(phi), gens, List([1..s], x -> Image(phi, Image(psi,gens[x]))));
end;

################################################################################
# Return an isomorphism that maps the generators of H to the generators of H,
# or fail if this is no isomorphism.
InstallGlobalFunction( canonicalIsomorphism,
function(G,H)
  local phi,phi0;
  if Length(GeneratorsOfGroup(G))>Length(GeneratorsOfGroup(H)) then
    phi0 := canonicalIsomorphism(H,G);
    if phi0 = fail then return fail; fi;
    phi := GroupHomomorphismByImages(G, H, GeneratorsOfGroup(G), List([1..Length(GeneratorsOfGroup(G))], x -> PreImagesRepresentative(phi0,GeneratorsOfGroup(G)[x])));
    return phi;
  else
    phi := GroupHomomorphismByImages(G, H, GeneratorsOfGroup(G), List([1..Length(GeneratorsOfGroup(G))], x -> GeneratorsOfGroup(H)[x]));
  fi;
  if phi = fail then
    return fail;
  fi;
  if IsInjective(phi) and IsSurjective(phi) then
    return phi;
  fi;
  return fail;
end
);

################################################################################
# Return one isomorphism of U to a subgroup of G

OneIsomorphicSubgroup := function(G, U)
  return IsomorphicSubgroups(G, U: findall:=false)[1];
end;

################################################################################
# Return a conjugacy map that moves a Sylow p-subgroup of a given subgroup of G
# into a given Sylow p-subgroup of G
# Simon King, following suggestions of Alexander Hulpke and Laurent Bartholdi

conjugateIntoSylow := function(G, U, S)
  local p,phi;
  p := PrimePGroup(S);
  if PrimePGroup(U)<>p then return fail; fi;
  while Index(G,U) mod p = 0 do
     U := SylowSubgroup(Normalizer(G,U),p);
  od;
  return ConjugatorAutomorphism(G,RepresentativeAction(G,U,S));
end;


################################################################################
InstallGlobalFunction( verifiedMinGens,
function(G)
  local s, gens, H;
  s := RankPGroup(G);
  gens := List([1..s], x -> GeneratorsOfGroup(G)[x]);
  H := Subgroup(G, gens);
  if Size(H) <> Size(G) then
    Error("verifiedMinGens: Please explicitly provide minimal generators for the group ", G);
  fi;
  return gens;
end
);

################################################################################
easyMakeBasis := function(G, Gname,fldr)
  local Gdir, Gstem, H;
  #H := Group(verifiedMinGens(G));
  #hh := regularPermutationAction(H: forceDefiningGenerators);
  H := asPermgroup(G);
  if Size(fldr)>0 then
     Gdir := Concatenation(fldr,"/",Gname, "/");
  else
     Gdir := Concatenation(Gname, "/");
  fi;
  ensureDirectoryExists(Gdir);
  Gstem := Concatenation(Gdir, Gname);
  makeBasis(H, Gstem, true: TG);
  return;
end;

################################################################################
verifiedMinGensOfSmallGroup := function(G)
  local s, gens, H;
  s := RankPGroup(G);
  gens := List([1..s], x -> GeneratorsOfGroup(G)[x]);
  H := Subgroup(G, gens);
  if Size(H) <> Size(G) then
    Error("verifiedMinGensOfSmallGroup: problems with Small Group ",
      IdGroup(G));
  fi;
  return gens;
end;

################################################################################
smallGroupMinGens := function(G)
  local Gid, smG, mingens, phi;
  Gid := IdGroup(G);
  smG := SmallGroup(Gid);
  mingens := verifiedMinGensOfSmallGroup(smG);
  phi := IsomorphismGroups(smG, G);
  return [Gid, List(mingens, g -> Image(phi, g))];
end;

################################################################################
identifyMaximalSubgroups := function(G)
  local msl, permsl;
  msl := MaximalSubgroups(G);
  permsl := List(msl, H -> smallGroupMinGens(H));
  return permsl;
end;

################################################################################
maxSubgroupNames := function(permsl)
  return List(permsl, xx -> Gid2Glabel(xx[1])[2]);
end;

################################################################################
identifyMaximalElementaryAbelians := function(G)
  local meacl, meal, permsl;
  #meal := maximalElabSubgroups(G);
  meal := newMaxels(G); # using a new function written by David Green (2010)
  permsl := List(meal, H -> smallGroupMinGens(H));
  return permsl;
end;

################################################################################
maxElementaryAbelianRanks := function(permsl)
  return List(permsl, xx -> Length(xx[2]));
end;

################################################################################
identifyZdash := function(G)
  # Zdash is the greatest central elab. Nowadays I often call it C.
  local H, perms;
  H := greatestCentralElab(G);
  perms := smallGroupMinGens(H);
  return perms;
end;

################################################################################
writeOutSgsFile := function(Istump, Glabel, specialSubgpId, CrankPos,
  maxelRankPos)
  local fp, buffer;
  fp := OutputTextFile(sgsFile(Glabel), false);
  buffer := Concatenation("# Subgroup information for ", Glabel[2]);
  WriteLine(fp, buffer);
  buffer := "local numSpecialSubgps, specialSubgpId, CrankPos, numMaxels,";
  WriteLine(fp, buffer);
  buffer := "  maxelRankPos, numBoltons, Bolton;";
  WriteLine(fp, buffer);
  buffer := Concatenation("numSpecialSubgps := ",
    String(Length(specialSubgpId)), ";");
  WriteLine(fp, buffer);
  # subgpNames := List(specialSubgpId, Hid -> Gid2GStem(Hid));
  buffer := Concatenation("specialSubgpId := ", String(specialSubgpId), ";");
  WriteLine(fp, buffer);
  buffer := Concatenation("CrankPos := ", String(CrankPos), ";");
  WriteLine(fp, buffer);
  buffer := Concatenation("numMaxels := ", String(Length(maxelRankPos)), ";");
  WriteLine(fp, buffer);
  buffer := Concatenation("maxelRankPos := ", String(maxelRankPos), ";");
  WriteLine(fp, buffer);
  buffer := "numBoltons := 0;";
  WriteLine(fp, buffer);
  buffer := "Bolton := [];";
  WriteLine(fp, buffer);
  buffer := "return [numSpecialSubgps, specialSubgpId, CrankPos,";
  WriteLine(fp, buffer);
  buffer := "  numMaxels, maxelRankPos, numBoltons, Bolton];";
  WriteLine(fp, buffer);
  CloseStream(fp);
  return;
end;

################################################################################
makeInducedHomomorphismData := function(Gstem, Hstem, Istem, phi, Gsize)
  # Gstem, Hstem: Group stem names *including* path.
  # The nontips files for H and G are Hstem.nontips, Gstem.nontips
  # Istem: All data file names related with the homomorphism H->G start with Istem
  # phi: H->G homomorphism
  # Author: Simon King (05/2009)
  # Idea:
  # - G shall eventually be a permutation group, namely in the same
  #   form as used in the cohomology computation. This is done by
  #   using regularPermutationAction.
  # - H must have minimal generators, which are the same as those used
  #   in the cohomology computation. This is either ensured by the user,
  #   or is achieved by verifiedMinGens. Hence, the first generators
  #   must provide a minimal generating set.
  ## also writes .irg file
  local tmpfile, irgfile, buffer, pl, H, G0, psi, G, psi_G0_G;
  # get the source right
  H := Group(verifiedMinGens(Source(phi)));
  # get the image right
  G0 := Range(phi);
  # Strange: Even if G0 is permutation group, we need to switch to the regular Permutation representation.
  # Otherwise, desasters occur.
  G := asPermgroup(G0); #regularPermutationAction(G0: forceDefiningGenerators);
  psi_G0_G := GroupHomomorphismByImages(G0,G, GeneratorsOfGroup(G0), GeneratorsOfGroup(G));
  psi := GroupHomomorphismByImages(H, G, GeneratorsOfGroup(H), List([1..Length(GeneratorsOfGroup(H))], x->Image(psi_G0_G, Image(phi, GeneratorsOfGroup(H)[x]))));
  pl := List([1..Length(GeneratorsOfGroup(H))], x->Image(psi, GeneratorsOfGroup(H)[x]));
  tmpfile := Concatenation(Istem, ".tmp");
  irgfile := Concatenation(Istem, ".irg");
  writeOutMtxPerms(pl, irgfile, tmpfile, Gsize);
  buffer := Concatenation(exportMTXLIB, "makeInclusionMatrix ", Gstem, " ", Hstem,
    " ", Istem);
  Exec(buffer);
  return;
end;

################################################################################
makeIma := function(Gstem, Hlabel, Istem, pl, Gsize)
  # also writes .irg file
  local tmpfile, irgfile, buffer, Hstem;
  Hstem := GroupStem(Hlabel);
  tmpfile := Concatenation(Istem, ".tmp");
  irgfile := Concatenation(Istem, ".irg");
  writeOutMtxPerms(pl, irgfile, tmpfile, Gsize);
  buffer := Concatenation(exportMTXLIB, "makeInclusionMatrix ", Gstem, " ", Hstem,
    " ", Istem);
  Exec(buffer);
  return;
end;

################################################################################
makeSpecialSubgpIma := function(GIdata, Hdata, i, fldr)
  # Hdata = [Hid, pl]
  # Hid: Gid of H, pl list of min gens as permutations
  local Istem, Hid, Hlabel;
  Istem := Concatenation(GIdata[2], "sg", String(i));
  Hid := Hdata[1];
  Hlabel := Gid2Glabel(Hid,fldr);
  makeIma(GIdata[1], Hlabel, Istem, Hdata[2], GIdata[3]);
  return;
end;

################################################################################
inclusionStump := function(Glabel)
  local Istump, Idir;
  if Size(Glabel[3])>0 then
    Idir := Concatenation(Glabel[3],"/",Glabel[2], "/sgp/");
  else
    Idir := Concatenation(Glabel[2], "/sgp/");
  fi;
  ensureDirectoryExists(Idir);
  Istump := Concatenation(Idir, Glabel[2]);
  return Istump;
end;

################################################################################
VrankPos := function(Hdata, i)
  # Hdata must refer to an elem ab subgroup
  return [Size(Hdata[2]), i];
end;

################################################################################
registrationOfSpecialSubgroup := function(GIdata, specialSubgp,
  specialSubgpId, Hdata,fldr)
  local n, Hid, i, j, H;
  Hid := Hdata[1];
  H := Group(Hdata[2]);
  n := Length(specialSubgp);
  for i in [1..n] do
    if Hid <> specialSubgpId[i] then continue; fi;
    if H = specialSubgp[i] then
      j := i;
      break;
    fi;
  od;
  if not IsBound(j) then
    # We've not seen this group before
    j := n+1;
    makeSpecialSubgpIma(GIdata, Hdata, j,fldr);
    specialSubgp[j] := H;
    specialSubgpId[j] := Hid;
  fi;
  return j;
end;

################################################################################
makeInclusionInfo := function(Gsize, Gname, fldr)
  local permsl, G, Istump, Glabel, GIdata, specialSubgp, specialSubgpId,
    CrankPos, Hdata, numMaxels, maxelRankPos, Hpos, i;
  # noms, msNames,
  Glabel := [Gsize, Gname, fldr];
  G := loadGroup(Glabel);
  Istump := inclusionStump(Glabel);
  # Print("Istump=", Istump, "\n");
  GIdata := [GroupStem(Glabel), Istump, Gsize];
  specialSubgp := [];
  specialSubgpId := [];
  # Process the greatest central elab
  Hdata := identifyZdash(G);
  i := registrationOfSpecialSubgroup(GIdata, specialSubgp, specialSubgpId,
    Hdata,fldr);
  CrankPos := VrankPos(Hdata, i);
  # Process the maxels
  permsl := identifyMaximalElementaryAbelians(G);
  numMaxels := Length(permsl);
  Hpos := [];
  for i in [1..numMaxels] do
    Hpos[i] := registrationOfSpecialSubgroup(GIdata, specialSubgp,
      specialSubgpId, permsl[i],fldr);
  od;
  maxelRankPos := List([1..numMaxels], j -> VrankPos(permsl[j], Hpos[j]));
  # # Currently obsolete processing of maximal subgroups
  # permsl := identifyMaximalSubgroups(G);
  # noms := Length(permsl);
  # makeMsIma(Gstem, Istump, permsl, Gsize);
  # msNames := maxSubgroupNames(permsl);
  writeOutSgsFile(Istump, Glabel, specialSubgpId, CrankPos, maxelRankPos);
  return;
end;

################################################################################
lePrimePower := function(a, b)
  local al, bl;
  al := FactorsInt(a);
  bl := FactorsInt(b);
  if al[1] < bl[1] then return true; fi;
  if al[1] > bl[1] then return false; fi;
  return (Length(al) < Length(bl));
end;

################################################################################
groupNamesDatabase := function()
  return ReadAsFunction("../templates/groupNames")();
end;

################################################################################
nameAb := function(invts)
  local num, i, name, fp;
  name := "Ab(";
  num := Length(invts);
  fp := OutputTextString(name, true);
  for i in [1..num] do
    if i > 1 then WriteAll(fp, ","); fi;
    WriteAll(fp, String(invts[i]));
  od;
  WriteAll(fp, ")");
  CloseStream(fp);
  return name;
end;

################################################################################
descAb := function(invts)
  local num, i, name, fp;
  name := "Abelian group ";
  num := Length(invts);
  fp := OutputTextString(name, true);
  for i in [1..num] do
    if i > 1 then WriteAll(fp, " x "); fi;
    AppendTo(fp, "C<sub>", String(invts[i]), "</sub>");
  od;
  CloseStream(fp);
  return name;
end;


################################################################################
checkAbelianInvariants := function(A)
  local ngens, gens, invts, expts;
  ngens := RankPGroup(A);
  gens := GeneratorsOfGroup(A){[1..ngens]};
  # LATER it is verified (in easyMakeBasis), that gens really does generate A
  invts := AbelianInvariants(A);
  expts := List(gens, g -> Order(g));
  if (expts <> Reversed(invts)) then
    Print("Abelian group ", IdGroup(A), ": exponents not as expected\n");
  fi;
  return;
end;

################################################################################
InstallGlobalFunction( makeThisSmallGroup,
function(Gid,fldr)
  local q, i, G, Gname, Exec_command;
  G := SmallGroup(Gid);
  q := Gid[1];
  i := Gid[2];
  Gname := Gid2GStem(Gid);
  if IsAbelian(G) then
    easyMakeBasis(G, Gname, fldr);
    if Size(fldr)>0 then
       ensureDirectoryExists(Concatenation(fldr,"/",datDir(q,i)));
    else
       ensureDirectoryExists(datDir(q,i));
    fi;
  else
    easyMakeBasis(G, Gname, fldr);
    if Size(fldr)>0 then
       ensureDirectoryExists(Concatenation(fldr,"/",datDir(q,i)));
    else
       ensureDirectoryExists(datDir(q,i));
    fi;
    makeInclusionInfo(q, Gname,fldr);
  fi;
  return;
end
);

################################################################################
theUnderlyingPrime := function(q)
  local p, n, l;
  if not IsPosInt(q) then
    Error("theUnderlyingPrime: ",q," not a positive integer\n");
  elif q = 1 then
    Error("theUnderlyingPrime: q=1 not allowed\n");
  fi;
  l := FactorsInt(q);
  p := l[1];
  n := Length(l);
  if q <> p^n then
    Error("theUnderlyingPrime: ",q," not a prime power\n");
  fi;
  return p;
end;

################################################################################
InstallGlobalFunction( isPrimePower,
function(q)
  local p, n, l;
  if q = 1 then return false; fi;
  l := FactorsInt(q);
  p := l[1];
  n := Length(l);
  return (q = p^n);
end
);

################################################################################
makeThisGroup := function(G, Gname,fldr)
  # This is for dealing with groups that are not in the SmallGroups library
  local q, Exec_command;
  q := Size(G);
  if not isPrimePower(q) then
    Error("makeThisGroup: not a (nontrivial) p-group");
  fi;
  if IsAbelian(G) then
    #Error("makeThisGroup: abelian case not implemented");
    easyMakeBasis(G, Gname, fldr);
    if Size(fldr)>0 then
      ensureDirectoryExists(Concatenation(fldr,"/",datDirByName(Gname)));
    else
      ensureDirectoryExists(datDirByName(Gname));
    fi;
  else
    easyMakeBasis(G, Gname, fldr);
    if Size(fldr)>0 then
      ensureDirectoryExists(Concatenation(fldr,"/",datDirByName(Gname)));
    else
      ensureDirectoryExists(datDirByName(Gname));
    fi;
    makeInclusionInfo(q, Gname,fldr);
    #makeDescFile([q, Gname], desc);
  fi;
  return;
end;

################################################################################
makeKey := function(keyList, Gid, Glabel, vulgar)
  local key, latin;
  latin := Glabel[2];
  key := [Gid[2], latin, vulgar];
  keyList[Gid[2]] := key;
  return;
end;

################################################################################
retrieveKeyByLatin := function(keyList, latin)
  local i, num, key;
  num := Length(keyList);
  for i in [1..num] do
    if IsBound(keyList[i]) then
      key := keyList[i];
      if key[2] = latin then return key; fi;
    fi;
  od;
  return fail;
end;

################################################################################
weightsPoly := function(t, Wt)
  local p, n;
  p := 0 * t;
  for n in Wt do
    p := p + t^n;
  od;
  return p;
end;


################################################################################
zRankFromXxx := function(xxx)
  # xxx = output of ReadAsFunction on .sgs file
  return xxx[3][1];
end;

################################################################################
pRankFromXxx := function(xxx)
  # xxx = output of ReadAsFunction on .sgs file
  return Maximum(List(xxx[5], x -> x[1]));
end;


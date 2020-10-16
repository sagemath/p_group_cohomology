#*****************************************************************************
# GapMB : the GAP 4 code version of MakeBasis
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

# *****************************************************************************
# This file implements the following functions:
#
#    makeBasis (G,name,RLL: options): GrpPerm, MonStgElt, BoolElt -> RingIntElt
#
#    makeSmallBasis (G,name,RLL,tries: options):
#      GrpPerm, MonStgElt, BoolElt, RingIntElt -> RingIntElt
#
#    listBasisSizes (G,name,RLL,tries: options):
#      GrpPerm, MonStgElt, BoolElt, RingIntElt -> [RingIntElt]
#
#    makeJenningsBasis (G,name: options): GrpPerm, MonStgElt ->
#
#    asPermgroup(G): GrpPC or GrpPerm -> regular permutation action with verified minimal generators
#    regularPermutationAction(G: options): GrpPC or GrpPerm -> GrpPerm
#    createRegFile(stem, group) ->
#    writeOutMtxPerms(List(Perm), outfile, tmpfile, degree) ->
#
#    printGroebnerBasis (name): MonStgElt ->
#    writeMinimalTips (name): MonStgElt ->
#    printMinimalTips (name): MonStgElt ->
#    printGroupInformation (name): MonStgElt ->
#
#    PermGroupAtlas (name, n): MonStgElt, RingIntElt -> GrpPerm
#    mtxPermList(infile, tmpfile) ->List(Perm)
#
# See the accompanying LaTeX document Present for more information
# *****************************************************************************

# *****************************************************************************
StringToIntegerSequence := function(t)
  local i, j, l, s;
  i := 1;
  l := [];
  while i <= Length(t) do
    j := i;
    while t[j] in "0123456789" do j := j+1; od;
    if j > i then
      Add(l, Int(t{[i..j-1]}));
    fi;
    i := j+1;
  od;
  return l;
end;

# *****************************************************************************

regularPermutationAction := function(G)
# Creates the image of G in S_|G| under the regular permutation action
# Uses defining generators if G in GrpPerm
# Uses PC generators if G in GrpPC, unless option forceDefiningGenerators chosen
  local gens, N, S, L, gg, forceDefiningGenerators;
  forceDefiningGenerators := ValueOption("forceDefiningGenerators");
  if IsPcGroup(G) and not forceDefiningGenerators then
    gens := FamilyPcgs(G);
  else
    gens := GeneratorsOfGroup(G);
  fi;
  N := Size(G);
  S := Elements(G);
  L := List(gens, g->PermList(List([1..N], i->Position(S,S[i]*g))));
  gg := Group(L);
  return gg;
end;

# *****************************************************************************
DeclareProperty("RegularRepresentation",IsPermGroup);

asPermgroup := function(G)
# Creates the isomorphic image of G in some permutation group
# Uses defining generators
  local RegAct;
  if HasRegularRepresentation(G) then return G; fi;
  if isPrimePower(Size(G)) then
     RegAct := Group(verifiedMinGens(regularPermutationAction(G: forceDefiningGenerators)));
  else
     RegAct := regularPermutationAction(G: forceDefiningGenerators);
  fi;
  SetRegularRepresentation(RegAct, true);
  return RegAct;
end;

# *****************************************************************************
printGroupInformation := function(name)
  Exec(Concatenation("groupInfo ", name));
end;

# *****************************************************************************
valueOfIntegerLine := function(s)
  # s is a string representing one integer, terminated by a newline
  # Returns value of integer
  local t;
  t := SplitString(s, '\n');
  return Int(t[1]);
end;

# *****************************************************************************
 mtxPermList := function(infile, tmpfile)
  local pl, fp, xxx, yyy, s, num, nontips;
  Exec("perm2Gap", infile, tmpfile);
  fp := InputTextFile(tmpfile);
  s := ReadLine(fp);
  num := valueOfIntegerLine(s);
  s := ReadLine(fp);
  nontips := valueOfIntegerLine(s);
  xxx := SplitString(ReadAll(fp), '\n');
  CloseStream(fp);
  RemoveFile(tmpfile);
  if Length(xxx) <> num * nontips then
    Print("num=", num, ", nontips=", nontips, "#xxx=", Length(xxx), "\n");
    Error("mtxPermList: xxx length wrong");
  fi;
  yyy := List(xxx, Int);
  xxx := List([0..num-1], n -> yyy{[(1+n*nontips)..((n+1)*nontips)]});
  pl := List(xxx, PermList);
  return pl;
end;

# *****************************************************************************
nontipsStatusLine := function(name)
  local fp, l, t;
  fp := InputTextFile(Concatenation(name,".nontips"));
  l := ReadLine(fp);
  CloseStream(fp);
  t := l{[1..Position(l,'\n')]};
  return StringToIntegerSequence(t);
end;

# *****************************************************************************
ThePrime := function(gg)
  local fac, p;
  fac := FactorsInt(Size(gg));
  if Length(fac) = 0 then
    Error("Group must be finite with infinite cohomological dimension");
  fi;
  p := fac[1];
  if not ForAll(fac, q -> q=p) then Error("Group is not a p-group"); fi;
  return p;
end;

# *****************************************************************************
GetArbGenerators := function(pcg)
  local Phi, mg, n, S, gens, H, j, posl, pos, this_gen;
  Phi := FrattiniSubgroup(pcg);
  if Size(Phi) = 1 then
    mg := Length(FactorsInt(Size(pcg)));
  else
    mg := Length(FactorsInt(Size(pcg))) - Length(FactorsInt(Size(Phi)));
  fi;
  n := Size(pcg);
  S := Elements(pcg);
  gens := [];
  H := Phi;
  for j in [1..mg] do
    posl := Filtered([1..n], i -> not S[i] in H);
    pos := Random(posl);
    this_gen := S[pos];
    Add(gens, this_gen);
    H := Subgroup(pcg, Concatenation(GeneratorsOfGroup(H), [this_gen]));
  od;
  if not Size(H) = Size(pcg) then
    Error("Theoretical error: Frattini orders"); fi;
  if not Size(Subgroup(pcg,gens)) = Size(pcg) then
    Error("Theoretical error in GetArbGenerators: ", Size(Subgroup(pcg,gens)));
  fi;
  return gens;
end;

# *****************************************************************************
GetSmallGenerators := function(pcg)
  local Phi, mg, n, S, gens, H, j, k, expl, posl, pos, this_gen, this_exp;
  Phi := FrattiniSubgroup(pcg);
  if Size(Phi) = 1 then
    mg := Length(FactorsInt(Size(pcg)));
  else
    mg := Length(FactorsInt(Size(pcg))) - Length(FactorsInt(Size(Phi)));
  fi;
  n := Size(pcg);
  S := Elements(pcg);
  expl := List([1..n], i -> Order(S[i]));
  gens := [];
  H := Phi;
  for j in [1..mg] do
    for k in Filtered([1..n], i -> S[i] in H) do
      expl[k] := n+1;
    od;
    this_exp := Minimum(expl);
    posl := Filtered([1..n], i -> expl[i] = this_exp);
    pos := Random(posl);
    this_gen := S[pos];
    Add(gens, this_gen);
    H := Subgroup(pcg, Concatenation(GeneratorsOfGroup(H), [this_gen]));
  od;
  if not Size(H) = Size(pcg) then
    Error("Theoretical error: Frattini orders"); fi;
  if not Size(Subgroup(pcg,gens)) = Size(pcg) then
    Error("Theoretical error in GetSmallGenerators: ", Size(Subgroup(pcg,gens)));
  fi;
  return gens;
end;

# *****************************************************************************
GetJenningsGenerators := function(gg)
  local p, js, gens, dims, this, next, n, mg, S, expl, H, j, posl, pos,
    dim, k, this_exp, this_gen;
  p := ThePrime(gg);
  js := JenningsSeries(gg);
  gens := [];
  dims := [];
  for dim in [1..Length(js)-1] do
    this := js[dim];
    next := js[dim+1];
    n := Size(this);
    if Size(next) = 1 then
      mg := Length(FactorsInt(Size(this)));
    else
      mg := Length(FactorsInt(Size(this))) - Length(FactorsInt(Size(next)));
    fi;
    S := Elements(this);
    expl := List([1..n], i -> Order(S[i]));
    H := next;
    for j in [1..mg] do
      for k in Filtered([1..n], i -> S[i] in H) do
        expl[k] := n+1;
      od;
      this_exp := Minimum(expl);
      posl := Filtered([1..n], i -> expl[i] = this_exp);
      pos := Random(posl);
      this_gen := S[pos];
      Add(gens, this_gen);
      Add(dims, dim);
      H := Subgroup(this, Concatenation(GeneratorsOfGroup(H), [this_gen]));
    od;
    if not Size(H) = Size(this) then
      Error("Theoretical error: Jennings orders");
    fi;
  od;
  if not Length(gens) = Length(FactorsInt(Size(gg))) then
    Error("Theoretical error: wrong number of Jennings generators");
  fi;
  return [gens, dims];
end;

# *****************************************************************************
testJenningsGenerators := function(gg)
  local p, js, gens, dims, soFar, dim, this, next, n, mg, these_gens, i;
  p := ThePrime(gg);
  js := JenningsSeries(gg);
  gens := GeneratorsOfGroup(gg);
  if not Length(gens) = Length(FactorsInt(Size(gg))) then
    Error("Incorrect number of generators");
  fi;
  dims := [];
  soFar := 0;
  for dim in [1..Length(js)-1] do
    this := js[dim];
    next := js[dim+1];
    n := Size(this);
    if Size(next) = 1 then
      mg := Length(FactorsInt(Size(this)));
    else
      mg := Length(FactorsInt(Size(this))) - Length(FactorsInt(Size(next)));
    fi;
    if not mg = 0 then
      these_gens := gens{[(soFar+1)..(soFar+mg)]};
      for i in [1..mg] do
        if not these_gens[i] in this then Error("Generators not Jennings"); fi;
      od;
      if not Subgroup(gg,
        Concatenation(these_gens, GeneratorsOfGroup(next))) = this then
        Error("Generators not Jennings");
      fi;
      for i in [1..mg] do
        Add(dims, dim);
      od;
      soFar := soFar + mg;
    fi;
  od;
  return dims;
end;

# *****************************************************************************
MinimallyGeneratedPermutationGroup := function(gg,arbgsm)
# Find a smallest set of generators for the p-group
  local phi, pcg, gens, ggens, ngg;
  phi := IsomorphismSpecialPcGroup(gg);
  pcg := Image(phi);
  if arbgsm then
    gens := GetArbGenerators(pcg);
  else
    gens := GetSmallGenerators(pcg);
  fi;
  ggens := List(gens, g -> PreImageElm(phi,g));
  ngg := Group(ggens);
  if not Size(ngg) = Size(gg) then
    Error("Theoretical error: ngg order ", Size(ngg));
  fi;
  return ngg;
end;

# *****************************************************************************
WriteOutPermsFile := function(name,ngg,m)
# m is the number of mintips
  local nameperms, gens, n, d, statusline, i;
  nameperms := Concatenation(name, ".perms");
  gens := GeneratorsOfGroup(ngg);
  n := Length(gens);
  d := LargestMovedPoint(ngg);
  statusline := Concatenation("# Permutation group ", name, " has ",
    String(n), " generators, ", "degree ", String(d), ".\n");
  PrintTo(nameperms, statusline);
  statusline := Concatenation("# There are ", String(m), " minimal tips.\n");
  AppendTo(nameperms, statusline);
  statusline := Concatenation("name := \"", name, "\";\n");
  AppendTo(nameperms, statusline);
  statusline := "G := Group(\n";
  AppendTo(nameperms, statusline);
  for i in [1..n] do
    AppendTo(nameperms, gens[i]);
    if i < n then
      AppendTo(nameperms,",\n");
    else
      AppendTo(nameperms,");\n");
    fi;
  od;
end;

# *****************************************************************************
writeOutMtxPerms := function(pl, outfile, tmpfile, nontips)
  local num, g, statusline, j, fp;
  num := Length(pl);
  statusline := Concatenation("12 1 ", String(nontips), " ",
    String(num));
  fp := OutputTextFile(tmpfile, false);
  WriteLine(fp, statusline); # Adds newline
  for g in pl do
    for j in [1..nontips] do
      WriteLine(fp, String(j^g));
    od;
  od;
  CloseStream(fp);
  Exec(Concatenation("zcv -Q ", tmpfile, " ", outfile));
  RemoveFile(tmpfile);
end;

# *****************************************************************************
createRegFile := function(name,ngg)
  local g, gens, gg, nametreg, namereg;
  # Now the permutations in Ringe format
  gg := asPermgroup(ngg); regularPermutationAction(ngg);
  gens := GeneratorsOfGroup(gg);
  nametreg := Concatenation(name, ".treg");
  namereg := Concatenation(name, ".reg");
  writeOutMtxPerms(gens, namereg, nametreg, Size(gg));
end;

# *****************************************************************************
destroyEvidence := function(tmpname)
  Exec(Concatenation("rm ", tmpname, ".nontips"));
  Exec(Concatenation("rm ", tmpname, ".reg"));
end;

# *****************************************************************************
renameStem := function(oldname, newname)
  Exec(Concatenation("mv ", oldname, ".nontips ", newname, ".nontips"));
  Exec(Concatenation("mv ", oldname, ".reg ", newname, ".reg"));
end;

# *****************************************************************************
completeStem := function(name, G, mintips)
  if name = "" then Error("completeStem: name cannot be the null string"); fi;
  Exec(Concatenation(exportMTXLIB, "makeActionMatrices ", name));
  WriteOutPermsFile(name,G,mintips);
end;

# *****************************************************************************
finishOff := function(ngg, name, tmpname, mintips)
  renameStem(tmpname, name);
  completeStem(name, ngg, mintips);
end;

# *****************************************************************************
chosenOrder := function(RLL)
  local orderString;
  if RLL then
    orderString := "RLL";
  else
    orderString := "LL";
  fi;
  return orderString;
end;

# *****************************************************************************
constructNonTips := function(name,gg,orderString)
  local nSL, mintips;
  createRegFile(name,gg);
  Exec(Concatenation(exportMTXLIB, "makeNontips -O ", orderString, "  ",
    String(ThePrime(gg)), " ", name));
  nSL := nontipsStatusLine(name);
  mintips := nSL[4];
  return mintips;
end;

# *****************************************************************************
arbitraryGsm := function(RLL,gsm)
# Returns true if arbitrary gsm chosen, false if smallest exponent gsm chosen
# Default is arbitrary for RLL, smallest exponent for LL
  if gsm = "arbitrary" then
    return true;
  elif gsm = "smallest" then
    return false;
  else
    return RLL;
  fi;
end;

# *****************************************************************************
listBasisSizes := function(gg,name,RLL,tries)
# Records number of mintips for <tries> generating sets.
  local gsm, orderString, arbgsm, results, tmpname, i, ngg, mintips;
  gsm := ValueOption("gsm");
  if not IsPermGroup(gg) then Error("Group must be a Permutation Group"); fi;
  orderString := chosenOrder(RLL);
  arbgsm := arbitraryGsm(RLL,gsm);
  results := [];
  tmpname := Concatenation(name, "tmp");
  for i in [1..tries] do
    ngg := MinimallyGeneratedPermutationGroup(gg,arbgsm);
    mintips := constructNonTips(tmpname,ngg,orderString);
    # Print("Attempt ", i, ": Groebner basis has size ", mintips, "\n");
    Add(results, mintips);
    destroyEvidence(tmpname);
  od;
  return results;
end;

# *****************************************************************************
makeSmallBasis := function(gg,name,RLL,tries)
# Has <tries> attempts at finding generators giving at most <most> mintips.
# To get <most> = +infinity, set <most> = 0.
  local gsm, most, orderString, arbgsm, found, bestname, tmpname, best,
    i, ngg, mintips, inSeries;
  gsm := ValueOption("gsm");
  most := ValueOption("most");
  inSeries := ValueOption("inSeries");
  if not IsPermGroup(gg) then Error("Group must be a Permutation Group"); fi;
  orderString := chosenOrder(RLL);
  arbgsm := arbitraryGsm(RLL,gsm);
  found := false;
  bestname := "";
  tmpname := Concatenation(name, "tmp");
  if most > 0 then
    best := most+1;
  else
    best := 0;
  fi;
  for i in [1..tries] do
    ngg := MinimallyGeneratedPermutationGroup(gg,arbgsm);
    mintips := constructNonTips(tmpname,ngg,orderString);
    # Print("Attempt ", i, ": Groebner basis has size ", mintips, "\n");
    if best = 0 or mintips < best then
      # Print("Best yet\n");
      if found then
        destroyEvidence(bestname);
      fi;
      best := mintips;
      if inSeries then
        bestname := name;
      else
        bestname := Concatenation(name, String(best));
      fi;
      renameStem(tmpname, bestname);
      found := true;
    else
      destroyEvidence(tmpname);
    fi;
  od;
  if found then
    completeStem(bestname, ngg, best);
    return best;
  else
    return -1;
  fi;
end;

# *****************************************************************************
makeBasis := function(gg,name,RLL)
  local gsm, TG, orderString, mintips, arbgsm, ngg;
  gsm := ValueOption("gsm");
  TG := ValueOption("TG");
  if not IsPermGroup(gg) then Error("Group must be a Permutation Group"); fi;
  orderString := chosenOrder(RLL);
  if TG then
    # Print("Number of Generators: ", Size(GeneratorsOfGroup(gg)), "\n");
    mintips := constructNonTips(name,gg,orderString);
    Exec(Concatenation(exportMTXLIB, "makeActionMatrices ", name));
  else
    arbgsm := arbitraryGsm(RLL,gsm);
    ngg := MinimallyGeneratedPermutationGroup(gg,arbgsm);
    mintips := constructNonTips(name,ngg,orderString);
    # Print("Groebner basis has size ", mintips, "\n");
    completeStem(name,ngg,mintips);
  fi;
  return mintips;
end;

# *****************************************************************************
makeJenningsBasis := function(gg,name)
  local TG, dims, ngg, xxx, gens, dimfile, i, nSL, mintips;
  TG := ValueOption("TG");
  if not IsPermGroup(gg) then Error("Group must be a Permutation Group"); fi;
  if TG then
    dims := testJenningsGenerators(gg);
    ngg := gg;
  else
    xxx := GetJenningsGenerators(gg);
    gens := xxx[1];
    dims := xxx[2];
    ngg := Subgroup(gg,gens);
  fi;
  createRegFile(name,ngg);
  dimfile := Concatenation(name, ".dims");
  PrintTo(dimfile, Length(dims), "\n");
  for i in [1..Length(dims)] do
    AppendTo(dimfile, dims[i], "\n");
  od;
  Exec(Concatenation(exportMTXLIB, "makeNontips -OJ ", String(ThePrime(ngg)), " ", name));
  Exec(Concatenation(exportMTXLIB, "makeActionMatrices ", name));
  nSL := nontipsStatusLine(name);
  mintips := nSL[4];
  if not TG then
    WriteOutPermsFile(name, ngg, mintips);
  fi;
end;

# *****************************************************************************
PushOptions(rec(TG := false, most := 0, gsm := "default", inSeries := false,
  forceDefiningGenerators := false));

# *****************************************************************************
PermGroupAtlas := function(istem, n)
  local fp, l, d, pl, G, i, j;
  fp := InputTextFile(Concatenation(istem,".1"));
  d := StringToIntegerSequence(ReadLine(fp))[3];
  CloseStream(fp);
  pl := [];
  for i in [1..n] do
    fp := InputTextFile(Concatenation(istem, ".", String(i)));
    ReadLine(fp); # Discard first line
    l := [];
    for j in [1..d] do
      Add(l, StringToIntegerSequence(ReadLine(fp))[1]);
    od;
    CloseStream(fp);
    Add(pl, PermList(l));
  od;
  G := Group(pl);
  return G;
end;

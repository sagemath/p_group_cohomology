#*****************************************************************************
#
# Computing maximal elementary abelian subgroups of finite p-groups
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

allPeltsCentral := function(p, G)
  local pelts, ZG, ncPelts;
  pelts := Filtered(Elements(G), g -> Order(g) = p);
  ZG := Center(G);
  ncPelts := Filtered(pelts, g -> not g in ZG);
  return Length(ncPelts) = 0;
end;

containsAllPelts := function(p, G, V)
  local pelts, ncPelts;
  pelts := Filtered(Elements(G), g -> Order(g) = p);
  ncPelts := Filtered(pelts, g -> not g in V);
  return Length(ncPelts) = 0;
end;

innerGreatestCentralElab := function(p,G,H)
  local ZH, Zdash, cPelts;
  ZH := Center(H);
  cPelts := Filtered(Elements(ZH), g -> Order(g) = p);
  Zdash := Subgroup(G, cPelts);
  return Zdash;
end;

greatestCentralElab := function(G)
  local p;
  p := FactorsInt(Size(G))[1];
  return innerGreatestCentralElab(p,G,G);
end;

nextTierElabReps := function(p,G,H,W)
  # W elem ab, central in H
  local ncV, ncVconj, tier, pelts, ncPelts, gensW, remain, gens, V;
  pelts := Filtered(Elements(H), g -> Order(g) = p);
  gensW := GeneratorsOfGroup(W);
  ncPelts := Filtered(pelts, g -> not g in W);
  remain := ShallowCopy(ncPelts);
  tier := [];
  ncVconj := [];
  while Length(remain) > 0 do
    gens := ShallowCopy(gensW);
    Add(gens, remain[1]);
    V := Subgroup(G, gens);
    ncV := Filtered(Elements(V), g -> not g in W);
    ncVconj := Flat(List(ncV, g -> Elements(ConjugacyClass(H, g))));
    remain := Filtered(remain, g -> not g in ncVconj);
    Add(tier, V);
  od;
  return tier;
end;

elabClasses := function(G)
  local q, p, r, tier, CGtier, vital, preTier, H, U, V, Vcc, Zdash,
    maxels, elabs, nextTier, i, l;
  q := Size(G);
  p := FactorsInt(q)[1];
  elabs := [];
  maxels := [];
  Zdash := innerGreatestCentralElab(p,G,G);
  r := Length(FactorsInt(Size(Zdash)));
  tier := [Zdash];
  Add(elabs, [tier, r]);
  CGtier := List(tier, W -> Centralizer(G, W));
  vital := Filtered([1..Length(tier)],
    i -> not containsAllPelts(p,CGtier[i], tier[i]));
  while Length(vital) > 0 do
    if Length(vital) < Length(tier) then
      l := [1..Length(tier)];
      for i in vital do Unbind(l[i]); od;
      l := Compacted(l);
      Add(maxels, [List(l, i -> tier[i]), r]);
    fi;
    preTier := [];
    for i in vital do
      H := CGtier[i];
      U := tier[i];
      nextTier := nextTierElabReps(p,G,H,U);
      Append(preTier, nextTier);
    od;
    tier := [];
    while Length(preTier) > 0 do
      V := preTier[1];
      Add(tier, V);
      Vcc := ConjugacyClassSubgroups(G, V);
      preTier := Filtered(preTier, W -> not W in Vcc);
    od;
    r := r + 1;
    Add(elabs, [tier, r]);
    CGtier := List(tier, W -> Centralizer(G, W));
    vital := Filtered([1..Length(tier)],
      i -> not containsAllPelts(p,CGtier[i], tier[i]));
  od;
  Add(maxels, [tier, r]);
  return [elabs, maxels];
end;

pRank :=function(G)
  local ec1,n;
  ec1 := elabClasses(G)[1];
  n:=Length(ec1);
  return ec1[n][2];
end;

elabCentralizers := function(G,elabs)
  return List(elabs, xxx -> [List(xxx[1], V -> Centralizer(G,V)), xxx[2]]);
end;

tiersGroupids := function(tiers)
  return List(tiers, xxx -> [List(xxx[1], H -> IdGroup(H)), xxx[2]]);
end;

# =========================== NEW FEBRUARY 2010 ====================
# ---------------------------  David J. Green   --------------------

omegaZ := function(G,p)
  return Omega(Centre(G),p);
end;

nicelyGeneratedOmegaZC := function(G,V,p)
  local C, f, gg;
  C := omegaZ(Centralizer(G,V),p);
  f := NaturalHomomorphismByNormalSubgroupNC(C,V);
  gg := List(IndependentGeneratorsOfAbelianGroup(ImagesSource(f)),
    g -> PreImagesRepresentative(f,g));
  return Group(Concatenation(GeneratorsOfGroup(V), gg));
end;

incrementalElabs := function(G,Cgens,p)
  # Cgens should be a generating set of Omega(Centre(G),p)
  local C,f,Q,cc,vv;
  C := Group(Cgens);
  if not C = omegaZ(G,p) then Error("incrementalElabs: theoretical error\n"); fi;
  f := NaturalHomomorphismByNormalSubgroupNC(G,C);
  Q := ImagesSource(f);
  cc := List(RationalClasses(Q),Representative);
  cc := Filtered(cc, g -> Order(g)=p);
  cc := List(cc, g -> PreImagesRepresentative(f,g));
  cc := Filtered(cc, g -> Order(g)=p);
  vv := List(cc, g -> Group(Concatenation(Cgens,[g])));
  return List(vv, V -> nicelyGeneratedOmegaZC(G,V,p));
end;

incrementalStepElabs := function(G,Cgens,p)
  # Add exactly one more generator in all possible ways
  # (different from incrementalElabs, which may add more stuff)
  # Cgens should be a generating set of Omega(Centre(G),p)
  local C,f,Q,cc,vv;
  C := Group(Cgens);
  if not IsSubgroup(omegaZ(G,p),C) then Error("incrementalElabs: theoretical error\n"); fi;
  f := NaturalHomomorphismByNormalSubgroupNC(G,C);
  Q := ImagesSource(f);
  cc := List(RationalClasses(Q),Representative);
  cc := Filtered(cc, g -> Order(g)=p);
  cc := List(cc, g -> PreImagesRepresentative(f,g));
  cc := Filtered(cc, g -> Order(g)=p);
  return List(cc, g -> Group(Concatenation(Cgens,[g])));
end;

splitByProperty := function(l, f)
# f(x) is true or false for each x in l
# Returns [lT,lF]: lT = List of x in l with l(x)=T
  local ii, jj, i;
  ii := Filtered([1..Length(l)], i -> f(l[i]));
  jj := [1..Length(l)];
  for i in ii do Unbind(jj[i]); od;
  jj := Compacted(jj);
  return [List(ii, i -> l[i]), List(jj, j -> l[j])];
end;

weedConjugates := function(G,vv)
  local result, ww, i, V;
  ww := ShallowCopy(vv);
  result := [];
  while Length(ww) > 0 do
    V := ww[1];
    Add(result, V);
    for i in [1..Length(ww)] do
      if i = 1 or IsConjugate(G,V,ww[i]) then
        Unbind(ww[i]);
      fi;
    od;
    ww := Compacted(ww);
  od;
  return result;
end;

SylowElabsWithRank := function(S,Om, p,r, z)
  #Simon King (2010-08): Find all S-conjugacy classes of rank r p-elementary abelian
  # subgroups of S containing Om, where S is a p-group and Om is omegaZ(S,p),
  # which is of rank z.
  local vv, found, V;
  if r = z then
    return [Group(IndependentGeneratorsOfAbelianGroup(Om))];
  fi;
  found := [];
  vv := SylowElabsWithRank(S,Om,p,r-1,z);
  for V in vv do
    Append(found, incrementalStepElabs(Centralizer(S, V),GeneratorsOfGroup(V),p) );
  od;
  return weedConjugates(S,found);
end;

ElabsWithRank := function(G,p,r)
  #Simon King (2010-08): Find all G-conjugacy classes of rank r p-elementary abelian
  # subgroups of S containing omegaZ(S,p), where S is a Sylow p-subgroup of G
  local S, Om;
  S := SylowSubgroup(G,p);
  Om :=omegaZ(S,p);
  return weedConjugates(G, SylowElabsWithRank(S,Om,p,r, pRank(Om)));
end;

newMaxels := function(G)
  local p, vv, n, xxx, ww, found, later, new, V, this;
  p := FactorsInt(Size(G))[1];
  found := [];
  vv := [Group(IndependentGeneratorsOfAbelianGroup(omegaZ(G,p)))];
  while Length(vv) > 0 do
    n := Minimum(List(vv,Size));
    # Print("newMaxels: n = ", n, "  |found| = ", Length(found), "  |vv| = ", Length(vv), "\n");
    xxx := splitByProperty(vv, V -> Size(V) = n);
    this := weedConjugates(G,xxx[1]);
    later := weedConjugates(G,xxx[2]);
    # Print("|this| = ", Length(this), "  |later| = ", Length(later), "\n");
    new := [];
    for V in this do
      ww := incrementalElabs(Centralizer(G, V),GeneratorsOfGroup(V),p);
      if Length(ww) = 0 then
        Add(found,V);
      else
        Append(new, ww);
      fi;
    od;
    vv := Concatenation(new, later);
  od;
  return found;
end;

tierified := function(vv)
  local n, this, tier, r, later, xxx;
  tier := [];
  later := vv;
  while Length(later) > 0 do
    n := Minimum(List(later,Size));
    xxx := splitByProperty(later, V -> Size(V) = n);
    this := xxx[1];
    later := xxx[2];
    r := Length(GeneratorsOfGroup(this[1]));
    Add(tier, [this,r]);
  od;
  return tier;
end;

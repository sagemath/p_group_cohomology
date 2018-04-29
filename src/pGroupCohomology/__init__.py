# -*- coding: utf-8 -*-

#*****************************************************************************
#
#    Sage Package "Modular Cohomology Rings of Finite Groups"
#
#    Copyright (C) 2009, 2010, 2015 Simon A. King  <simon.king@uni-jena.de>
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
r"""
Modular Cohomology Rings of Finite Groups (top level documentation).

AUTHORS:

- Simon King  <simon.king@uni-jena.de> (Cython and Python code, porting, maintainance)
- David Green <david.green@uni-jena.de> (underlying C code)

IMPLEMENTATION:

Our package is formed by Singular- and Gap-functions, as well as Python-, Cython- and C-code.

NOTE:

    Our package uses the `Small Groups <http://www-public.tu-bs.de:8080/~hubesche/small.html>`_
    library of Hans Ulrich Besche, Bettina Eick and Eamonn O'Brien. It
    should be installed in Sage by ``sage -i database_gap``.

Modular cohomology rings of a finite group `G` are available via the constructor
:func:`CohomologyRing`. The real work behind the scenes is done in the modules
:mod:`~pGroupCohomology.factory`,
:mod:`~pGroupCohomology.cohomology`,
:mod:`~pGroupCohomology.modular_cohomology`,
:mod:`~pGroupCohomology.barcode`, :mod:`~pGroupCohomology.cochain`,
:mod:`~pGroupCohomology.resolution` and
:mod:`~pGroupCohomology.dickson`.

In the first section of our introduction, we demonstrate the usage of
our package. After outlining the functionality, we go into more detail
and illustrate various ways of defining a cohomology ring, computing
the ring structure, and working in the cohomology ring.  Last, we
discuss how to save and load a cohomology ring on a local file system
and how to export and import it to a different platform.

In the second section, we give an overview on the theoretical
background of our package. The emphasis is on the construction of
parameters for the cohomology ring, which can then be used to prove
completeness of the ring structure by means of completeness criteria
that are due to different authors ([Benson]_, [GreenKing]_, [King]_,
[Symonds]_).  We illustrate this with step-by-step examples.

An overview of the various options that can be used is given in the
documentation of :func:`CohomologyRing`.

**In a nutshell**

- One starts with a finite group ``G`` (either a group in GAP, a pair
  of numbers denoting an address in the SmallGroups library, or a string
  defining the group) and a prime number ``p``
- One configures the cohomology ring by ``H = CohomologyRing(G, prime=p)``.
  The prime can be ommitted if ``G`` is a prime power group.
- One makes the cohomology ring by ``H.make()``.

In most cases, the computation of ``H`` doesn't involve further action.
However, sometimes particular options help with the computation. This
documentation describes the underlying theory, the available options,
reveals the underlying computational steps, and of course documents
further data that this package can compute.

EXAMPLES:

1. Synopsis
===========

Our package is devoted to the cohomology rings of finite groups with
coefficients in `\mathbb F_p` (the finite field with `p` elements,
where `p` is a prime less than 255 that divides the group order).
Note that the first computation of the modular cohomology rings of all
groups of order 128 and the first computation of the mod-2 cohomology
ring of the third Conway group where obtained with our package; see
[GreenKing]_ and [KingGreenEllis]_ for more details. We computed the
mod-`p` cohomology rings for various interesting finite non prime
power groups and different primes `p`. Our results are available
`here <http://users.minet.uni-jena.de/~king/cohomology/nonprimepower/>`_. The non
prime power groups are not part of our web repository yet.

We expect the groups to be given either by their address in the Small
Groups Library, or as a group in Sage's Gap interface. In the latter
case and if `G` happens to be a prime power group, it is required that
the list of generators of `G` starts with a minimal generating set. If
this is not the case, a ``ValueError`` is raised. Internally, the group
will be transformed into a permutation group, which, in some cases, is
very difficult. So, it is recommended to start with a permutation group
right away.

The package is shipped with the cohomology rings for all groups of
order 64; the data are stored in folders and can simply be retrieved
by calling :func:`~pGroupCohomology.CohomologyRing` with appropriate
keys.  These data are provided to *all* users of the Sage installation
and we refer to it as the *local sources*.

In addition, we provide the cohomology rings for all groups of order
128 and for all but six groups of order 243 in a web repository.
Unless the user requires a recomputation from scratch, these data will
be automatically downloaded. In future versions, this will also be
possible for various non prime power groups.

Any user can construct new databases; we refer to them as a *workspace*.
At each time, there only is a single workspace, and it is used to
store all data created in cohomology computations. It is possible to
switch between workspaces. There is a default location in a sub-directory
of ``DOT_SAGE``. But any location may be chosen as well, provided that
the user has write permission.

Cohomology rings are parent structures and are cached. That means, if
two groups are essentially equal then their cohomology rings will be
identic (and not only equal). Note for two groups being "essentially equal",
it does not suffice that they are isomorphic. All groups are supposed
to have a fixed list of generators. Two groups are "essentially equal",
if there exists a group isomorphism that sends the list of generators
of one group to an initial segment of the list of generators of the
other group. Moreover, two cohomology rings can only be identic if
they have the same location of data storage.

When a cohomology ring is created, the following locations are
searched, in order:

1. It is first tried to find the result in the cache.

2. It is tried to load it from the current workspace.

3. If it is not there, the default is to try to find it in the local sources.

4. Finally, by default it is attempted to download the result from a web
   repository, which we refer to as *remote sources*.

Data from either local or remote sources are mirrored in the workspace,
which is because the user does not necessarily have write permissions to
alter the local sources. To be precise, symbolic links are created in
the workspace that link to data in the local sources. If further
computation requires more data, they are created and stored in the workspace.
If all this fails, a new ring is initialized in the current workspace.

The data belonging to the cohomology ring of a prime power group (e.g., a minimal
free resolution, information on embedding of elementary abelian subgroups, standard
monomials etc.) are distributed in a folder tree, one tree for each group.

In the non prime power case, the situation is easier. It is not needed to
store small data pieces during the computation, and eventually the main
data are saved in a single file. Its default location is in the current
workspace. The computation does, however, rely on the cohomology rings
of various subgroups, e.g., a Sylow subgroup. So, again the data are distributed.

Creating a cohomology ring
--------------------------

In the following subsections, we explain here how to describe the
group whose modular cohomology ring shall be computed.

There are also various global options that influence the algorithm and
the use of databases. For example, it might be instructive to use logging;
the log gives detailed information on how data are computed (the "debug"
logging level is of course even more verbous). Global options can be
changed at any time using the method
:meth:`~pGroupCohomology.factory.CohomologyRingFactory.global_options`.

Usually, the package attempts to make use of existing data. However,
if the optional parameter ``from_scratch`` is set to ``True`` then
this cohomology ring is not loaded from local or remote sources.
Note, however, that this option only takes effect on the
ring itself, but not for cohomology rings of certain subgroups that
might be created during the computation.

Further options are described in the documentation of
:func:`~pGroupCohomology.CohomologyRing`.

... using the SmallGroups library
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In our examples, we put the workspace into a temporary directory.
Of course, in reality, a permanent directory would be chosen instead.
We do so in order to avoid a conflict with an existing workspace.
::

    sage: from pGroupCohomology import CohomologyRing
    sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
    sage: H0 = CohomologyRing(8,3)

Since the cohomology ring of ``SmallGroup(8,3)``, which is the
Dihedral Group of order 8, is in the local sources shipped with our
package, it is simply loaded and already completely computed. It is
not needed to specify a prime to determine the coefficients, since the
group is of prime power order. Note that we also have a list of group
names and group descriptions -- hence, ``H0`` knows that it belongs to
the Dihedral Group of order 8::

    sage: H0
    H^*(D8; GF(2))
    sage: print(H0)
    Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
     b_1_0: 1-Cocycle in H^*(D8; GF(2)),
     b_1_1: 1-Cocycle in H^*(D8; GF(2))]
    Minimal list of algebraic relations:
    [b_1_0*b_1_1]

The generators are of type :class:`~pGroupCohomology.cochain.COCH`.
It is also possible to convert the cohomology ring into a quotient
ring in the Singular interface::

    sage: singular(H0)
    polynomial ring, over a field, global ordering
    // coefficients: ZZ/2
    // number of vars : 3
    //        block   1 : ordering M
    //                  : names    c_2_2 b_1_0 b_1_1
    //                  : weights      2     1     1
    //                  : weights     -1     0     0
    //                  : weights      0    -1     0
    //        block   2 : ordering C
    // quotient ring from ideal
    _[1]=b_1_0*b_1_1

In Sage, parent structures should be unique. And indeed, cohomology
rings of *the same* group in *the same* workspace are unique::

    sage: H0 is CohomologyRing(8,3)
    True
    sage: H0 is loads(dumps(H0))
    True

We set up a different workspace in a temporary directory, and show that
indeed two cohomology rings are only identical if their data are stored
in the same place. Moreover, we use an optional argument to avoid that
the ring is loaded from the local or remote sources::

    sage: tmp = tmp_dir()
    sage: CohomologyRing.set_workspace(tmp)
    sage: H1 = CohomologyRing(8,3,from_scratch=True)
    sage: H1 is H0
    False

Since we used the option ``from_scratch=True``, it was not attempted
to download the cohomology ring from local or remote sources. Hence,
beyond the basic setup, ``H1`` is unknown and is thus not even equal
to ``H0``::

    sage: H0 == H1
    False

We now compute ``H1`` (see below for the theoretical background) and
verify that then ``H0`` is equal (though not identical) to ``H1``::

    sage: H1.make()
    sage: H0 == H1
    True

Here is a similar example, using a non prime power group. In this
case, we need to provide the modulus by the optional parameter
``prime``.

::

    sage: HS6a = CohomologyRing(720,763,prime=2)
    sage: HS6a.make()
    sage: print(HS6a)
    Cohomology ring of SmallGroup(720,763) with coefficients in GF(2)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_1: 2-Cocycle in H^*(SmallGroup(720,763); GF(2)),
     c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2)),
     b_3_3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
     c_3_2: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))]
    Minimal list of algebraic relations:
    [b_3_3*c_3_2+c_2_1*c_1_0*b_3_3]
    sage: singular(HS6a)
    polynomial ring, over a field, global ordering
    // coefficients: ZZ/2
    // number of vars : 4
    //        block   1 : ordering M
    //                  : names    c_2_1 c_1_0 b_3_3 c_3_2
    //                  : weights      2     1     3     3
    //                  : weights     -1    -1     0    -1
    //                  : weights     -1     0     0     0
    //                  : weights      0    -1     0     0
    //        block   2 : ordering C
    // quotient ring from ideal
    _[1]=b_3_3*c_3_2+c_2_1*c_1_0*b_3_3

... using a group in the Gap interface
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Above, we mentioned that two cohomology rings are identic only if the
corresponding groups are essentially equal. Indeed, if we represent
the Dihedral Group of order 8 in a different way then we obtain a
different ring presentation. Note that, when referring to a group in
the Gap interface, we need to provide a name for that group, in one or
the other way. That name also determines the location of data storage,
and thus if two different names are provided then the corresponding
cohomology rings are not the same::

    sage: G = gap('DihedralGroup(8)')
    sage: H2 = CohomologyRing(G,GroupName='DihedralA')
    sage: G.SetName('"DihedralB"')
    sage: H3 = CohomologyRing(G)
    sage: H2 is H3
    False

Of course, when ``H2`` and ``H3`` are completely computed, they are
isomorphic to ``H1``, since they belong to isomorphic groups. However,
they do not have the same ring presentation. This is because the
presentation of the cohomology ring depends on the choice of a minimal
generating set of the group; and the minimal generating sets of
``gap('SmallGroup(8,3)')`` and of ``gap('DihedralGroup(8)')`` are
essentially different::

    sage: H2.make()
    sage: H3.make()
    sage: H2 == H3
    True
    sage: H2 == H1
    False

Indeed, the minimal relations of ``H1`` and ``H2`` look different::

    sage: print(H1)
    Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
     b_1_0: 1-Cocycle in H^*(D8; GF(2)),
     b_1_1: 1-Cocycle in H^*(D8; GF(2))]
    Minimal list of algebraic relations:
    [b_1_0*b_1_1]
    sage: print(H2)
    Cohomology ring of DihedralA with coefficients in GF(2)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_2: 2-Cocycle in H^*(DihedralA; GF(2)),
     b_1_0: 1-Cocycle in H^*(DihedralA; GF(2)),
     b_1_1: 1-Cocycle in H^*(DihedralA; GF(2))]
    Minimal list of algebraic relations:
    [b_1_1^2+b_1_0*b_1_1]

But of course, the rings are isomorphic.

Above, we computed the cohomology of some non prime power group. It is
in fact a symmetric group::

    sage: G = gap('SymmetricGroup(6)')
    sage: HS6b = CohomologyRing(G, prime=2, GroupName='SymmetricGroup(6)', from_scratch=True)
    sage: HS6b.make()
    sage: print(HS6b)
    <BLANKLINE>
    Cohomology ring of SymmetricGroup(6) with coefficients in GF(2)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_1: 2-Cocycle in H^*(SymmetricGroup(6); GF(2)),
     c_1_0: 1-Cocycle in H^*(SymmetricGroup(6); GF(2)),
     b_3_2: 3-Cocycle in H^*(SymmetricGroup(6); GF(2)),
     c_3_3: 3-Cocycle in H^*(SymmetricGroup(6); GF(2))]
    Minimal list of algebraic relations:
    [b_3_2^2+b_3_2*c_3_3+c_2_1*c_1_0*b_3_2]
    <BLANKLINE>

Obviously the two ring presentations for the mod-2 cohomology of the
symmetric group of rank 6 are different. This is since the ring
presentation will essentially depend on the choice of generators of
the Sylow subgroup (which here is chosen by the program).


Computations in a cohomology ring
---------------------------------

Ring theoretic invariants
^^^^^^^^^^^^^^^^^^^^^^^^^

Up to now, we implemented the computation of four ring theoretic
invariants, namely the dimension, the depth, the `a`-invariants and
the Poincaré series::

    sage: H2.dimension()
    2
    sage: H2.depth()
    2
    sage: H2.a_invariants()
    [-Infinity, -Infinity, -2]
    sage: H2.poincare_series()
    1/(t^2 - 2*t + 1)

Of course, they are the same for both presentations of the cohomology
ring of the dihedral group of order 8::

    sage: H1.dimension()
    2
    sage: H1.depth()
    2
    sage: H1.a_invariants()
    [-Infinity, -Infinity, -2]
    sage: H1.poincare_series()
    1/(t^2 - 2*t + 1)

Actually we implemented two essentially different ways of computating
the Poincaré series. The method
:meth:`~pGroupCohomology.cohomology.COHO.poincare_without_parameters`
is usually much slower than
:meth:`~pGroupCohomology.cohomology.COHO.poincare_series`, but of
course the results are the same::

    sage: H2.poincare_without_parameters()
    1/(t^2 - 2*t + 1)

After computing the ring structure, generators and relations of the
cohomology ring are present. Generator number zero is the
multiplicative unit of the underlying field. The other generators are
represented by cochains (:class:`~pGroupCohomology.cochain.COCH`, or
:class:`~pGroupCohomology.cochain.MODCOCH` for non prime power groups)::

    sage: H1.gens()
    [1, c_2_2: 2-Cocycle in H^*(D8; GF(2)), b_1_0: 1-Cocycle in H^*(D8; GF(2)), b_1_1: 1-Cocycle in H^*(D8; GF(2))]

The relations are given as strings::

    sage: H1.rels()
    ['b_1_0*b_1_1']

The relations can be interpreted as elements of the cohomology ring,
and indeed they vanish::

    sage: print(H1(H1.rels()[0]))
    2-Cocycle in H^*(D8; GF(2)),
    represented by
    [0 0 0]

We can also compute the nil radical, i.e., the ideal formed by all
nilpotent elements. It is given in the Singular interface, as an ideal
in a free graded commututive ring. In particular, all elements of the
relation ideal of the cohomology ring are in the nil radical. For the
dihedral group of order 8, the nil radical vanishes::

    sage: H1.nil_radical()
    0
    sage: H2.nil_radical()
    0

Here are the data for the mod-2 cohomology of the symmetric group of
degree 6::

    sage: HS6a.dimension()
    3
    sage: HS6a.depth()
    3
    sage: HS6a.a_invariants()
    [-Infinity, -Infinity, -Infinity, -3]
    sage: HS6a.poincare_series()
    (-t^2 + t - 1)/(t^5 - 2*t^4 + t^3 - t^2 + 2*t - 1)
    sage: HS6a.poincare_without_parameters()
    (-t^2 + t - 1)/(t^5 - 2*t^4 + t^3 - t^2 + 2*t - 1)
    sage: HS6a.nil_radical()
    0


Induced maps
^^^^^^^^^^^^

As we have seen before, the presentation of the cohomology ring
depends on the choice of a minimal generating set of the underlying
finite `p`-group (resp. Sylow `p`-subgroup). For our purposes, we always
assume that a finite group has a fixed set of generators, and we call
two groups *equivalent*, if there is a group isomorphism that maps the
given list of generators of one group to an initial segment of the list
of generators of the other group.

:meth:`~pGroupCohomology.cohomology.COHO.group` returns a permutation
group in the gap interface equivalent to the one that was used to set up the
cohomology ring::

    sage: G1 = H1.group()
    sage: G1
    Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] )
    sage: G2 = H2.group()
    sage: G2
    Group( [ (1,2)(3,8)(4,6)(5,7), (1,3,4,7)(2,5,6,8), (1,4)(2,6)(3,7)(5,8) ] )

Apparently, ``G1`` and ``G2`` are different permutation groups. But in
fact they are isomorphic. Note that we could get a group isomorphism
by Gap's function ``IsomorphismGroups``. But the result is not
unique. In order to have reproducible doc tests, we provide an
explicit isomorphism::

    sage: phi = gap('GroupHomomorphismByImages(Group([(1,2)(3,8)(4,6)(5,7),(1,3)(2,5)(4,7)(6,8)]), Group([(1,2)(3,8)(4,6)(5,7),(1,3,4,7)(2,5,6,8),(1,4)(2,6)(3,7)(5,8) ]), [(1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8)], [(1,6)(2,4)(3,5)(7,8), (1,8)(2,7)(3,6)(4,5)])')
    sage: phi.IsInjective()
    true
    sage: phi.IsSurjective()
    true

Of course, the group isomorphism induces an isomorphism of the
corresponding cohomology rings. After ensuring that ``phi`` is printed
nicely, we obtain the induced map::

    sage: phi.SetName('"phi"')
    sage: phi_star = H2.hom(phi,H1)
    sage: phi_star
    phi^*

Indeed, we can verify that the image of the relation of ``H2`` is zero
in ``H1``::

    sage: H2.rels()
    ['b_1_1^2+b_1_0*b_1_1']
    sage: phi_star(H2('b_1_1'))^2 + phi_star(H2('b_1_0'))*phi_star(H2('b_1_1'))
    (phi^*(b_1_1))**2+(phi^*(b_1_0))*(phi^*(b_1_1)): 2-Cocycle in H^*(D8; GF(2))
    sage: print(phi_star(H2('b_1_1'))^2 + phi_star(H2('b_1_0'))*phi_star(H2('b_1_1')))
    2-Cocycle in H^*(D8; GF(2)),
    represented by
    [0 0 0]

We can also compute the inverse of ``phi_star``, compose the two maps,
and see that it is the identity map::

    sage: phi_star_inv = phi_star^(-1)
    sage: phi_star_inv
    (phi^*)^(-1)
    sage: [(phi_star_inv*phi_star)(X) == X for X in H2.gens()]
    [True, True, True, True]
    sage: [(phi_star*phi_star_inv)(X) == X for X in H1.gens()]
    [True, True, True, True]

It is possible to convert an induced homomorphism into a map of
quotient rings in the Singular interface. This allows for working with
cohomology ring elements of very high degrees. However, it is always
needed to take care of the ``basering`` in Singular::

    sage: S_phi_star = singular(phi_star)
    sage: singular(H2).set_ring()
    sage: I = singular.ideal(['c_2_2^50','b_1_0^50','b_1_1^50'])
    sage: singular(H1).set_ring()
    sage: S_phi_star(I)
    b_1_1^100+c_2_2^2*b_1_1^96+c_2_2^16*b_1_1^68+c_2_2^18*b_1_1^64+c_2_2^32*b_1_1^36+c_2_2^34*b_1_1^32+c_2_2^48*b_1_1^4+c_2_2^50,
    b_1_1^50+b_1_0^2*b_1_1^48+b_1_0^16*b_1_1^34+b_1_0^18*b_1_1^32+b_1_0^32*b_1_1^18+b_1_0^34*b_1_1^16+b_1_0^48*b_1_1^2+b_1_0^50,
    b_1_1^50

Note that Singular does not do automatic reduction in quotient
rings. So, eventually we do the reductions explicitly, in two ways,
with the same result::

    sage: S_phi_star(I).reduce(singular('ideal(0)'))
    b_1_1^100+c_2_2^2*b_1_1^96+c_2_2^16*b_1_1^68+c_2_2^18*b_1_1^64+c_2_2^32*b_1_1^36+c_2_2^34*b_1_1^32+c_2_2^48*b_1_1^4+c_2_2^50,
    b_1_1^50+b_1_0^50,
    b_1_1^50
    sage: singular(H2).set_ring()
    sage: I = I.reduce(singular('ideal(0)'))
    sage: singular(H1).set_ring()
    sage: S_phi_star(I)
    b_1_1^100+c_2_2^2*b_1_1^96+c_2_2^16*b_1_1^68+c_2_2^18*b_1_1^64+c_2_2^32*b_1_1^36+c_2_2^34*b_1_1^32+c_2_2^48*b_1_1^4+c_2_2^50,
    b_1_1^50+b_1_0^2*b_1_1^48+b_1_0^16*b_1_1^34+b_1_0^18*b_1_1^32+b_1_0^32*b_1_1^18+b_1_0^34*b_1_1^16+b_1_0^48*b_1_1^2+b_1_0^50,
    b_1_1^50+b_1_0*b_1_1^49+b_1_0^16*b_1_1^34+b_1_0^17*b_1_1^33+b_1_0^32*b_1_1^18+b_1_0^33*b_1_1^17+b_1_0^48*b_1_1^2+b_1_0^49*b_1_1
    sage: S_phi_star(I).reduce(singular('ideal(0)'))
    b_1_1^100+c_2_2^2*b_1_1^96+c_2_2^16*b_1_1^68+c_2_2^18*b_1_1^64+c_2_2^32*b_1_1^36+c_2_2^34*b_1_1^32+c_2_2^48*b_1_1^4+c_2_2^50,
    b_1_1^50+b_1_0^50,
    b_1_1^50

For a non prime power group, a permutation representation equivalent to the given group,
a subgroup which was used for the stable element method and a Sylow `p`-subgroup are available
as well::

    sage: HS6a.group()
    Group( [ (1,2), (1,2,3,4,5,6) ] )
    sage: HS6a.subgroup()
    Group( [ (1,3)(2,5), (1,2), (4,6), (1,2)(3,5) ] )
    sage: HS6a.sylow_subgroup()
    Group( [ (1,3)(2,5), (1,2), (4,6) ] )

The dihedral group of order 8 is a subgroup of the symmetric group of
rank 6. We compute the ring homomorphism that is induced by the
embedding. In order to get a reproducible result, we define the
group homomorphism explicitly::

    sage: phi = gap('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,2), (1,2,3,4,5,6) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,3), (1,2)(3,4) ] )')
    sage: phi_star = HS6a.hom(phi,H0)
    sage: [H0.element_as_polynomial(phi_star(x)) for x in HS6a.gens()]
    [1: 0-Cocycle in H^*(D8; GF(2)),
     b_1_1^2+c_2_2: 2-Cocycle in H^*(D8; GF(2)),
     b_1_0: 1-Cocycle in H^*(D8; GF(2)),
     c_2_2*b_1_1: 3-Cocycle in H^*(D8; GF(2)),
     0: 3-Cocycle in H^*(D8; GF(2))]
    sage: singular(H0).set_ring()
    sage: singular(phi_star)
    s...[1]=b_1_1^2+c_2_2
    s...[2]=b_1_0
    s...[3]=c_2_2*b_1_1
    s...[4]=0

Here is the kernel of the induced map::

    sage: phi_star.preimage()
    c_3_2,
    c_1_0*b_3_3
    sage: phi_star(HS6a('c_3_2')).as_polynomial()
    '0'
    sage: phi_star(HS6a('c_1_0*b_3_3')).as_polynomial()
    '0'

Massey products
^^^^^^^^^^^^^^^

We can compute (set valued) higher Massey products and the (single
valued) restricted Massey powers introduced by [Kraines]_ for cocycles
of prime power groups. For non prime power groups, we have so far only
an experimental implementation for restricted Massey powers.

We first study some examples on ``H0`` (cohomology of the Dihedral Group
of order 8) that we have defined above. Note that we are transforming
the returned sets into sorted lists, in order
to have reproducible doc tests::

    sage: sorted(list(H0.massey_products(H0.2,H0.3,H0.2)))
    [0: 2-Cocycle in H^*(D8; GF(2)), b_1_0^2: 2-Cocycle in H^*(D8; GF(2))]
    sage: sorted(list(H0.massey_products(H0.2,H0.3,H0.2,H0.3)))
    [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
     b_1_1^2+c_2_2: 2-Cocycle in H^*(D8; GF(2)),
     b_1_0^2+c_2_2: 2-Cocycle in H^*(D8; GF(2)),
     b_1_1^2+b_1_0^2+c_2_2: 2-Cocycle in H^*(D8; GF(2))]
    sage: sorted(list(H0.massey_products(H0.2*H0.1,H0.3*H0.1,H0.2*H0.1)))
    [0: 8-Cocycle in H^*(D8; GF(2)),
     c_2_2^3*b_1_0^2: 8-Cocycle in H^*(D8; GF(2)),
     c_2_2^2*b_1_0^4: 8-Cocycle in H^*(D8; GF(2)),
     c_2_2^2*b_1_0^4+c_2_2^3*b_1_0^2: 8-Cocycle in H^*(D8; GF(2)),
     c_2_2*b_1_0^6: 8-Cocycle in H^*(D8; GF(2)),
     c_2_2*b_1_0^6+c_2_2^3*b_1_0^2: 8-Cocycle in H^*(D8; GF(2)),
     c_2_2*b_1_0^6+c_2_2^2*b_1_0^4: 8-Cocycle in H^*(D8; GF(2)),
     c_2_2*b_1_0^6+c_2_2^2*b_1_0^4+c_2_2^3*b_1_0^2: 8-Cocycle in H^*(D8; GF(2))]

If one is interested in just a single element of the Massey products,
one can use the option ``all=False``::

    sage: H0.massey_products(H0.2*H0.1,H0.3*H0.1,H0.2*H0.1,H0.3*H0.1, all=False)
    {c_2_2^5: 10-Cocycle in H^*(D8; GF(2))}

By the `i`-th restricted Massey power of a cocycle `C` in a cohomology
ring with coefficients `\mathbb F_p`, we mean the restricted
`p^i`-fold Massey product of `C` as introduced by D. Kraines. If it is
defined, then it is a single cocycle::

    sage: H = CohomologyRing(27,3)
    sage: H.make()
    sage: H.8
    a_3_4: 3-Cocycle in H^*(E27; GF(3))
    sage: H.8.massey_power()
    <a_3_4; 1>: 8-Cocycle in H^*(E27; GF(3))
    sage: H.element_as_polynomial(_)
    b_2_0^2*a_1_1*a_3_5+b_2_0^2*a_1_0*a_3_4+b_2_0*c_6_8: 8-Cocycle in H^*(E27; GF(3))

It is known that in odd degree and for `p>2` it can be expressed as
the negative of the composition of the first Steenrod power with the Bockstein
operator. This allows for a verification of the above result, see
:meth:`~pGroupCohomology.cochain.COCH.massey_power` for details.

Massey products allow to distinguish certain isomorphic cohomology
rings, so, they contain information that go beyond the ring
structure. An easy example is provided by the cohomology rings of the
cyclic groups of order 3 and order 9. The rings are isomorphic.
::

    sage: HC3 = CohomologyRing(3,1)
    sage: HC3.make()
    sage: HC9 = CohomologyRing(9,1)
    sage: HC9.make()
    sage: print(HC3)
    Cohomology ring of Small Group number 1 of order 3 with coefficients in GF(3)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_0: 2-Cocycle in H^*(SmallGroup(3,1); GF(3)),
     a_1_0: 1-Cocycle in H^*(SmallGroup(3,1); GF(3))]
    Minimal list of algebraic relations:
    []
    sage: print(HC9)
    Cohomology ring of Small Group number 1 of order 9 with coefficients in GF(3)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_0: 2-Cocycle in H^*(SmallGroup(9,1); GF(3)),
     a_1_0: 1-Cocycle in H^*(SmallGroup(9,1); GF(3))]
    Minimal list of algebraic relations:
    []

Note that the relation ``a_1_0^2`` is not listed, since the relation
`x^2=0` holds for any cocycle `x` of odd degree, for `p>2`, and is
thus somehow redundant. The 1st restricted Massey power of the degree
one generator is non-trivial for the cyclic group of order 3, but only
the 2nd restricted Massey power of the degree one generator of the
cohomology ring of the cyclic group of order 9 is non-trivial::

    sage: HC3.element_as_polynomial(HC3.2.massey_power())
    -c_2_0: 2-Cocycle in H^*(SmallGroup(3,1); GF(3))
    sage: HC9.element_as_polynomial(HC9.2.massey_power())
    0: 2-Cocycle in H^*(SmallGroup(9,1); GF(3))
    sage: HC9.element_as_polynomial(HC9.2.massey_power(2))
    -c_2_0: 2-Cocycle in H^*(SmallGroup(9,1); GF(3))

Bar Codes
^^^^^^^^^

Cohomology rings contain much information on a group. Unfortunately,
it is, in general, quite difficult to test whether two graded
commutative rings are isomorphic. Hence, it is of interest to consider
invariants that can be more easily compared, such as the Poincaré
series or the depth. Bar codes are not ring theoretic invariants,
but are defined in terms of the finite group whose cohomology is
being studied.

Any sequence of group homomorphisms `\phi_i: G_i \to G_{i+1}` with
`i=1,...,n` gives rise to a series of induced homomorphisms of
cohomology rings. Note that we insist that the sequence starts with
the group and ends with the trivial group. It is easy to get such
sequences in the case of prime power groups (e.g., upper central
series, derived series, `p`-central series). For non prime power
groups, this may be more difficult.

Persistent group cohomology, introduced in [EllisKing]_, asks how long
cocycles in a given degree "survive" being mapped by the induced
homomorphisms. In our paper, we observe a certain correspondence to
periodicity of coclass trees, and suggest that persistent group
homology may be an interesting theoretical tool. In addition, it can
be seen as an invariant of groups.

For a given degree `d`, the persistent cohomology can be described by
an upper triangular matrix of non-negative integers, where entry `i,j`
(`i\le j`) is the dimension of the image of the degree `d` part of
`H^*(G_j)` in `H^*(G_i)` under the induced homomorphism given by the
composition of `\phi_i,\phi_{i+1},...,\phi_{j-1}`, including the
case `i=j` in which the matrix entry simply gives the dimension of the
degree `d` part of `H^*(G_i)`.

As usual, the sequence of dimensions sorted by degree gives rise to a
Poincaré series. Hence, an upper triangular matrix of rational
functions results and this provides information for all degrees.

We like to emphasize that the persistence matrices are very easy to
compare and provide a quite strong tool for distinguishing groups.
While the cohomology ring only depends on the group algebra, the bar
codes may contain additional information on the group itself, by
taking into account the normal series. However, the following example
shows that bar codes contain information that even goes beyond the
isomorphism types of the normal subgroups and quotient groups.
::

    sage: H158 = CohomologyRing(64,158)
    sage: H160 = CohomologyRing(64,160)

These cohomology rings are part of our database, hence, they are
already completely known. The Poincaré series, the `a`-invariants, the
degrees of generators and of relations of the cohomology rings
coincide::

    sage: H158.poincare_series()
    (t^4 + t^3 + t^2 + t + 1)/(t^6 - 2*t^5 + 3*t^4 - 4*t^3 + 3*t^2 - 2*t + 1)
    sage: H160.poincare_series()
    (t^4 + t^3 + t^2 + t + 1)/(t^6 - 2*t^5 + 3*t^4 - 4*t^3 + 3*t^2 - 2*t + 1)
    sage: H158.degvec
    [4, 4, 1, 1, 1, 3, 3]
    sage: H160.degvec
    [4, 4, 1, 1, 1, 3, 3]
    sage: H158.set_ring()
    sage: [singular('deg(%s)'%r) for r in H158.rels()]
    [2, 2, 3, 3, 4, 4, 5, 6, 6, 6]
    sage: H160.set_ring()
    sage: [singular('deg(%s)'%r) for r in H160.rels()]
    [2, 2, 3, 3, 4, 4, 5, 6, 6, 6]
    sage: H158.a_invariants()
    [-Infinity, -Infinity, -2]
    sage: H160.a_invariants()
    [-Infinity, -Infinity, -2]

We consider here the bar codes associated with the upper central
series. It turns out that the non-trivial terms of the upper central
series and the resulting factor groups are isomorphic::

    sage: G158 = gap('SmallGroup(64,158)')
    sage: G160 = gap('SmallGroup(64,160)')
    sage: [(G.IdGroup(), (G158/G).IdGroup()) for G in G158.UpperCentralSeries()]
    [([ 64, 158 ], [ 1, 1 ]),
     ([ 16, 2 ], [ 4, 2 ]),
     ([ 4, 2 ], [ 16, 11 ]),
     ([ 1, 1 ], [ 64, 158 ])]
    sage: [(G.IdGroup(), (G160/G).IdGroup()) for G in G160.UpperCentralSeries()]
    [([ 64, 160 ], [ 1, 1 ]),
     ([ 16, 2 ], [ 4, 2 ]),
     ([ 4, 2 ], [ 16, 11 ]),
     ([ 1, 1 ], [ 64, 160 ])]

Nevertheless, the groups can be distinguished using the bar codes
associated with the upper central series::

    sage: B158 = H158.bar_code('UpperCentralSeries')
    sage: B160 = H160.bar_code('UpperCentralSeries')
    sage: B158 == B160
    False
    sage: B158[1]==B160[1]
    True
    sage: B158[2]==B160[2]
    True
    sage: B158[3]==B160[3]
    False


Indeed, the bar codes differ in degree 3; graphically::

    sage: ascii_art(B158[3])
            *
            *
          *-*
          *-*
          *
          *
          *
          *
          *
          *
        *-*
        *-*
        *
        *
      *
      *
      *
      *
    *
    *
    *
    *
    sage: ascii_art(B160[3])
            *
            *
          *-*
          *
          *
          *
          *
          *
          *
          *
        *-*-*
        *-*
        *
      *-*
      *
      *
      *
    *
    *
    *
    *

These pictures (bar codes) can be interpreted as follows. Let `G` be a
finite `p`-group and let `G=G_0 > G_1 > ... > G_n > 1` be a normal
series; in our example, we have `n=2`. The first `n+1` columns of the
bar code correspond to the normal subgroups groups `G_n, G_{n-1},...,
G_0`, while the last `n` columns correspond to the factor groups
`G/G_n, G/G_{n-1},..., G/G_1`. We consider the sequence of group
homomorphisms given by inclusions and quotients. The stars in the bar
code correspond to basis vectors of the degree `d` part of the
cohomology rings of the respective groups. Stars are connected by a
line (i.e., a hyphen) if the corresponding basis vectors are mapped to
each other by the induced maps (which of course go from right to
left).

In terms of the persistence matrix::

    sage: B158[3].matrix()
    [ 4  0  0  0  0]
    [ 0  4  0  0  0]
    [ 0  0  4  2  0]
    [ 0  0  0 10  2]
    [ 0  0  0  0  4]
    sage: B160[3].matrix()
    [ 4  0  0  0  0]
    [ 0  4  1  0  0]
    [ 0  0  4  2  1]
    [ 0  0  0 10  2]
    [ 0  0  0  0  4]

The bar codes in degree 3 can also be computed directly, and of course
the result coincides with the bar codes obtained from the "full" bar
codes (based on Poincaré series)::

    sage: B158[3] == H158.bar_code('UpperCentralSeries',degree=3)
    True
    sage: B160[3] == H160.bar_code('UpperCentralSeries',degree=3)
    True

Since apparently the ``(2,4)`` entries of the persistence matrices
differ, we show here how the Poincaré series in that position look
like::

    sage: B158.matrix()[2,4]
    2*t^2 + 2*t + 1
    sage: B160.matrix()[2,4]
    t^3 + 2*t^2 + 2*t + 1

Hence, the iamge of the map `H^*(G/G_2) \to H^*(G)` induced by the
quotient map contains only finitely many cocycles, where `G` is group
number 158 or 160 of order 64, and `G_2` is the second term of the
upper central series.

Essential and Depth Essential Ideals
------------------------------------

The essential ideal of a cohomology ring is formed by all those elements
whose restrictions to all subgroups vanish. The depth essential ideal
at rank `r` is formed by all those elements that vanish on the centralisers
of all `p`-elementary abelian subgroups of rank `r`. These ideals can be
computed using :meth:`~pGroupCohomology.cohomology.COHO.essential_ideal`
and :meth:`~pGroupCohomology.cohomology.COHO.depth_essential_ideal`.

If `r` is at most the depth of the cohomology ring, then the depth essential
ideal vanishes. It is conjectured by J. Carlson that it is non-zero whenever
`r` exceeds the depth.
::

    sage: D = CohomologyRing(8,3)
    sage: D.make()
    sage: Q = CohomologyRing(8,4)
    sage: Q.make()
    sage: SD = CohomologyRing(16,8)
    sage: SD.make()
    sage: S6 = CohomologyRing(720,763,prime=2)
    sage: S6.make()

The quaternion group is the smallest group that has a non-vanishing
essential ideal::

    sage: Q.essential_ideal()
    a_1_0^2,
    a_1_0*a_1_1

The dihedral group and the group of order 720 (which is
the symmetric group on 6 elements) have no essential
classes, for different reasons::

    sage: CohomologyRing.global_options('info')
    sage: S6.essential_ideal()
    H^*(SmallGroup(720,763); GF(2)):
              Compute essential_ideal
              The group is not of prime power order -- there is no essential ideal
    0
    sage: D.essential_ideal()
    H^*(D8; GF(2)):
              Compute essential_ideal
              The depth exceeds the Duflot bound -- there is no essential ideal
    0
    sage: CohomologyRing.global_options('warn')

It used to be a conjecture that the product of any two essential
classes vanishes. But then it was found that the cohomology of the
Sylow 2-subgroup of `U_3(4)`, which is of order 64, has exactly
one essential class that decomposes into essential classes of smaller
degrees. We verify this property::

    sage: H = CohomologyRing(64,245)
    sage: H
    H^*(Syl2(U3(4)); GF(2))
    sage: I = H.essential_ideal()    #long time
    sage: singular(H).set_ring()
    sage: (I*I).NF('std(0)').interred()  #long time
    a_4_8*a_6_8*a_1_0^3*a_1_3
    sage: singular('NF((a_4_8*a_6_8*a_1_0^3*a_1_3)^2, std(0))')
    0

Until recently, that was the only known counterexample to the
conjecture. However, using this package, it was found that the
cohomology ring of the direct product of the cyclic group of order two
and the Sylow 2-subgroup of `U_3(4)` has the same property.

Last, we illustrate Carlson's depth essential conjecture with some
group of order 64::

    sage: H = CohomologyRing(64,23)
    sage: H.CenterRk
    2
    sage: H.depth()
    3
    sage: H.dimension()
    4
    sage: H.depth_essential_ideal(2)
    0
    sage: H.depth_essential_ideal(3)
    0
    sage: H.depth_essential_ideal(4)
    a_1_0,
    a_1_1,
    a_2_0

Data storage and data relocation
--------------------------------

Modular cohomology rings of finite groups can be very complicated.
When computing the ring structure, many data pieces are
needed --- but not all pieces at the same time. Therefore we save the
various pieces in separate files, and reload them when they are
needed. In some examples, the memory and time consumption of saving
*all* data in a single file would not be reasonable. Hence, 'saving' a
cohomology ring to some file ``f`` means that ``f`` only contains the
information needed to find the files in which the various data pieces
are stored.

This method is fast, but has a clear disadvantage: If you wish to
transfer your cohomology computations to a different computer, it does
not suffice to copy one file for one cohomology ring. *All* data
pieces must be copied. Moreover, when the data are in a different
location, then the information stored in ``f`` would point to
non-existing paths. We tried to address these problems in the least
inconvenient way, as explained in the following sub-sections.

Data storage
^^^^^^^^^^^^

We first describe the situation for prime power groups. We do some new
computations from scratch, using a temporary directory.
::

    sage: from pGroupCohomology import CohomologyRing
    sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
    sage: tmp = tmp_dir()
    sage: CohomologyRing.set_workspace(tmp)
    sage: H = CohomologyRing(8,3,from_scratch=True)
    sage: H.make()

By default, when computing a cohomology ring ``H``, the result is
automatically saved in a file ``H.autosave_name()``. Cohomology rings
are unique parent structures, and therefore reloading from that file
only creates a new reference to ``H``::

    sage: K = load(H.autosave_name())
    sage: K is H
    True
    sage: loads(dumps(H)) is H
    True

By the command ``CohomologyRing.set_workspace(tmp)``, all data in the
user database are stored in sub-folders of the folder ``tmp``. The
names of these folders are composed as follows.

1. The basic folder ``tmp`` is known to ``H`` by the attribute
   ``root``.
   ::

       sage: os.path.realpath(H.root) == os.path.realpath(tmp)
       True

2. Any cohomology ring has been assigned a "stem name" that determines
   the names of sub-folders and file names associated with the ring.
   If the cohomology ring belongs to a group in the Small Groups Library,
   its stem name is formed using the address in the Small Groups Library.
   Otherwise, it is obtained from the group name used in the definition
   of the cohomology ring::

       sage: H = CohomologyRing(8,3)
       sage: G = gap('DihedralGroup(8)')
       sage: K = CohomologyRing(G, GroupName = 'DihedralA')
       sage: G.SetName('"DihedralB"')
       sage: L = CohomologyRing(G)
       sage: H.GStem
       '8gp3'
       sage: K.GStem
       'DihedralA'
       sage: L.GStem
       'DihedralB'

3. Data belonging to a cohomology ring can be found in a folder that is
   stored as the attribute "gps_folder", and is composed by the root and
   the stem name::

       sage: os.path.realpath(H.gps_folder) == os.path.realpath(os.path.join(H.root,H.GStem))
       True

The situation for non prime power groups is different. Here, the data
structure for the ring itself is somewhat easier, so, main data are
saved in just one file.  On the other hand, the computations rely on
the stable element method and thus involve the cohomology rings of
various subgroups. When reloading, these are sought in the cache or
in the workspace or local sources or remote sources, and are
re-computed if they can nowhere be found. Here, we show that the rings
are cached::

    sage: HS6a = CohomologyRing(720,763,prime=2)
    sage: HS6a.make()
    sage: HS6a is loads(dumps(HS6a))
    True
    sage: save(HS6a, HS6a.autosave_name())
    sage: HS6a is load(HS6a.autosave_name())
    True

Data relocation
^^^^^^^^^^^^^^^

If you wish to transfer data of a cohomology ring ``H`` to a different
location, you may do so. But please make sure that (in the case of prime power
groups) ``H.gps_folder`` keeps its name (only the parent directory is allowed
to change!), and that all files in ``H.gps_folder`` and its sub-folders are
preserved. Then, by :meth:`~pGroupCohomology.factory.CohomologyRingFactory.set_workspace`,
one can set up the workspace in the new location, and reload the ring.  In
order to demonstrate that it really is the same ring, we provide ``H`` with an
additional attribute before saving and moving the data::

    sage: H.setprop('info', 'The cohomology data were moved')
    sage: save(H,H.autosave_name())
    sage: tmp2 = tmp_dir()
    sage: import os
    sage: os.rename(tmp,tmp2)
    sage: CohomologyRing.set_workspace(tmp2)
    sage: M = CohomologyRing(8,3)
    sage: M is H
    False
    sage: print(M)
    Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
    <BLANKLINE>
    Computation complete
    Minimal list of generators:
    [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
     b_1_0: 1-Cocycle in H^*(D8; GF(2)),
     b_1_1: 1-Cocycle in H^*(D8; GF(2))]
    Minimal list of algebraic relations:
    [b_1_0*b_1_1]
    sage: M.info
    'The cohomology data were moved'

2. The Underlying Theory
========================

Let `R` be a graded algebra over a field `K`. An *approximation* of `R` is

- a sequence of graded commutative `K`-algebras `\tau_kR` presentable in
  degree at most `k` (for any positive integer `k`), together with
- a sequence of `K`-algebra homomorphisms `\alpha_k: \tau_kR\to R` for
  `k=1,2,...` whose restriction on degree `d` is an isomorphism of vector
  spaces, for any `d\le k`, and
- a `K`-algebra homomorphism `\lambda_k: \tau_kR\to \tau_{k+1}R` such that
  `\alpha_k= \alpha_{k+1}\circ \lambda_k, for `k=1,2,...`.

We refer to `\tau_kR` as an approximation of `R` out to degree `k`. Given a
minimal presentation of `R` as a graded `K` algebra, we obtain an
approximation of `R` out to degree `k` by the quotient of a free
graded-commutative algebra whose generators correspond to the generators of
`R` out to degree `k`, modulo the two-sided ideal generated by the relations
of `R` out to degree `k`.

Modular cohomology rings of finite groups are finitely presentable. Hence, for
all sufficiently large `k`, an approximation of the cohomology ring out to
degree `k` is actually isomorphic to the cohomology ring. The general scheme
of our computations of a cohomology ring is:

- Compute an approximation of the cohomology ring in increasing degree.
- Use a completeness criterion to detect whether the approximation is
  isomorphic to the cohomology ring.

Ring approximation in the case of prime power groups
----------------------------------------------------

Computing a minimal projective resolution
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

[Green]_ provides an algorithm for the computation of initial segments of a
minimal projective resolutions for modular group algebras of finite
`p`-groups, using non-commutative Groebner bases. He implemented it in
C-programs, and we provide a Cython wrapper in :mod:`pGroupCohomology.resolution`.

Chosing generators
^^^^^^^^^^^^^^^^^^

Knowing a resolution out to degree `d` allows for computing a minimal set of
cohomology generators out to degree `d` and a minimal set of algebraic
relations of degree up to `d` for these generators. It pays off to choose the
generators in a special way, by taking into account the restriction to certain
*special subgroups* `S_1,...,S_n`of `P`. Here, `S_1` denotes the greatest
central elementary abelian subgroup of `P`, and `S_2,...,S_n` denotes
representatives for the conjugacy classes of maximal elementary abelian
subgroups of `P`.

1. A cohomology class of `P` is nilpotent if and only if its
   restrictions to `S_2,...,S_n` are nilpotent. Since the cohomology
   rings of elementary abelian groups are either polynomial rings
   or the tensor product of a polynomial ring with an outer algebra
   (if `p` is odd), it is easy to test whether a cohomology class of `P`
   is nilpotent, even if the whole cohomology ring is not known yet.
   We choose as many as possible new nilpotent generators in degree `d`.
2. After step 1, continue with choosing as many as possible new
   generators in degree `d` with nilpotent restriction to `S_1`.
3. After step 2, include the remaining new generators in degree
   `d`. We call these *Duflot* generators, referring to [Duflot]_

If `z` is the rank of the centre of `P` then there are exactly `z` Duflot
generators, which was proved by [Kuhn]_, and they form a not necessarily
maximal regular sequence.  David Green introduced a monomial ordering on the
cohomology ring of `P` that, in the first place, depends on the degree of a
monomial, but also depends on the number of nilpotent respectively Duflot
regular generators occuring in the monomial. It turns out that this monomial
ordering magically simplifies many computations.

Note that the choice of generators and relations depends on how the group has
originally been defined.

Ring approximation in the case of non prime power groups
--------------------------------------------------------

The Stable Element Method
^^^^^^^^^^^^^^^^^^^^^^^^^

For the theoretical background of the Stable Element Method, we refer to
[AdemMilgram]_.  It is known that the mod-`p` cohomology ring of a finite
group `G` is a sub-ring of the mod-`p` cohomology of any subgroup `P` whose
index in `G` is co-prime to `p`. This sub-ring is formed by those cocycles of
`P` that are stable under conjugation by elements of `G`. That means, a
cocycle `c\in H^\ast(P; \mathbb F_p)` is stable if and only if for all `g\in
G` holds `r_{P, P\cap P^g}(c) = r_{P^g, P\cap P^g}(\phi_g(c))`, where `\phi_g`
denotes the homomorphism induced by conjugation with `g^{-1}`, and `r_{P,
P\cap P^g}, r_{P^g, P\cap P^g}` are restriction maps.

It suffices to test stability for representatives of all double cosets of `P`
in `G`. While this is, of course, much better than testing all elements of `G`,
the number of double cosets can still be rather large. It is thus often
better to compute the cohomology of `G` in two steps. By default, we proceed as
follows.

 - Let `S` be a Sylow `p`-subgroup of `G`. Compute its mod-`p` cohomology,
   ``HS``.
 - Let `N = N_G(Z(S))`. Compute its mod-`p` cohomology ``HN`` as a sub-ring
   of ``HS``.
 - If `N\not=G`: Compute the mod-`p` cohomology of `G` as a sub-ring of ``HN``.

The choice of generators
^^^^^^^^^^^^^^^^^^^^^^^^

This is mainly as in the case of prime power groups, with exception of the
Duflot generators. In the prime power case, we call a cohomology class
*Duflot*, if it has non-trivial restriction to the greatest central elementary
abelian subgroup. This makes sense, because this subgroup is non-trivial in
the prime power case. If `G` is a finite group that is not of prime power
order, we call a cohomology class *Duflot*, if it has non-trivial restriction
to the greatest central elementary abelian subgroup *of a Sylow `p`-subgroup*
`S` of `G`.

In particular, if the Sylow `p`-subgroup of `G` is elementary abelian, then
all elements in the mod-`p` cohomology ring of `G` are Duflot. Let `z` be the
rank of the greatest central elementary abelian subgroup of `S`. It is still
true that one can always find `z` Duflot elements in the mod-`p` cohomology
ring of `G` whose restrictions to the greatest central elementary abelian
subgroup of `S` forms a regular sequence, which means that these Duflot
elements form a regular sequence in the mod-`p` cohomology ring of `G`. We
refer to this as a *Duflot regular sequence*. However, it is not always
possible to choose generators so that a Duflot regular sequence can be found
among the generators.


Completeness Criteria
---------------------

Let `R=H^*(G;\mathbb F_p)`. We can compute ring approximation `\tau_k R` out
to arbitrary finite degree `k`. Since `R` has a finite presentation as an
`\mathbb F_p`-algebra, there remains to find a bound such that `\tau_k R` is
isomorphic to `R` for all `k` exceeding the bound.

In the case of an abelian group, it is known that a computation out to degree
2 will always suffice.  In the case of generalized quaternion groups, it is
known that a computation out to degree 4 will always suffice.

In all other cases, we need to use a *completeness criterion*. A completeness
criterion is an algorithmic procedure that can decide whether an approximation
of `R` out to degree `k` actually is isomorphic to `R`, as graded `\mathbb
F_p`-algebra. Such a criterion must be

- *effective* (there is some `N_0` such that the criterion asserts isomorphy
  of `\tau_kR` and `R` for all `k\ge N_0`) and

- *correct* (if `n_0` is the smallest number such that `\tau_{n_0}R` is
   isomorphic to `R`, then `N_0\ge n_0`)

For practical computations, it is important that `N_0-n_0` is small. And of
course, it is also important that the computations, which the completeness
criterion relies on, are not too difficult.

This spkg uses a criterion introduced by [Benson]_, improved by [GreenKing]_,
a criterion introduced by [Symonds]_, and a criterion introduced by [King]_
for finite groups that are not of prime power order.

Homogeneous systems of parameters
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

All three criteria require some knowledge of parameters of the mod-`p`
cohomology ring, `R`, of a finite group `G`. A finite sequence of homogeneous
elements `p_1,...,p_t` of `R` is called *homogeneous system of parameters* (or
hsop), if they generate a sub-algebra of `R` over which `R` is finite. In this
generality, we do not assume that the parameters are algebraically
independent.

A complication arises from the fact that we need to compute the parameters of
`R` in *approximations* of `R`. However, while computing the approximations in
increasing degrees, we can control the restrictions to the above-mentioned
maximal elementary abelian subgroups `S_2,...,S_n` of (a Sylow `p`-subgroup
of) `G`. If the cohomology of `S_2,...,S_n` is finite over the restrictions of
the elements `p_1,...,p_t` of some approximation of `R`, then these elements
give rise to a hsop of `R`.

For Benson's criterion, one needs to construct `p_1,...,p_t` such that they
form a filter-regular sequence in `R`. Filter-regular means that the
multiplication map by parameter number `k` on the quotient of `H^*(G)` modulo
the first `k-1` parameters has finite dimensional kernel. Since they are
parameters, the quotient of `H^*(G)` by all parameters is finite
dimensional. The parameters are used to compute the filter degree type of the
ring approximation, and if this succeeds, degree bound `N_0` is obtained
from the degree sum of the parameters.

In the modified Benson criterion, one still needs to construct `p_1,...,p_t`
such that they form a filter-regular sequence in `R`. But then, one can try to
show the existence of parameters in *smaller degrees* over a finite extension
field of `\mathbb F_p`. The degree bound `N_0` is obtained from the degree sum
of the *smaller* parameters, which do not require an explicit construction.

In the Symonds criterion, the parameters need to be constructed explicitly,
and the degree bound `N_0` is obtained from the degree sum of the
parameters. However, it is not needed that the parameters are algebraically
independent. This additional freedom often allows for a construction of
parameters in fairly small degrees.

In the next paragraphs, we explain how we construct (or show the existence of)
the parameters in the different flavours.

Filter regular parameters\---Dickson classes and the Benson criterion
.....................................................................

Let `G` be a finite group and `P` be a Sylow `p`-subgroup of `G`. Let `r` be
the `p`-rank of `P`, and let `z` be the rank of the centre of `P`. Using
Dickson invariants, we define `r-z` cohomology classes `d_{1,j},...,d_{r-z,j}`
of `S_j` (`j=2,...,n`) in the polynomial part of the cohomology ring of `S_j`,
restricting to zero on `S_1` (recall that `S_2,...S_n` are maximal elementary
abelian subgroups of `G`, and `S_1` is a common subgroup, namely the greatest
elementary abelian subgoup in the centre of `P`).

If `G=P` is a prime power group, [GreenKing]_ show that there exist cohomology
classes `D_1,...,D_{r-z}` of `G` such that `D_i` simultaneously restrict to
`d_{i,2},...,d_{i,n}` or to their `p^{k_i}`-th power for some
`k_1,...,k_{r-z}`.  We briefly refer to these classes as *restricted Dickson
classes* or *restricted Dickson elements* for `G` respectively for `S_j`.

If `G` is not of prime power order, then it may be that we won't find
restricted Dickson elements. If they exist, we can proceed as in the prime
power case: Based on [Benson]_, [GreenKing]_ show that a Duflot regular
sequence of `H^*(G)` together with the restricted Dickson classes for `G` form
a filter-regular homogeneous system of parameters (HSOP) for `H^*(G)`.

If the restricted Dickson elements do not exist, one can use the original
construction exposed in [Benson]_, which uses Dickson invariants in the
cohomology rings of `S_2,...S_n`, but *not* in a complement of `S_1`. These
unrestricted Dickson elements can be constructed in ring approximations, and
they are guaranteed to provided a filter regular hsop of the cohomology
ring. Note that unrestricted Dickson elements are of much higher degree than
restricted Dickson elements.

Given a filter-regular hsop, one is allowed to try and factorise the
parameters, possibly after modification by nilpotent elements. Let `D_i` be
the smallest resulting non-constant factors. [GreenKing]_ show that the result
is still a filter-regular hsop. And finally, the last parameter may be
replaced by any other parameter, since filter-regularity is automatic for the
last parameter. The motivation for all these refinements is to keep the
parameter degrees low.

From the dimensions of annihilators of the filter regular parameters, one can
compute the so-called *filter degree type*, which is a sequence of numbers
whose maximum gives a bound for the Castelnuovo\--Mumford regularity of the
ring approximation. The filter degree type together with the degrees of the
filter regular system of parameters and the rank of the centre of `P` give
rise to a degree bound of [Benson]_:

**Theorem 1**

  Let `G` be a finite group. Assume that `R_n` is an approximation of
  `H^\ast(G;\mathbb F_p)` out to degree `n` and assume that there is
  a filter regular hsop for `R_n` in degrees at least two that gives
  rise to a filter regular hsop of `H^\ast(G;\mathbb F_p)`. Let
  `f_0,...,f_r` be the filter degree type and let `d_1,...,d_r` be the
  degrees of the filter regular hsop. If

    `n > \max(0, f_0+0,  f_1+1,...,f_{r-1}+r-1) - r + d_1+ ... +d_r`

  then `R_n` is isomorphic to the cohomology ring.

  If the depth of `H^\ast(G;\mathbb F_p)` is at least two, then the preceding
  statement holds with `n \ge ...` instead of `n > ...`. This is the case,
  e.g., if the centre of a Sylow `p`-subgroup `P` of `G` has `p`-rank at least
  two, or if there is a subgroup `P<U<G` such that `H^\ast(U;\mathbb F_p)` has
  depth at least two.

Benson conjectures that the filter degree type for any modular cohomology ring
of a finite p-group is of the form `-1,-2,...,-r,-r`. [Symonds]_ has shown
that the regularity of a modular cohomology ring is zero. But of course
neither of these statements is guaranteed to hold for an incomplete
approximation of a cohomology ring. That's why it is needed to compute the
filter degree type in Benson's criterion. This can be a very difficult task.

According to [GreenKing]_, it suffices to have one filter regular hsop of the
ring approximation that gives rise to a hsop of the cohomology ring, and to
prove the existence of a filter regular hsop of smaller degrees by changing
the coefficients to a finite extension field\---then, one can use Benson's
criterion using the degrees of the smaller hsop. The underlying result for an
existence proof is this:

**Lemma 2** [GreenKing]_

  Let `R=H^\ast(G;\mathbb F_p)`. Assume that `p_1,...,p_r` is a filter-regular
  hsop of `R`. If there is `1\le i< r` and some integer `d` such that `R`
  modulo the two-sided ideal generated by `p_1,...,p_i` together with the
  degree-`d` part of `R` is a finite dimensional algebra, then there is some
  finite field extension `K` of `\mathbb F_p` such that `H^\ast(G; K)` has a
  filter-regular hsop formed by elements in degrees `|p_1|, ..., |p_i|`
  together with `r-i` elements of degree `d`.

Since the filter degree type is independent of the choice of a filter-regular
system of parameters, we can use the Dickson classes for computing the
filter-degree type. Then, we prove the existence of a filter regular hsop in
smaller degrees. We do not need this hsop explicitly\---we only need the
degrees (which comes out of the existence proof) and the filter-degree type
(which can be computed using the Dickson classes).

Arbitrary parameters\---The Symonds Criterion
.............................................

**Theorem 3** [Symonds]_

  Let `R_n` be the approximation of `H^\ast(G;\mathbb F_p)` out to
  degree `n`. Assume that there is a hsop for `R_n` in degrees
  `d_1,...,d_r` that gives rise to a hsop of `H^\ast(G;\mathbb
  F_p)`. Let `N` be the maximal degree of generators of `R_n` as a
  module over the parameters. If

    `n \ge \max(N, d_1+ ... +d_r - r +1)`

  then `R_n` is isomorphic to the cohomology ring.

In order to compute the maximal degree `N` of module generators over the
parametes, it is needed to explicitly know the parameters. Hence, in contrast
to the Benson criterion, it seems impossible to improve the Symonds criterion
by an existence result for small parameters over an extension field.

However, for verifying the Symonds criterion, it is not needed to compute the
filter degree type of the hsop. Actually, it is not even needed to have
algebraically independent parameters: It suffices to have elements that
generate an ideal of Krull dimension zero.

We use two methods to compute a suitable hsop:

1. Start with a filter-regular hsop. Then try to replace each of the given
   parameters by an element of smaller degree, in a ring approximation. The
   restrictions to maximal `p`-elemenentary abelian subgroups allow to verify
   whether the result gives still rise to parameters of the cohomology ring
   (but not necessarily of the current ring approximation!).

   Since filter-regular hsops are algebraically independent, the result of the
   replacements is still an algebraically independent hsop, though not
   necessarily filter-regular.

2. By considering the restrictions to maximal `p`-elementary abelian
   subgroups, find a minimal subset of the set of generators of the current
   ring approximation that forms a hsop of the cohomology ring. Actually, one
   is free to add all generators of degree 1, since degree 1 parameters do not
   contribute to the degree bound in Symonds' result.

   The resulting hsop is, of course, in general not even algebraically independent.

We are free to choose the hsop that gives the best degree bound in the Symonds
criterion.

Arbitrary parameters over a field extension\---The Hilbert\--Poincaré criterion
...............................................................................

Given an arbitrary hsop (for example, the one obtained by the first method
explained in the previous paragraph), one can apply an existence result for
parameters over a finite field extension, similar to the one used for the
modified Benson criterion:

**Lemma 4** [King]_

  Let `R=H^\ast(G;\mathbb F_p)` and let `Q` be a hsop of `R`. Let `S\subset
  Q`, and let `d` be some integer such that `R` modulo the two-sided ideal
  generated by the elements of `S` together with the degree-`d` part of `R` is
  a finite dimensional algebra. Let `r` be the `p`-rank of `G` (which is equal
  to the Krull dimension of `R`), and let `r'` be the Krull dimension of `R`
  modulo the ideal generated by `S`. Then there is some finite field extension
  `K` of `\mathbb F_p` such that `H^\ast(G; K)` has a filter-regular hsop
  formed by elements in degrees `|q|` for all `q\in S`, together with `r-r'`
  elements of degree `d`.

The difference to the existence result used for the modified Benson criterion
is that the subset `S` is not necessarily formed by an initial segment of `Q`,
which gives more possibilities to find parameters in small degrees. The
resulting hsop over some field extension is *not* guaranteed to be
filter-regular, if `S` is not an initial segment of the hsop.

Provided that all generators of the cohomology ring have already been found,
one can then deduce completeness of the current ring approximation, by
studying its Hilbert\--Poincaré series. The following result arose in a
discussion of Simon King with Peter Symonds.

**Theorem 5** [King]_

  Let `R=H^\ast(G;\mathbb F_p)` and let `\alpha_n: \tau_nR\to R` be a ring
  approximation out to degree `n`. Assume that `\alpha_n` is known to be
  surjective. Let `d` be a lower bound for the depth of `R`. Assume that there
  is some finite field extension `K` of `\mathbb F_p` such that `H^\ast(G; K)`
  has a hsop formed by elements of degree `d_1,...,d_r`. Denote `N =
  \left(\sum_{i=1}^rd_i \right) - d`, and assume `n\ge N`. Let `f_n\in \mathbb Z[t]` be the
  Hilbert\--Poincaré series of `\tau_nR`.

  Then, `\alpha_n` is an isomorphism if and only if `f_n\cdot \prod_{i=1}^r
  (1-t^{d_i})` is a polynomial of degree at most `N`.

Proving surjectivity of a ring approximation in the non prime power case
........................................................................

For applying the previous Theorem, there remains the problem of finding a
lower bound for the depth, and the problem of deciding whether `\alpha_n` is
surjective. Here, we need to restrict to the case that `G` is a finite group
that is not of prime power order. Actually, the criterion is designed for
being used in the context of the stable element method explained earlier.

Let `U<G` be a subgroup whose index in `G` is co-prime to `p`. Recall that the
stable element method describes `R=H^\ast(G;\mathbb F_p)` as a sub-algebra of
`H^\ast(U;\mathbb F_p)`, where we assume that the latter cohomology ring has
already been computed. In particular, we can compute the depth of
`H^\ast(U;\mathbb F_p)`, which is a lower bound for the depth of `R` used in
the Theorem above.

Surjectivity of the ring approximation can be proved using the following
result.

**Theorem 6** [King]_

  Let `R=H^\ast(G;\mathbb F_p)`, let `\alpha_n: \tau_nR\to R` be a ring
  approximation out to degree `n`, denote `R_U=H^\ast(U;\mathbb F_p)`, and let
  `\iota: R\to R_U` be the inclusion used in the stable element method.

  If `n` is sufficiently large, then `R_U` is finite over
  `A_n=\iota\left(\alpha_n(\tau_nR)\right)`. If `R_U` is generated in degree
  at most `D` as an `A_n` module, and if `n\ge D`, then `\alpha_n` is
  surjective.

There are many examples in which the Symonds criterion detects completeness of
the cohomology ring approximation in lower degrees than the Hilbert\--Poincaré
criterion. This can be the case, if `D` is small. But even in that case, the
preceding Theorem is extremely useful to speed up the stable element
method. Namely, if surjectivity of the ring approximation is known, then all
stable elements of `R_U` are decomposable in terms of the generators that have
already been found. Hence, there is no need to solve large systems of
equations for computing the space of stable elements in higher degree. This
often saves a considerable amount of resources.

Comparison of the Criteria
--------------------------

If there is a nilpotent generator in degree `d`, then there will be a relation
at least in degree `2d`. If there are generators in degrees `d_1` and `d_2`
that are neither nilpotent nor Duflot (such generators are called *boring*),
then there will be a relation at least in degree `d_1+d_2`. Hence, before
attempting to prove completeness of a cohomology ring approximation by a
computationally expensive criterion, we consider the previously found
generators and compute out to the degree in which we expect the last
relations, before we attempt any of the completeness criteria.

When this degree is attained, we first try the Symonds criterion (both for
prime power and finite non prime power groups). The Symonds criterion requires
the explicit construction of a hsop for the cohomology ring, but it does not
require algebraic independence. This gives some freedom in the choice of
parameters, and very often one gets a very good degree bound. Moreover, the
criterion is very easy to use\---one only needs to find out in what degree the
ring approximation is generated as a module over the sub-algebra generated by
the chosen parameters.

If the Symonds criterion detects completeness, the computation can be
finished. If it detects that the ring approximation is incomplete (this is the
case, if the hsop of the cohomology ring is not a hsop of the ring
approximation), then we continue the computation, until the next generator or
relation is found.

If the Symonds criterion is inconclusive (this is the case, if the degrees of
the explicitly constructed hsop are too large to detect completeness of the
current ring approximation), then we try a different criterion, namely the
modified Benson criterion in the case of a prime power group, or the
Hilbert\--Poincaré criterion for finite groups that are not of prime power
order. This may be successful, if the existence result for small degree
parameters over an extension field succeeds.

3. A step-by-step example
=========================

The purpose of this section is to illustrate the theoretical results
formulated in the previous section. In our example, we compute the mod-2
cohomology ring of the symmetric group of rank 8. Normally, this would be done
by defining ``G = gap.SymmetricGroup(8)`` and ``H = CohomologyRing(G,
GroupName="S8", prime = 2)``, simply followed by ``H.make()``. But here, we
show what is happening behind the scenes.

The Sylow subgroup
------------------

We want to test this example as if it was in a new Sage session and therefore
restart GAP and Singular and create a new temporary folder for storing
cohomology data::

    sage: gap.quit()
    sage: singular.quit()

Since we are using the stable element method, we first need to get the
cohomology ring of a Sylow 2-subgroup. It is of order 128::

    sage: G = gap.SymmetricGroup(8)
    sage: G.SylowSubgroup(2).IdGroup()
    [ 128, 928 ]

We set up the computation of its cohomology ring (requesting a computation
from scratch in a new temporary directory)::

    sage: from pGroupCohomology import CohomologyRing
    sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
    sage: HSyl = CohomologyRing(128, 928, from_scratch=True)

Note that the program has a list of names of interesting groups, and so group
number 928 of order 128 in the Small Groups library is correctly identified as
the Sylow 2-subgroup of the symmetric group of rank 8::

    sage: HSyl
    H^*(Syl2(S8); GF(2))

At this point, the ring structure is not computed, but only the basic setup is
present: The lowest term of a minimal projective resolution, together with the
restriction maps on the special subgroups. The cohomology rings of the special
subgroups have been computed while setting up ``HSyl``. ::

    sage: print(HSyl)
    <BLANKLINE>
    Cohomology ring of Sylow 2-subgroup of Symmetric Group S_8 with coefficients in GF(2)
    <BLANKLINE>
    Computed up to degree 0
    Minimal list of generators:
    []
    Minimal list of algebraic relations:
    []
    <BLANKLINE>
    sage: Res = HSyl.resolution(); Res
    Resolution of GF(2)[Syl2(S8)]
    sage: sorted(HSyl.restriction_maps().items())
    [(1,
      [(2, 1),
       Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(2,1); GF(2))]),
     (2,
      [(8, 5),
       Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(8,5); GF(2))]),
     (3,
      [(8, 5),
       Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(8,5); GF(2))]),
     (4,
      [(16, 14),
       Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(16,14); GF(2))]),
     (5,
      [(16, 14),
       Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(16,14); GF(2))]),
     (6,
      [(16, 14),
       Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(16,14); GF(2))])]
    sage: sorted(HSyl.subgroups().items())
    [((2, 1), H^*(SmallGroup(2,1); GF(2))),
     ((8, 5), H^*(SmallGroup(8,5); GF(2))),
     ((16, 14), H^*(SmallGroup(16,14); GF(2)))]

As we can see, the Sylow 2-subgroup of ``G`` contains 2 conjugacy classes of
maximal elementary abelian subgroups of order 8 and three conjugacy classes of
maximal elementary abelian subgroups of order 16. The maximal central
elementary abelian subgroup has order 2.

We could explicitly request the computation of higher terms of the resolution,
::

    sage: Res.nextDiff()
    sage: print(Res)
    Resolution:
    0 <- GF(2) <- GF(2)[Syl2(S8)] <- rank 3

but this is done anyway when we compute an approximation of the cohomology
ring in increasing degrees. We compute the ring out to degree 3 (which could
also be achieved by ``HSyl.make(3)``)::

    sage: HSyl.next()
    sage: HSyl.next()
    sage: HSyl.next()
    sage: print(Res)
    Resolution:
    0 <- GF(2) <- GF(2)[Syl2(S8)] <- rank 3 <- rank 7 <- rank 13 <- rank 22
    sage: print(HSyl)
    <BLANKLINE>
    Cohomology ring of Sylow 2-subgroup of Symmetric Group S_8 with coefficients in GF(2)
    <BLANKLINE>
    Computed up to degree 3
    Minimal list of generators:
    [b_2_4: 2-Cocycle in H^*(Syl2(S8); GF(2)),
     b_2_5: 2-Cocycle in H^*(Syl2(S8); GF(2)),
     b_2_6: 2-Cocycle in H^*(Syl2(S8); GF(2)),
     b_1_0: 1-Cocycle in H^*(Syl2(S8); GF(2)),
     b_1_1: 1-Cocycle in H^*(Syl2(S8); GF(2)),
     b_1_2: 1-Cocycle in H^*(Syl2(S8); GF(2)),
     b_3_11: 3-Cocycle in H^*(Syl2(S8); GF(2)),
     b_3_12: 3-Cocycle in H^*(Syl2(S8); GF(2))]
    Minimal list of algebraic relations:
    [b_1_0*b_1_1,
     b_1_0*b_1_2,
     b_2_4*b_1_2,
     b_2_5*b_1_1,
     b_2_6*b_1_0]
    <BLANKLINE>

There is a convention for the names of the cohomology ring generators: If the
name starts with the letter "a", then it is nilpotent. If it starts with the
letter "c", then it is Duflot. Otherwise, it starts with the letter
"b". Hence, all 8 generators found in degree at most 3 are not Duflot and not
nilpotent. In other words, they have trivial restriction to the central
elementary abelian subgroup, but non-trivial restriction to at least one
maximal elementary abelian subgroup. Let us verify this for two of the
generators. There are different methods to get the restrictions. First, we
call the restriction map to the greatest central elementary abelian subgroup
on some degree two generator.
::

    sage: HSyl.1
    b_2_4: 2-Cocycle in H^*(Syl2(S8); GF(2))
    sage: HSyl.restriction_maps()[1][1]
    Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(2,1); GF(2))
    sage: HSyl.restriction_maps()[1][1](HSyl.1)
    (b_2_4)_: 2-Cocycle in H^*(SmallGroup(2,1); GF(2))

The name of the image is obtained from the name of the preimage. We can verify
that the image indeed vanishes::

    sage: HSyl.restriction_maps()[1][1](HSyl.1).is_zero()
    True

There is a convenient method that computes the restriction of all generators
of the current ring approximation to the `n`-th special subgroup and expresses
the images in terms of the cohomology ring generators of the subgroup. So, we
can easily see that all generators restrict to zero on the greatest central
elementary abelian subgroup::

    sage: HSyl.restrict_to_subgroup(1)
    [0: 2-Cocycle in H^*(SmallGroup(2,1); GF(2)),
     0: 2-Cocycle in H^*(SmallGroup(2,1); GF(2)),
     0: 2-Cocycle in H^*(SmallGroup(2,1); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(2,1); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(2,1); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(2,1); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(2,1); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(2,1); GF(2))]

We verify that each generator has non-trivial restriction to at least one
maximal elementary abelian subgroup and is thus not nilpotent::

    sage: HSyl.restrict_to_subgroup(2)
    [c_1_1*c_1_2: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     c_1_2+c_1_1: 1-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(8,5); GF(2))]
    sage: HSyl.restrict_to_subgroup(3)
    [0: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     c_1_1*c_1_2: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     c_1_2+c_1_1: 1-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(8,5); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(8,5); GF(2))]
    sage: HSyl.restrict_to_subgroup(4)
    [0: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_3^2+c_1_2*c_1_3: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_1*c_1_3+c_1_1*c_1_2+c_1_1^2+c_1_0*c_1_2: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_2: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_1*c_1_3^2+c_1_1*c_1_2^2+c_1_1^2*c_1_3+c_1_1^2*c_1_2+c_1_0*c_1_2^2+c_1_0^2*c_1_2: 3-Cocycle in H^*(SmallGroup(16,14); GF(2))]
    sage: HSyl.restrict_to_subgroup(5)
    [0: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_1*c_1_2+c_1_1^2+c_1_0*c_1_3+c_1_0*c_1_2: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_3: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_2: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_1*c_1_2*c_1_3+c_1_1^2*c_1_3+c_1_0*c_1_2*c_1_3+c_1_0^2*c_1_3: 3-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_1*c_1_2^2+c_1_1^2*c_1_2+c_1_0*c_1_2^2+c_1_0^2*c_1_2: 3-Cocycle in H^*(SmallGroup(16,14); GF(2))]
    sage: HSyl.restrict_to_subgroup(6)
    [c_1_3^2+c_1_2*c_1_3: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_1*c_1_3+c_1_1^2+c_1_0*c_1_2: 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_2: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     c_1_1*c_1_3^2+c_1_1*c_1_2*c_1_3+c_1_1^2*c_1_3+c_1_1^2*c_1_2+c_1_0^2*c_1_2: 3-Cocycle in H^*(SmallGroup(16,14); GF(2)),
     0: 3-Cocycle in H^*(SmallGroup(16,14); GF(2))]

Parameters
^^^^^^^^^^

Note that none of the generators is Duflot. Hence, the current ring
approximation does not contain parameters for the cohomology ring and is thus
incomplete::

    sage: print(HSyl.parameters())
    None

In the next degree, we finally find a Duflot generator (there is only one,
since the greatest central elementary abelian subgroup is of rank one)::

    sage: HSyl.next()
    sage: HSyl.duflot_regular_sequence()
    ['c_4_21']

However, the program did not bother to try and compute parameters yet::

    sage: HSyl.filter_regular_parameters()
    sage: HSyl.parameters()

The first reason is that we expect a relation in degree six::

    sage: HSyl.expect_last_relation()
    6

The second reason is that the `p`-rank of this group (which is equal to the
dimension of the cohomology ring) is four and the rank of the centre is one,
which means that the restricted Dickson elements are of degrees 4, 6 and 7 and
are thus found in higher degrees than the current ring approximation. The
default method of finding restricted Dickson elements uses linear algebra and
only works in those degrees that already are available::

    sage: HSyl.Dickson
    ['b_1_2*b_3_12+b_1_2^4+b_1_1*b_3_11+b_1_1^2*b_1_2^2+b_1_1^4+b_1_0^4+b_2_6*b_1_2^2+b_2_6*b_1_1*b_1_2+b_2_6^2+b_2_5^2+b_2_4^2',
     None,
     None]

Note that the unrestricted Dickson elements originally considered by [Benson]_
are of much higher degrees, namely 8, 12, 14 and 15. In any case, it is
possible to try to compute the restricted Dickson elements by a method
involving elimination. This is potentially very expensive and is here not done
by default. Let's call this method::

    sage: HSyl.find_dickson()
    True
    sage: HSyl.Dickson
    ['b_1_2*b_3_12+b_1_2^4+b_1_1*b_3_11+b_1_1^2*b_1_2^2+b_1_1^4+b_1_0^4+b_2_6*b_1_2^2+b_2_6*b_1_1*b_1_2+b_2_6^2+b_2_5^2+b_2_4^2',
     'b_3_12^2+b_1_2^3*b_3_12+b_1_1*b_1_2^2*b_3_12+b_1_1^2*b_1_2^4+b_1_1^3*b_3_12+b_1_1^3*b_3_11+b_1_1^4*b_1_2^2+b_2_6*b_1_2*b_3_12+b_2_6*b_1_2^4+b_2_6*b_1_1^3*b_1_2+b_2_6^2*b_1_2^2+b_2_6^2*b_1_1*b_1_2+b_2_6^2*b_1_1^2+b_2_5*b_1_2*b_3_12+b_2_5*b_2_6*b_1_2^2+b_2_5^2*b_1_2^2+b_2_5^2*b_1_0^2+b_2_4*b_1_1*b_3_11+b_2_4*b_2_6^2+b_2_4^2*b_1_1^2+b_2_4^2*b_1_0^2+c_4_21*b_1_2^2',
     'b_1_2*b_3_12^2+b_1_1*b_1_2^3*b_3_12+b_1_1^2*b_1_2^2*b_3_12+b_1_1^3*b_1_2*b_3_12+b_1_1^4*b_3_12+b_2_6*b_1_2^2*b_3_12+b_2_6*b_1_1*b_1_2^4+b_2_6*b_1_1^3*b_1_2^2+b_2_6^2*b_1_1*b_1_2^2+b_2_6^2*b_1_1^2*b_1_2+b_2_5*b_1_2^2*b_3_12+b_2_5*b_2_6*b_1_2^3+b_2_4*b_1_1^2*b_3_11+b_2_4*b_2_6^2*b_1_1+c_4_21*b_1_2^3']

Together with the Duflot generator, we obtain a filter regular hsop. We find
that we could replace the last Dickson element by a parameter in degree one
(the resulting hsop would still be filter-regular)::

    sage: HSyl.find_small_last_parameter(HSyl.duflot_regular_sequence()+HSyl.Dickson)
    'b_1_2+b_1_1'

Of course, there is no need to do the preceding computation explicitly, as it
is done internally anyway when computing a filter-regular hsop::

    sage: HSyl.filter_regular_parameters()
    ['c_4_21',
     'b_1_2*b_3_12+b_1_2^4+b_1_1*b_3_11+b_1_1^2*b_1_2^2+b_1_1^4+b_1_0^4+b_2_6*b_1_2^2+b_2_6*b_1_1*b_1_2+b_2_6^2+b_2_5^2+b_2_4^2',
     'b_3_12^2+b_1_2^3*b_3_12+b_1_1*b_1_2^2*b_3_12+b_1_1^2*b_1_2^4+b_1_1^3*b_3_12+b_1_1^3*b_3_11+b_1_1^4*b_1_2^2+b_2_6*b_1_2*b_3_12+b_2_6*b_1_2^4+b_2_6*b_1_1^3*b_1_2+b_2_6^2*b_1_2^2+b_2_6^2*b_1_1*b_1_2+b_2_6^2*b_1_1^2+b_2_5*b_1_2*b_3_12+b_2_5*b_2_6*b_1_2^2+b_2_5^2*b_1_2^2+b_2_5^2*b_1_0^2+b_2_4*b_1_1*b_3_11+b_2_4*b_2_6^2+b_2_4^2*b_1_1^2+b_2_4^2*b_1_0^2+c_4_21*b_1_2^2',
     'b_1_2+b_1_1']

We can also replace other parameters of this filter-regular hsop by elements
of smaller degree. The result is an algebraically independent hsop, but there
is no guarantee that it is filter-regular::

    sage: HSyl.parameters()
    ['c_4_21',
     'b_1_1^2+b_1_0^2+b_2_6+b_2_5+b_2_4',
     'b_1_0^2+b_2_6',
     'b_1_2+b_1_1']

When we try to find a subset of the generators of the current ring
approximation that is a hsop of the cohomology ring, we obtain::

    sage: HSyl.dependent_parameters()
    ['b_1_0', 'b_1_1', 'b_1_2', 'c_4_21', 'b_2_4', 'b_2_5', 'b_2_6']

All these hsops are for the cohomology ring, but they are no hsops for the
current ring approximation::

    sage: HSyl.set_ring()
    sage: I = HSyl.relation_ideal()
    sage: singular.eval('degBound=0')
    ''
    sage: (I + singular.ideal(HSyl.filter_regular_parameters())).std().dim()
    2
    sage: (I + singular.ideal(HSyl.parameters())).std().dim()
    2
    sage: (I + singular.ideal(HSyl.dependent_parameters())).std().dim()
    2

But this is no surprise, since the current ring approximation is up to degree
4, but we expect a relation in degree six. So, let us compute two degrees
further::

    sage: HSyl.next()
    sage: HSyl.next()

Now, the cohomology parameters are parameters for the ring approximation,
too::

    sage: HSyl.set_ring()
    sage: singular.eval('degBound=0')
    ''
    sage: I = HSyl.relation_ideal()
    sage: (I + singular.ideal(HSyl.filter_regular_parameters())).std().dim()
    0
    sage: (I + singular.ideal(HSyl.parameters())).std().dim()
    0
    sage: (I + singular.ideal(HSyl.dependent_parameters())).std().dim()
    0

Completion tests
^^^^^^^^^^^^^^^^

In what degrees would it make sense to try the Symonds criterion? We found
algebraically independent parameters in degrees 4, 2, 3, 1, and we found
dependent parameters in degrees 1, 1, 1, 4, 2, 2, 2, which means that the
Symonds criterion can only apply in degree strictly greater than `3+1+2+0=6`
or strictly greater than `0+0+0+3+1+1+1=6`. Hence, it does not apply yet.

What about the modified Benson criterion? It turns out that we can not prove
the existence of smaller parameters over a finite extension field, so, we have
to work with the explicitly computed filter-regular hsop in degrees 4, 2, 3, 1
(the last parameter needs to be squared, because the parameter degrees must be
at least two for Benson's criterion). The `p`-rank of the centre of our Sylow
2-subgroup is one, which means that we only get 1 as lower bound for the depth
of the cohomology ring. Hence, the Benson criterion can only apply in degree
strictly greater than `3+1+2+1=7`. Note, however, that the filter degree type
(which is stored as an attribute) already is as expected::

    sage: HSyl.raw_filter_degree_type(HSyl.filter_regular_parameters())
    ([-1, -1, -1, 10, 11],
     [[0], [0], [0], [0, 1, 1, 3, 3, 4, 4, 3, 3, 1, 1], [1, 2, 5, 7, 10, 11, 11, 10, 7, 5, 2, 1]],
     [4, 4, 6, 1])
    sage: HSyl.fdt
    [-1, -2, -3, -4, -4]

However, we need to compute the ring approximation out to degree 7 (not
finding any new generator or relation), before we succeed with proving
completeness with the Symonds criterion.
::

    sage: HSyl.next()
    sage: HSyl.last_interesting_degree()
    6
    sage: HSyl.test_for_completion()
    True
    sage: HSyl._method
    'Symonds'

Indeed, the ring approximation can be generated in degree `3\le7` as a module
over one of the previously obtained hsops::

    sage: HSyl._max_module_deg
    3
    sage: HSyl.set_ring()
    sage: singular.eval('degBound=0')
    ''
    sage: I = HSyl.relation_ideal()
    sage: HSyl._parameters_for_criterion
    ['b_1_0', 'b_1_1', 'b_1_2', 'c_4_21', 'b_2_4', 'b_2_5', 'b_2_6']
    sage: (I + singular.ideal(HSyl._parameters_for_criterion)).std().kbase()
    b_3_12,
    b_3_11,
    1

An intermediate subgroup
------------------------

Often it is easier to not directly apply the stable element method to a Sylow
subgroup, but first compute the cohomology of an intermediate group between
`G` and its Sylow subgroup. By default, we use the normaliser in `G` of the
centre of the Sylow subgroup of `G`::

    sage: G.Normalizer(G.SylowSubgroup(2).Centre()).IdGroup()
    [ 384, 5602 ]

So, we create the basic setup of its cohomology ring::

    sage: HU = CohomologyRing(384, 5602, prime=2)

Stable elements
^^^^^^^^^^^^^^^

The stable element method for this intermediate subgroup works on the Sylow
subgroup. We find that one stability condition is enough. The stability
conditions are expressed in terms of a two maps that either restrict directly
from the Sylow subgroup to its intersection with a conjugate, or restrict
after twisting with the map that is induced by conjugation::

    sage: HU.sylow_cohomology() is HSyl
    True
    sage: HU._PtoPcapCPdirect
    [Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(64,138); GF(2))]
    sage: HU._PtoPcapCPtwist
    [Induced homomorphism of degree 0 from H^*(Syl2(S8); GF(2)) to H^*(SmallGroup(64,138); GF(2))]

Let us compute subspace of stable elements of degree one in the cohomology
ring of the Sylow subgroup::

    sage: HU.stable_space(1)
    ([Gen2: 1-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
      Gen1: 1-Cocycle in H^*(SmallGroup(384,5602); GF(2))],
     ['b_1_2', 'b_1_1', 'b_1_0'],
     ['b_1_2', 'b_1_1'])

This means: The cohomology of our intermediate subgroup has two generators in
degree one, whose restrictions to the Sylow subgroup have leading monomials
``b_1_2`` or ``b_1_1``, and apart from this the cohomology of the Sylow
subgroup has another degree one monomial ``b_1_0`` that does not occur as
leading monomial of a stable element. Of course, there are no relations in
degree one. So, in degree one, we obtain::

    sage: HU.next()
    sage: HU.gens()
    [1,
     b_1_0: 1-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
     b_1_1: 1-Cocycle in H^*(SmallGroup(384,5602); GF(2))]

We find that the stable subspace in degree two is of dimension 5. The
decomposable elements form a sub-space of dimension 3 (that is the first
output of :meth:`~pGroupCohomology.modular_cohomology.MODCOHO.find_relations`),
and there are no relations in degree two (that is the second output)::

    sage: HU.stable_space(2)
    ([Gen5: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
      Gen4: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
      Gen3: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
      Gen2: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
      Gen1: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2))],
     ['b_1_2^2', 'b_1_1*b_1_2', 'b_1_1^2', 'b_1_0^2', 'b_2_6', 'b_2_5', 'b_2_4'],
     ['b_1_2^2', 'b_1_1*b_1_2', 'b_1_1^2', 'b_1_0^2', 'b_2_6'])
    sage: HU.find_relations(2)
    ([b_1_1^2: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
      b_1_0*b_1_1: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
      b_1_0^2: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2))],
     [])

Hence, we find two cohomology generators in degree two, and obtain
::

    sage: HU.next()
    sage: print(HU)
    <BLANKLINE>
    Cohomology ring of SmallGroup(384,5602) with coefficients in GF(2)
    <BLANKLINE>
    Computed up to degree 2
    Minimal list of generators:
    [b_2_3: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
     b_2_4: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
     b_1_0: 1-Cocycle in H^*(SmallGroup(384,5602); GF(2)),
     b_1_1: 1-Cocycle in H^*(SmallGroup(384,5602); GF(2))]
    Minimal list of algebraic relations:
    []
    <BLANKLINE>

By the way, if one wants to verify that the stability conditions hold for the
elements of `HU`, then one can proceed as follows. Each element knows its
restriction to the subgroup used in the stable element method::

    sage: g = HU.1; g
    b_2_3: 2-Cocycle in H^*(SmallGroup(384,5602); GF(2))
    sage: g.val_str()
    'b_1_0^2+b_2_4'

We create the corresponding element of ``HSyl`` and verify that the two induced
maps involved in the stability conditions evaluate equal on this element::

    sage: gS = HSyl(g.val_str())
    sage: HU._PtoPcapCPdirect[0](gS) == HU._PtoPcapCPtwist[0](gS)
    True

In degree 3, we find the first relation::

    sage: HU.find_relations(3)[1]
    ['b_2_3*b_1_0']

The Hilbert\--Poincaré test
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let us compute the cohomology ring approximation out to degree six::

    sage: HU.make(6)
    sage: HU.last_interesting_degree()
    6
    sage: HU.expect_last_relation()
    6

Hence, it seems possible that the ring approximation is complete in degree
six. What parameters do we find? The filter regular ones are rather lengthy,
we only show one term so that the degrees are visible::

    sage: HU.parameters_from_sylow_subgroup()
    sage: HU.filter_regular_parameters()
    ['...b_1_1^8+...',
     '...b_3_9^4+...',
     '...b_1_0^2*b_3_0^4+...',
     'b_1_1+b_1_0']
    sage: HU.parameters()
    ['b_1_0^4+b_2_4^2+b_2_3^2+c_4_15',
     'b_3_9^2+b_3_0^2+b_2_4*b_1_0*b_3_0+b_2_4^3+b_2_3*c_4_15',
     'b_2_4+b_2_3',
     'b_1_1+b_1_0']
     sage: HU.dependent_parameters()
     ['b_1_0', 'b_1_1', 'c_4_15', 'b_3_0', 'b_3_9', 'b_2_3', 'b_2_4']

Let us determine in what degrees our three completion tests have a theoretical
chance to apply. We found a filter-regular hsop only in degrees 8, 12, 14 and
1 (the latter by replacing a degree 15 reduced Dickson element by some
parameter in degree 1). Hence, the Benson test in its original form could not
be applied before degree `7+11+13+1=32`. But it is possible to prove the
existence of a filter-regular hsop over a finite extension field, namely as
follows::

    sage: HU.potential_degree_bound(HU.filter_regular_parameters(), [8, 12, 14, 1])
    18
    sage: HU.WhatFRS
    (['c_4_15'], 6)

This answer means: There is some finite field extension for which the
cohomology ring has a filter-regular hsop formed by the Duflot element
``c_4_15``, together with three elements of degree 6. Let us verify the
existence result::

    sage: I = HU.relation_ideal()
    sage: HU.set_ring()
    sage: singular.eval('degBound=0')
    ''
    sage: (I + singular.ideal(['c_4_15'] + HU.standard_monomials(6))).std().dim()
    0

Since the lower bound for the depth of this cohomology ring is greater than
one, ::

    sage: HU.sylow_cohomology().depth()
    3

the modified Benson criterion could apply in degree `3+5+5+5=18`. But this is
not good enough. We could use the Symonds criterion with the algebraically
independent hsop in degrees 4, 6, 2, 1, so that the criterion could only apply
in degrees strictly greater than `3+5+1+0=9`, or with an algebraically
dependent hsop in degrees 1, 1, 4, 3, 3, 2, 2, so that again the criterion
could only apply in degrees strictly greater than `0+0+3+2+2+1+1=9`.
Nevertheless, let us test for completion now::

    sage: CohomologyRing.global_options('info')
    sage: HU.test_for_completion()
    H^*(SmallGroup(384,5602); GF(2)):
              We found parameters, but they would not allow for an application of Symonds' criterion.
              Trying to find better parameters in a more costly way.
              The Symonds criterion is inconclusive.
              Trying the Hilbert-Poincare criterion
              We expect that the Hilbert-Poincare criterion will not apply before degree 7
              No conclusion on the completeness of this cohomology ring.
    sage: CohomologyRing.global_options('warn')

Since it seems possible to apply the Hilbert\--Poincaré criterion in degree 7,
we compute the ring out to the next degree (but we do not find new relations
or generators), and succeed with applying the Hilbert\--Poincaré test::

    sage: HU.next()
    sage: HU.last_interesting_degree()
    6
    sage: HU.test_for_completion()
    True
    sage: HU._method
    'Hilbert-Poincar&eacute;'

So, in this example, the Hilbert\--Poincaré criterion is better than the
Symonds criterion, which is better than the modified Benson criterion. But
there are examples in which the relative strength of the criteria is
different.

Last, we verify the completeness test manually. In this example, we can show
that there is a finite field extension of `\mathbb F_2` over which there is an
hsop of the cohomology ring in degrees 4, 2, 1, 3, by applying our existence
result. We can replace the degree 12 parameter in our previously found
algebraically independent hsop by an element in degree 3, when extending the
base field::

    sage: HU.set_ring()
    sage: I = HU.relation_ideal()
    sage: (I + singular.ideal([HU.parameters()[0]] + HU.parameters()[2:] + HU.standard_monomials(3))).std().dim()
    0

This computation is done internally in the following method::

    sage: HU.parameter_degrees_over_field_extension()
    ((4, 2, 1, 3), 3, True)

The first output gives the parameter degrees, the second gives a lower bound
for the depths, and the third tells that the existence result has actually
been applied. Since `4+2+1+3-3=7`, the Hilbert\--Poincaré criterion can be
applied, and it proves completeness, since
::

    sage: p = HU.poincare_series()
    sage: t = p.parent().gen()
    sage: p*(1-t^4)*(1-t^2)*(1-t)*(1-t^3)
    t^6 + t^5 + t^4 + 3*t^3 + 2*t^2 + t + 1

is a polynomial of degree at most 7.

Stable element method in two steps
----------------------------------

Now, as we have computed the cohomology ring of an intermediate subgroup, we
aim at computing the cohomology ring of `G`, the symmetric group of rank
8. Since this group is not part of the small groups library, we need to assign
a name to it when defining the cohomology ring::

    sage: H = CohomologyRing(G, GroupName="SymmetricGroup(8)", prime = 2)
    sage: H
    H^*(SymmetricGroup(8); GF(2))

As we have announced above, the group studied in the previous subsection
is used as intermediate subgroup.
::

    sage: H.subgroup_cohomology() is HU
    True
    sage: H.sylow_cohomology() is HSyl
    True

There are three stability conditions, and look a bit more complicated, as
there occur three different intersections of our subgroup with its
conjugates::

    sage: H._PtoPcapCPdirect
    [Induced homomorphism of degree 0 from H^*(SmallGroup(384,5602); GF(2)) to H^*(D8xV4; GF(2)),
     Induced homomorphism of degree 0 from H^*(SmallGroup(384,5602); GF(2)) to H^*(SmallGroup(32,27); GF(2)),
     Induced homomorphism of degree 0 from H^*(SmallGroup(384,5602); GF(2)) to H^*(D8; GF(2))]

The computation of an approximation of the cohomology ring works as for the
cohomology of the intermediate subgroup. We have not demonstrated yet how to
prove that all cohomology generators have been found. So, let us compute out
to degree four::

    sage: H.make(4)
    sage: H.duflot_regular_sequence()
    ['c_4_0']
    sage: H.generator_degbound() # this has no output, but may set some attributes
    sage: print(H.degbound_for_gens)
    None

So, a Duflot regular sequence is available, but we can't determine a bound for
the maximal degree of a minimal generating set. Let us proceed until degree 7::

    sage: H.make(7)
    sage: H.generator_degbound()
    sage: H.degbound_for_gens
    8

So, we will find more generators at most in degree 8. Why is that? There will
be generators at most in the degree in which the cohomology ring of the
subgroup used in the stable element method can be generated as a module over
the image of the current ring approximation. Hence::

    sage: HU.set_ring()
    sage: singular.eval('degBound=0')
    ''
    sage: I = HU.relation_ideal()
    sage: (I + singular.ideal([x.val_str() for x in H.gens()[1:]])).std().kbase().sort()[1]
    1,
    b_1_1,
    b_2_3,
    b_1_1^2,
    b_2_3*b_1_1,
    b_1_1^3,
    b_3_9,
    c_4_15,
    b_2_3^2,
    b_2_3*b_1_1^2,
    b_2_3^2*b_1_1,
    b_2_3*b_1_1^3,
    b_2_3*b_3_9,
    b_2_3*c_4_15,
    b_2_3^3,
    b_2_3^2*b_1_1^2,
    b_2_3^3*b_1_1,
    c_4_15^2,
    b_2_3^3*b_1_1^2

The maximal degree of a module generator is 8 (which is the degree of the
last five elements in the above list of monomials), as we have claimed.
By consequence, when we compute degree 8, we still compute the stable subspace.
::

    sage: CohomologyRing.global_options('info')
    sage: H.make(8)
    H^*(SymmetricGroup(8); GF(2)):
              We have no degree bound yet
              Computing ring approximation in degree 8
              Determining stable subspace in degree 8
    H^*(SmallGroup(384,5602); GF(2)):
              Determine degree 8 standard monomials
    H^*(D8xV4; GF(2)):
              Determine degree 8 standard monomials
    H^*(SmallGroup(32,27); GF(2)):
              Determine degree 8 standard monomials
    H^*(D8; GF(2)):
              Determine degree 8 standard monomials
    H^*(SymmetricGroup(8); GF(2)):
              Setting up conditions to determine stable elements
              Solving equations
              Computing Groebner basis up to degree 8
              Exploring relations in degree 8
              Determine degree 8 standard monomials
              Express 27 standard monomials as cocycles
              Found 2 relations in degree 8
              There is no new generator in degree 8
              Try to lift 1st power of 0th Dickson invariant
              Exploring relations in degree 8
              Determine degree 8 standard monomials
              Express 25 standard monomials as cocycles
              Found 0 relations in degree 8
              Factorising an element; it can be interrupted with Ctrl-c
              Degree 8 of the visible ring structure is computed!
              Storing ring approximation
              We expect a relation in degree at least 14
              Computation of the ring approximation is finished
    <BLANKLINE>
              Storing ring approximation

Hence, we did actually not find another generator in degree 8, and we have
just proved that there will be no generators in higher degrees. So, starting
with degree 9, the computation of the ring approximation will be considerably
simplified, as there is no need to compute the stable subspace::

    sage: H.all_generators_found
    True
    sage: H.make(9)
              We have no degree bound yet
              Computing ring approximation in degree 9
              All generators are known
              Computing Groebner basis up to degree 9
              Exploring relations in degree 9
              Determine degree 9 standard monomials
              Express 35 standard monomials as cocycles
              Found 2 relations in degree 9
              There is no new generator in degree 9
              Degree 9 of the visible ring structure is computed!
              Storing ring approximation
              We expect a relation in degree at least 14
              Computation of the ring approximation is finished
    <BLANKLINE>
              Storing ring approximation

As we see, the last relations are expected in degree 14, which is actually too
high (the last relation is in degree 12), but let us compute out to degree 14
anyway.
::

    sage: CohomologyRing.global_options('warn')
    sage: H.make(14)
    sage: H.knownDeg
    14
    sage: H.last_interesting_degree()
    12

It now makes sense to study parameters. We find filter regular parameters in degrees 8, 12, 14 and 6
(we truncate the output),
::

    sage: H.filter_regular_parameters()
    ['...b_1_0^8+...',
     '...b_3_0^4+...',
     '...b_7_18^2+...',
     'b_1_0^6+b_6_0']

algebraically independent parameters in degrees 4, 6, 7 and 6
::

    sage: H.parameters()
    ['b_2_1^2+c_4_0',
     'b_3_1^2+b_3_0^2+b_2_1*c_4_0',
     'b_7_18+b_2_1*b_5_0+c_4_0*b_3_1+c_4_0*b_3_0',
     'b_1_0^6+b_6_0']

and algebraically dependent parameters in degrees 1, 7, 6, 4, 3, 3 and 2.
::

    sage: H.dependent_parameters()
    ['b_1_0', 'b_7_18', 'b_6_0', 'c_4_0', 'b_3_0', 'b_3_1', 'b_2_1']

Since `7+11+13+5`, `3+5+6+5` and `0+6+5+3+2+2+1` are all greater than the
current degree of approximation, we can only hope for using an existence proof
of parameters in smaller degrees. But alas, this fails for the Benson
criterion ::

    sage: H.potential_degree_bound(H.filter_regular_parameters(),[8, 12, 14,6])
    36

and for the Hilbert\--Poincaré criterion::

    sage: H.parameter_degrees_over_field_extension()
    ((4, 6, 7, 6), 3, False)
    sage: H.subgroup_cohomology().depth()
    3
    sage: 4+6+7+6-3
    20

We finish the computation and find that completion has been proven using the
Symonds criterion, in degree 20 (so, the same degree could also be obtained
with the Hilbert\--Poincaré criterion), using an algebraically dependent
hsop::

    sage: H.make()
    sage: H._method
    'Symonds'
    sage: H.knownDeg
    20
    sage: H._parameters_for_criterion
    ['b_1_0', 'b_7_18', 'b_6_0', 'c_4_0', 'b_3_0', 'b_3_1', 'b_2_1']


References
==========

.. [AdemMilgram] Alejandro Adem, R. James Milgram: *Cohomology of finite groups.* Second edition. Grundlehren der Mathematischen Wissenschaften [Fundamental Principles of Mathematical Sciences], **309.** Springer-Verlag, Berlin, 2004.
.. [Benson] Dave Benson: Dickson invariants, regularity and computation in group cohomology. *Illinois J. Math.* **48** (2004), 171--197.
.. [BensonCarlson] Dave Benson, Jon F. Carlson: Projective resolutions and Poincaré duality complexes. *Trans. Amer. Math. Soc.* **342** (1994), 447--488.
.. [CartanEilenberg] Henri Cartan and Samuel Eilenberg: *Homological algebra*. Princeton University Press, Princeton, N. J., 1956.
.. [Duflot] Jeanne Duflot: Depth and equivariant cohomology, *Comment. Math. Helv.* **56** (1981), 627--637.
.. [EllisKing] Graham Ellis and Simon King: `Persistent homology of groups. <http://arxiv.org/abs/1006.2237>`_, *J. Group Theory* **14** (2011), 575--587.
.. [Green] David Green: Gr\"obner bases and the computation of group cohomology.  *Lecture Notes in Mathematics,* **1828**. Springer-Verlag, Berlin, 2003.
.. [GreenKing] David Green, Simon King: `The computation of the cohomology rings of all groups of order 128. <http://arxiv.org/abs/1001.2577>`_, *J. Algebra* **325** (2011), 352--363.
.. [King] Simon King: `Comparing completeness criteria for modular cohomology rings of finite groups. <http://dx.doi.org/10.1016/j.jalgebra.2012.11.003>`_, *J. of Algebra* **374** (2013), 247--256.
.. [KingGreenEllis] Simon King, David Green, Graham Ellis: `The Mod-2 Cohomology Ring of the Third Conway Group is Cohen-Macaulay. <http://dx.doi.org/10.2140/agt.2011.11.719>`_, *Algebraic \& Geometric Topology* **11** (2011), 719--734.
.. [Kraines] David Kraines: Massey Higher Products. *Trans. AMS* **124** (1966), 431--449.
.. [Kuhn] Nicholas J. Kuhn: Primitives and central detection numbers in group cohomology, *Adv. Math.* **216** (2007), 387--442.
.. [Pham] Pham Anh Minh: Modular invariant theory and cohomology algebras of extra-special `p`-groups. *Pacific J. Math.* **124** (1986), 345--363.
.. [Ravenel] Douglas Ravenel, *Complex cobordism and stable homotopy groups of spheres,* Pure and Applied Mathematics, **121**. Academic Press, Inc., Orlando, FL, (1986).
.. [Symonds] Peter Symonds: `On the Castelnuovo-Mumford Regularity of the Cohomology Ring of a Group <http://www.maths.manchester.ac.uk/~pas/preprints/coreg.pdf>`_.  *J. American Math. Soc.,* **23** (2010), 1159--1173.
.. [Wilkerson] Clarence Wilkerson: *A primer on the Dickson invariants,* Proceedings of the Northwestern Homotopy Theory Conference (Evanston, Ill., 1982), *Contemp. Math.,* **19** (1983), 421--434.


"""

from pGroupCohomology.factory import CohomologyRing

# -*- coding: utf-8 -*-

#*****************************************************************************
#
#    Modular Cohomology Rings of Finite Non Prime Power Groups
#
#    Copyright (C) 2010, 2015 Simon A. King <simon.king@uni-jena.de>
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
Modular Cohomology Rings of Finite Non-Primepower Groups.

This module contains :class:`MODCOHO`, that provides a framework for the computation of
the cohomology rings with coefficients in `\mathbb F_p` for any finite group.

It is based on the stable element method of Henri Cartan and Samuel
Eilenberg [CartanEilenberg]_ and uses a completeness criterion based
on the Poincaré series [King]_.  The stable element method involves the
computation of cohomology rings of finite `p`-groups, which is based
on the class :class:`~pGroupCohomology.cohomology.COHO`. See
:mod:`pGroupCohomology` for an introduction.

AUTHORS:

- Simon King <simon.king@uni-jena.de>

"""

from __future__ import print_function, absolute_import
import sys, os
from pGroupCohomology import CohomologyRing
from pGroupCohomology.auxiliaries import coho_options, coho_logger, safe_save, _gap_reset_random_seed, Failure
from pGroupCohomology.cohomology import COHO, temporary_result, permanent_result

from sage.all import Ring
from sage.all import Integer
from sage.all import cputime
from sage.all import walltime
from sage.all import load
from sage.all import SAGE_ROOT
from sage.all import Algebras, CommutativeAlgebras
from sage.all import subsets
from sage.all import Infinity

from pGroupCohomology.resolution_bindings cimport *
from sage.libs.meataxe cimport *
from sage.matrix.matrix_gfpn_dense cimport Matrix_gfpn_dense as MTX
from sage.matrix.matrix_gfpn_dense cimport new_mtx
from sage.rings.polynomial.hilbert import hilbert_poincare_series, first_hilbert_series
from pGroupCohomology.auxiliaries import gap, singular
from pGroupCohomology.cohomology import unpickle_gap_data, pickle_gap_data
from pGroupCohomology.resolution cimport *
from pGroupCohomology.cochain cimport COCH, ChMap

#############################
##                         ##
##   Auxiliary functions   ##
##                         ##
#############################

def _IdGroup(G, D, Client, ring=True):
    """
    Assign an identification number for a given group, that is unique in the current session.

    INPUT:

    - ``G``, a group in the libGAP interface
    - ``D``, a dictionary of dictionaries. ``D[q][n]`` returns the
      modular cohomology ring of the group of order ``q`` that was
      assigned to number ``n``. ``D['prime']`` must return
      the common modulus for all modular cohomology rings.
    - ``Client``, some cohomology ring. This is only used to retrieve
      the options that shall be used to compute cohomology rings.
    - ``ring`` (optional boolean, default ``True``): If ``True``,
      create the cohomology ring of ``G`` and store it in ``D``.

    OUTPUT:

    - A triple ``q,n,G2``, where ``q`` is the order of ``G``
      and ``G = G2``, where the generating sets of ``G`` and ``G2``
      may differ. If the number ``n`` is positive then ``q,n`` is
      the address of ``G`` in the Small Groups library.
    - If the option ``ring=True`` is used, then the cohomology ring
      of ``G`` with coefficients in ``GF(D['prime'])`` is stored as
      ``D[q][n]``. If ``G`` can not be found in the Small Groups
      library then ``n<=0``, and the pair ``(q,n)`` is a unique
      identifier for the isomorphism class of ``G`` in the current
      session.
    - If the option ``ring=False`` is used then ``n`` is such that
      ``G`` is isomorphic to a group whose cohomology is stored in
      ``D[q][n]``, or (if ``G`` can't be found in the Small Groups
      library) ``n = -len(D[q].keys())``.
    - The generators of ``G2`` match the generators of the group of
      ``D[q][n]``.

    NOTE:

    This function may change the generators of ``G``.

    TESTS::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(8,3)
        sage: from pGroupCohomology.modular_cohomology import _IdGroup
        sage: D = {'prime':3}
        sage: G1 = libgap.AlternatingGroup(7)

    The group order is beyond the scope of the ``SmallGroups`` library.
    So, the triple "(Group Order, 0, <group with potentially smaller generating set>)"
    is returned::

        sage: _IdGroup(G1, D, H, ring=False)
        (2520, 0, Group([ (1,2,3,4,5,6,7), (5,6,7) ]))

    We take another group of the same order and compute their cohomology
    rings. Since the cohomology of ``G1`` was not stored in ``D``, a new
    entry is created as ``D[q][n]``::

        sage: G2 = libgap.CyclicGroup(2520)
        sage: _IdGroup(G2,D,H)
        (2520, 0, <pc group of size 2520 with 1 generators>)
        sage: D['prime']
        3
        sage: sorted([(k,v) for (k,v) in D.items() if k!='prime'])
        [(2520, {0: H^*(8gp3_2520_0; GF(3))})]

    When we now test ``G1`` again, a different identifier is returned,
    since it is not isomorphic to ``G2``::

        sage: _IdGroup(G1,D,H, ring=False)
        (2520, -1, Group([ (1,2,3,4,5,6,7), (5,6,7) ]))

    However, the identifier for ``G2`` is preserved::

        sage: _IdGroup(G2,D,H, ring=False)
        (2520, 0, <pc group with 1 generators>)

    If a group can be found in the Small Groups library, that value
    will always be used::

        sage: G3 = libgap.AlternatingGroup(6)
        sage: _IdGroup(G3,D,H, ring=False)
        (360, 118, Group([ (1,2,6,5,4), (1,2,3,5,4) ]))
        sage: sorted([(k,v) for (k,v) in D.items() if k!='prime'])
        [(360, {}), (2520, {0: H^*(8gp3_2520_0; GF(3))})]
        sage: _IdGroup(G3,D,H)
        (360, 118, Group([ (1,2,6,5,4), (1,2,3,5,4) ]))
        sage: sorted([(k,v) for (k,v) in D.items() if k!='prime'])
        [(360, {118: H^*(SmallGroup(360,118); GF(3))}),
         (2520, {0: H^*(8gp3_2520_0; GF(3))})]

    """
    gap = G.parent()
    _gap_reset_random_seed()
    try:
        q,n = G.IdGroup().sage()
        coho_logger.info( "Considering SmallGroup(%d,%d)"%(q,n), None)
        if q!=1:
            if q in D and n in D[q]:
                H = D[q][n]
                try:
                    phi = H.group().canonicalIsomorphism(G)
                except:
                    _gap_reset_random_seed()
                    phi = H.group().canonicalIsomorphism(G)
                if phi == Failure:
                    phi = H.group().IsomorphismGroups(G)
#~                 gap.eval('%s:=Group(List([1..Length(GeneratorsOfGroup(%s))],
#~                    x->Image(%s,GeneratorsOfGroup(%s)[x])))'%(G.name(),H.group().name(),phi.name(),H.group().name()))
                    G = gap.Group([phi.Image(g) for g in H.group().GeneratorsOfGroup()])
            else:
                phi = gap.SmallGroup(q,n).IsomorphismGroups(G)
#~                 gap.eval('%s:=Group(List([1..Length(GeneratorsOfGroup(Source(%s)))],
#~                     x->Image(%s,GeneratorsOfGroup(Source(%s))[x])))'%(G.name(),phi.name(),phi.name(),phi.name()))
                G = gap.Group([phi.Image(g) for g in phi.Source().GeneratorsOfGroup()])
        if q in D and n in D[q]:
            return (q,n,G)
        if not q in D:
            D[q] = {}
        if ring:
            if (q,n)!=(1,1):
                if D['prime'].divides(q):
                    if q.is_prime_power():
                        D[q][n] = CohomologyRing(q,n,useFactorization=Client.useFactorization,useElimination=Client.useElimination)
                    else:
                        D[q][n] = CohomologyRing(q,n, prime=D['prime'],useFactorization=Client.useFactorization,useElimination=Client.useElimination)
        return (q,n,G)

    except BaseException, msg:
        if not ("group identification" in str(msg)):
            raise msg
    q = G.Order().sage()
    coho_logger.info( "Considering group of order %s"%q, None)
    if not q in D:
        D[q]={}
    for m,H in D[q].items():
        phiG = H.group().IsomorphismGroups(G)
        if phiG != Failure:
#~             gap.eval('%s:=Group(List([1..Length(GeneratorsOfGroup(%s))],x->Image(%s,GeneratorsOfGroup(%s)[x])))'%
#~                 (G.name(),H.group().name(),phiG.name(),H.group().name()))
            G = gap.Group([ phiG.Image(g) for g in H.group().GeneratorsOfGroup()])
            return (q,m,G)
    n = -len(D[q].keys())
    coho_logger.info( "Computing minimal generating set of the group", None)
    try:
        G = G.MinimalGeneratingSet().Group()
    except (RuntimeError, ValueError):
        coho_logger.warning( "Failed to construct a minimal generating set of the group -- keep your fingers crossed...", None)
        G = G.SmallGeneratingSet().Group()
    if ring:
        if q.is_prime_power():
            D[q][n] = CohomologyRing(G,GStem=Client.GStem+'_%d_%d'%(q,-n),useFactorization=Client.useFactorization,useElimination=Client.useElimination)
        else:
            D[q][n] = CohomologyRing(G,GStem=Client.GStem+'_%d_%d'%(q,-n), prime=D['prime'],useFactorization=Client.useFactorization,useElimination=Client.useElimination)
    return (q,n,G)

###################################################
##                                               ##
##   Modular Cohomology Rings of finite groups   ##
##                                               ##
###################################################

class MODCOHO(COHO):
    """
    Modular cohomology rings of finite groups that are not of prime power order.

    Normally, instances of this class should be created using the constructor
    :func:`~pGroupCohomology.CohomologyRing`, since this takes care of
    uniqueness of parent structures. See
    :func:`~pGroupCohomology.CohomologyRing` and
    :mod:`pGroupCohomology` for an introduction.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: G = libgap.SmallGroup(48,36)
        sage: H1 = CohomologyRing(G, prime=2, GroupName='SomeGroup', from_scratch=True)
        sage: H1.make()
        sage: H1.poincare_series()
        1/(-t^3 + 3*t^2 - 3*t + 1)
        sage: H2 = CohomologyRing(48,36, prime=2)   # indirect doctest

    In order to save resources, the cohomology ring is cached and then
    reloaded even if a different definition is provided::

        sage: H1 is H2
        True
        sage: print(H2)
        Cohomology ring of SomeGroup with coefficients in GF(2)
        <BLANKLINE>
        Computation complete
        Minimal list of generators:
        [c_2_5: 2-Cocycle in H^*(SomeGroup; GF(2)),
         b_1_0: 1-Cocycle in H^*(SomeGroup; GF(2)),
         b_1_1: 1-Cocycle in H^*(SomeGroup; GF(2)),
         c_1_2: 1-Cocycle in H^*(SomeGroup; GF(2))]
        Minimal list of algebraic relations:
        [b_1_0*b_1_1]
        sage: H2 is loads(dumps(H2))
        True

    """
    def __init__(self, G,p, HP,Subgroup, **kwds):
        """
        Normally, instances of this class should be created using the constructor
        :func:`pGroupCohomology.CohomologyRing`, since this takes care of unique
        parent structures. Here, we demonstrate the input used internally.

        INPUT:

        - ``G`` (Group in GAP)
        - ``p`` (prime number, must divide the order of ``G``)
        - ``HP`` (instance of :class:`~pGroupCohomology.cohomology.COHO` or
          :class:`~pGroupCohomology.modular_cohomology.MODCOHO`): Cohomology ring
          of a subgroup of ``G`` the stable element method will be applied to
        - ``Subgroup``, a subgroup of ``G`` that contains a Sylow subgroup of ``G``.
          The generators of ``Subgroup`` must match the generators of ``HP.group()``.
        - optional ``SubgpId``, the address of ``Subgroup`` in the Small Groups library.
        - optional ``GPerm`` (permutation group isomorphic to ``G``)
        - optional ``GroupName``, a name for ``G``
        - optional ``GroupDescr``, a phrase used to describe ``G``; will only be used in
          a web page created for the cohomology ring
        - optional ``GStem``, a not necessarily descriptive identifier of the cohomology ring,
          which will be used for creating file names

        If ``G`` has no custom name in GAP, ``GStem`` must be provided.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.modular_cohomology import MODCOHO
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.SymmetricGroup(6)
            sage: S = G.SylowSubgroup(3)
            sage: P = G.Normalizer(S.Centre())
            sage: P.IdGroup()
            [ 72, 40 ]
            sage: HP = CohomologyRing(72,40,prime=3, from_scratch=True)
            sage: HP.make()
            sage: phiP = HP.group().IsomorphismGroups(P)
            sage: P = libgap.Group([phiP.Image(g) for g in HP.group().GeneratorsOfGroup()])
            sage: H1 = MODCOHO(G,3,HP,P,GroupName='Sym6',GStem='S6')   # indirect doctest
            sage: H1.make()
            sage: H1
            H^*(Sym6; GF(3))
            sage: print(H1)
            Cohomology ring of Sym6 with coefficients in GF(3)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_4_0: 4-Cocycle in H^*(Sym6; GF(3)),
             c_8_1: 8-Cocycle in H^*(Sym6; GF(3)),
             a_3_0: 3-Cocycle in H^*(Sym6; GF(3)),
             a_7_1: 7-Cocycle in H^*(Sym6; GF(3))]
            Minimal list of algebraic relations:
             []
            sage: H2 = MODCOHO(G,3,HP._HSyl,S,GroupName='Sym6',GStem='S6b')
            sage: H2.make()
            sage: print(H2)
            Cohomology ring of Sym6 with coefficients in GF(3)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_4_0: 4-Cocycle in H^*(Sym6; GF(3)),
             c_8_1: 8-Cocycle in H^*(Sym6; GF(3)),
             a_3_0: 3-Cocycle in H^*(Sym6; GF(3)),
             a_7_1: 7-Cocycle in H^*(Sym6; GF(3))]
            Minimal list of algebraic relations:
            []

        """
        # Strange, but these three lines seem necessary:
        self.__dict__['_property_dict']={}
        self._property_dict = self.__dict__['_property_dict']
        self._decorator_cache = {}

        from weakref import WeakValueDictionary
        from pGroupCohomology.cohomology import COHO_prefix, COHO_Terminator
        self._HomsetCache = WeakValueDictionary({})
        self.GenS = singular(0)
        singular.eval('option(redSB,redTail,redThrough)')
        singular.LIB('general.lib')
        self.prefix = COHO_prefix()()
        self._Terminator = COHO_Terminator(self.GenS, self.prefix)
        try:
            p = Integer(p)
        except:
            raise ValueError("base field must be given by a prime number")
        if not p.is_prime():
            raise ValueError("base field must be given by a prime number")
        from sage.all import GF
        base_ring = GF(p)
        if base_ring.characteristic()==2:
            cat = CommutativeAlgebras(base_ring)
        else:
            cat = Algebras(base_ring)
        # Avoid some generic stuff that would override essential methods
        self._no_generic_basering_coercion = True
        Ring.__init__(self,GF(p), category=cat)
        self._prime = p
        if G==None: # used for pickling
            return

        if not hasattr(G,'parent'):
            raise ValueError("The group must be given in the Gap interface")
        gap = G.parent()
        if not isinstance(HP,COHO):
            raise TypeError("Cohomology ring of a subgroup expected, not "+repr(type(HP)))
        GPerm     = kwds.get('GPerm')
        SubgpId   = kwds.get('SubgpId')
        GroupName = kwds.get('GroupName')
        GStem = kwds.get('GStem')
        if 'GroupDescr' in kwds:
            self.setprop('GroupDescr', kwds.get('GroupDescr'))

        ##########################################
        ## Basic setup
        ##########################################

        self.setprop('useElimination',kwds.get('useElimination'))
        if kwds.get('useFactorization') is not None:
            self.setprop('useFactorization', kwds.get('useFactorization'))
        else:
            self.setprop('useFactorization', True)
        self._DuflotRegSeq = [] # will be a maximal Duflot regular sequence

        # Get some Group-ID
        if isinstance(G,tuple):
            GId = G
            G = gap.SmallGroup(G[0], G[1])
            GStem = GStem or "%dgp%d"%(GId[0],GId[1])
        else:
            gap = G.parent()
            GId = kwds.get('GroupId',(G.Order().sage(),0))
            if GId[1]>0:
                try:
                    bla = gap.SmallGroup(GId[0],GId[1]).canonicalIsomorphism(G)
                except:
                    _gap_reset_random_seed()
                    bla = gap.SmallGroup(GId[0],GId[1]).canonicalIsomorphism(G)
                if bla == Failure:
                    raise ValueError("Group and GroupId are incompatible")
        self._Order = GId[0]

        # Construct GStem
        if GStem is None: # explicit advice of the user has preference.
            # If nothing else is found, use Name from gap
            if G.HasName():
                GStem = G.Name().sage()
            else:
                raise ValueError("Can not infer group name: Optional argument <GStem> must be provided")
        self.GStem = GStem

        if GroupName or G.HasName():
            self.setprop('GroupName', GroupName or G.Name().sage())

        # Find an *equivalent* PermutationGroup
        if GPerm is None:
            if not G.IsPermGroup():
                G2 = G.asPermgroup()
#~                 tmpPhi = gap('GroupHomomorphismByImages(%s,%s,GeneratorsOfGroup(%s),GeneratorsOfGroup(%s))'%
#~             (G.name(),G2.name(),G.name(),G2.name()))
                tmpPhi = G.GroupHomomorphismByImages(G2, G.GeneratorsOfGroup(), G2.GeneratorsOfGroup())
            else:
                tmpPhi = None
                G2 = G
        else:
            G2 = GPerm
            if kwds.get('verifyGroupIso'):
                try:
                    tmpPhi = G.canonicalIsomorphism(G2)
                except:
                    _gap_reset_random_seed()
                    tmpPhi = G.canonicalIsomorphism(G2)
            else:
#~                 tmpPhi = gap('GroupHomomorphismByImagesNC(%s,%s,GeneratorsOfGroup(%s),GeneratorsOfGroup(%s))'%
#~                 (G.name(),G2.name(),G.name(),G2.name()))
                tmpPhi = G.GroupHomomorphismByImagesNC(G2, G.GeneratorsOfGroup(), G2.GeneratorsOfGroup())
            if tmpPhi == Failure:
                raise ValueError("The given permutation group GPerm is not an equivalent description of the given group G")
        self._gap_group = G2
        self._gapBackup = ('Group('+G2.GeneratorsOfGroup().String().sage()+')').replace('\n','').replace(' ','')
        # Conclusion:
        # G is whatever group.
        # G2=self.group() is a permutation group equivalent to G.
        # If G is not G2, tmpPhi:G->G2 is an isomorphism;
        # otherwise tmpPhi is None

        # The subgroups HP and Subgroup must be provided by CohomologyRing
        # Test if they are admissible
        if not G.IsSubgroup(Subgroup):
            raise ValueError("We expected a group-subgroup pair")
        if kwds.get('verifyGroupIso'):
            try:
                bla = Subgroup.canonicalIsomorphism(HP.group())
            except:
                _gap_reset_random_seed()
                bla = Subgroup.canonicalIsomorphism(HP.group())
            if bla == Failure:
                raise ValueError("The generators of the given subgroup must be compatible with those of the group of the given cohomology ring")

        P = Subgroup
        PId = SubgpId
        if PId is None:
            # P is too big for the IdGroup algorithm!
            self._POrder = Order = P.Order().sage()
            if Order == 1:
                raise ValueError("Sylow subgroups cannot be trivial!")
        else:
            self._POrder = Order = PId[0]
        self._HP = HP
        self.Resl = self._HP.Resl
        coho_logger.info( "Using a subgroup of order %s", self, self._POrder)
        if not HP.completed:
            HP.make()

        # Now we have P set up as subgroup of G, but the attribute
        # _Subgp has to provide
        # a subgroup of self.group()
        if tmpPhi is not None:
            # P is compatible with HP. So, map the generators
            self._Subgp = gap.Group([tmpPhi.Image(g) for g in P.GeneratorsOfGroup()])
        else: # G is a perm group, thus so is P
            self._Subgp = P
        self._SubgpBackup = ('Group(' + self._Subgp.GeneratorsOfGroup().String().sage() + ')').replace('\n','').replace(' ','')

        # We also need a Sylow p-subgroup (might be identical with _Subgp)
        HS = HP
        while isinstance(HS, MODCOHO):
            HS = HS._HP
        self._HSyl = HS
        # The subgroup pair (P, _SylowGp) has to be compatible with (HP.group(),HP.sylow_subgroup())
        # This was forgotten in the old approach
        #
        # However, if it was called by CohomologyRing, we already
        # have a canonical Isomorphism by construction, and also
        # it was checked above if kwds.get('verifyGroupIso').
        # So now, do it quick and dirty...
        if kwds.get('verifyGroupIso'):
            try:
                phiHPtoP = HP.group().canonicalIsomorphism(P)
            except:
                _gap_reset_random_seed()
                phiHPtoP = HP.group().canonicalIsomorphism(P)
        else:
            PGen = P.GeneratorsOfGroup()
            phiHPtoP = HP.group().GroupHomomorphismByImagesNC(P, HP.group().GeneratorsOfGroup(), [PGen[i] for i in range(HP.group().GeneratorsOfGroup().Length().sage())])
        SubSylow = (HP.sylow_subgroup or HP.group)()
        _SylowGp = gap.Group([phiHPtoP.Image(g) for g in SubSylow.GeneratorsOfGroup()])
        if tmpPhi is not None:
            self._SylowGp = gap.Group([tmpPhi.Image(g) for g in _SylowGp.GeneratorsOfGroup()])
        else:
            self._SylowGp = _SylowGp
        self._SylowGpBackup = ('Group(' + self._SylowGp.GeneratorsOfGroup().String().sage() + ')').replace('\n','').replace(' ','')

        # Starting the subgroup dictionary
        if PId is None:
            SubgpDict = { Order : {-1:HP} }
        else:
            SubgpDict = { PId[0] : {PId[1]:HP} }
        SubgpDict['prime'] = p

        ######################################################
        ## SECOND STEP:
        ## Restrictions to the intersection of P with its conjugates
        ######################################################
        # The intersections of P with its images under conjugation:
        # and the corresponding cohomology maps

        # We are interested in the stable elements of self._HP. The only
        # elements of G that act nontrivially on P are its double coset
        # representatives.
        coho_logger.info( "Computing double coset representatives for the given subgroup", self)
        CBase = G.DoubleCosetRepsAndSizes(P,P) # This should start with 1, but we better don't rely on it.
        coho_logger.info( "Intersecting subgroup with %d conjugates", self, CBase.Length().sage())
        C = [] # relevant double coset representatives
        phiC = [] # conjugator isomorphism corresponding to C
        HCP = [] # the cohomology of the intersection of P with its conjugates
        PtoPcapCP = [] # the restriction of P to the intersections
        CPtoPcapCP = [] # the restriction of P-conjugates to the intersections
        for i in range(CBase.Length().sage()): # don't consider the trivial element, which comes first
            c = CBase[i][0]
            # The conjugator automorphisms, later restricted to P
            phiG = G.ConjugatorAutomorphism(c)
            PConj = phiG.Image(P)
            X = P.Intersection(PConj)
            if X.Order().sage() != 1:
                # This tries to get the generating sets and may change
                # the list of generators of X
                if X.Order().sage() == self._POrder:
                    # Use the generating set of P, so that the generators of the
                    # conjugates CP of P are compatible with the cohomology ring HP.
                    X = PConj = P
                    HCP.append(HP)
                    C.append(c)
                    phi = P.GroupHomomorphismByImages(PConj, P.GeneratorsOfGroup(), [phiG.Image(g) for g in P.GeneratorsOfGroup()])
                    phiC.append(phi)
                else:
                    # The following line may change the generating set of X and will provide
                    # the cohomology of X.
                    PIdTmp = _IdGroup(X, SubgpDict, self)
                    X = PIdTmp[2]
                    PIdTmp = PIdTmp[:2]
                    C.append(c)
                    phi = P.GroupHomomorphismByImages(PConj, [phiG.Image(g) for g in P.GeneratorsOfGroup()])
                    phiC.append(phi)
                    if (PIdTmp != (1,1)) and p.divides(PIdTmp[0]):
                        HCP.append(SubgpDict[PIdTmp[0]][PIdTmp[1]])
                        if not HCP[-1].completed:
                            HCP[-1].make()
                    else:
                        HCP.append(None)
                if HCP[-1] is not None:
                    # Now, construct the restriction maps
                    PtoPcapCP.append( HP.hom( X.GroupHomomorphismByImages(P, X.GeneratorsOfGroup(), X.GeneratorsOfGroup()), HCP[-1]))
                    # Since phiG is mono, PreImagesRepresentative is unique.
                    CPtoPcapCP.append(HP.hom( X.GroupHomomorphismByImages(P,
                            [phiG.PreImagesRepresentative(g) for g in X.GeneratorsOfGroup()]), HCP[-1]))
        if tmpPhi is not None:
            self.setprop('Cosets',[tmpPhi.Image(X).String().sage().replace('\n','').replace(' ','') for X in C])
        else:
            self.setprop('Cosets',[X.String().sage().replace('\n','').replace(' ','') for X in C])

        if len(C)==0:
            coho_logger.info( "No stability condition - all cocycles are stable", self)
        elif len(C)==1:
            coho_logger.info( "1 double coset may be relevant to stability", self)
        else:
            coho_logger.info("%d double cosets may be relevant to stability",self, len(C))

        # The elements of self are represented by the stable
        # elements of self._HP, and these are the elements on
        # which the following two series of maps coincide:
        IdPairs=[]
        self._PtoPcapCPdirect = []
        self._PtoPcapCPtwist = []
        for i in range(len(PtoPcapCP)): # this is equal to len(self.Cosets)
            X = PtoPcapCP[i]
            if X is not None:
                Y = CPtoPcapCP[i]
                if X is not Y: # hence, they may contribute
                    ID = set([id(X),id(Y)])
                    if ID not in IdPairs:
                        self._PtoPcapCPdirect.append(X)
                        self._PtoPcapCPtwist.append(Y)
                        IdPairs.append(ID)
                    else:
                        self.Cosets[i] = None
                else:
                    self.Cosets[i] = None
        self.setprop('Cosets',[X for X in self.Cosets if X is not None])
        # in the folowing method, maps are removed if their singular
        # representations are redundant
        self._simplifyMapData()
        if len(self._PtoPcapCPdirect)==0:
            coho_logger.info( "All cocycles are stable", self)
        elif len(self._PtoPcapCPdirect)==1:
            coho_logger.info( "One induced map on the cohomology of the given subgroup may be relevant to stability", self)
        else:
            coho_logger.info("%d induced maps on the cohomology of the given subgroup may be relevant to stability",self, len(self._PtoPcapCPdirect))

        # The key is:
        # - A unique description of the given group-with-generators
        # - The key of self._HP (in particular, it determines a
        #   group-with-generators equivalent to a subgroup)
        # - The prime
        self.setprop('_key', (( ''.join([t.strip() for t in ('Group('+G2.GeneratorsOfGroup().String().sage()+')').split()]),) if GId[1]==0 else tuple(GId), self.GStem, self._HP._key, p))
        # Insert self into the cache
        from pGroupCohomology import CohomologyRing
        _cache = CohomologyRing._cache
        _cache[self._key] = self  # Note that there is no entry yet with this key --
                                  # provided that the ring
                                  # initialisation is done with
                                  # CohomologyRing!

        ####################################################
        ## THIRD STEP
        ## Several basic attributes must concide with those of self._HP
        ####################################################

        self.Gen = [] # Gen contains the list of generators
        self.firstOdd = 0
        self.Rel = []  # shall be a list of polynomials given by strings
        self.knownDeg = 0
        self.lastRelevantDeg = 0 # this is the last degree in which a Singular ring was created
        self.completed = False
        self.suffDeg = -1
        self.degvec = []
        self.Triangular = {} # Contains (for each degree) an echelon basis for decomposable classes.
        self.lastRel = 0
        self.RelG = None # shall be a list of polynomials given by strings
        self.StdMon = {0:{'1':singular('1')}}
        self.Dickson = [] # shall contain strings that eventually help to define a filter regular sequence
        self.alpha = None # used in Benson's criterium. Is very likely to be -1, if the cohomology ring is computed
        self.InitSubgroups()
        # Finally, if we are lucky, the computation is actually already
        # done, since self is "the same" as self._HP
        self._copy_from_subgroup() # checks if there are stability conditions

    def __reduce__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(48,48,prime=3, from_scratch=True)
            sage: H.make()
            sage: loads(dumps(H)) is H   #indirect doctest
            True

        """
        singular = self.GenS.parent()
        SubgroupList = []
        PtoPcapCPdirect = []
        PtoPcapCPtwist  = []
        PtoPcapCPdirectSing = []
        PtoPcapCPtwistSing = []
        if self._PtoPcapCPdirectSing:
            try:
                self._PtoPcapCPdirectSing[0]._check_valid()
            except:
                self._simplifyMapData()
        # stability conditions
        for i in range(len(self._PtoPcapCPdirect)):
            singular(self._PtoPcapCPdirect[i].codomain()).set_ring()
            SubgroupList.append(self._PtoPcapCPdirect[i].codomain()._key)
            PtoPcapCPdirectSing.append(singular.eval('string(%s)'%self._PtoPcapCPdirectSing[i].name()))
            PtoPcapCPtwistSing.append(singular.eval('string(%s)'%self._PtoPcapCPtwistSing[i].name()))
            PtoPcapCPdirect.append(self._PtoPcapCPdirect[i].__reduce__()[1][2:])
            PtoPcapCPtwist.append(self._PtoPcapCPtwist[i].__reduce__()[1][2:])
        if self.subgpDickson:
            sgpDickson = [(i,[(X.val_str(), X.Deg, X._name, X._rdeg, X._ydeg) for X in gpDickson]) for i,gpDickson in self.subgpDickson.items()]
        else:
            sgpDickson = []

        # Ring structure
        GEN = [(X.val_str(), X.Deg, X._name, X._rdeg, X._ydeg) for X in self.Gen]
        Triangular = []
        DuflotRegSeq = [(X.val_str(), X.Deg, X._name, X._rdeg, X._ydeg) for X in self._DuflotRegSeq]
        ## Singular elements:
        StdMon = []
        DG = []
        # we need to set the singular ring of self
        if self.lastRelevantDeg:
            self.set_ring()
            # it may happen that a relation was found *after*
            # the last make_groebner was issued. So, we need
            # to update self.RelG
            self.RelG = [s.strip() for s in singular.eval('print(%sI)'%(self.prefix)).split(',')]
            for nkey in self.StdMon.keys():
                StdMon.append([nkey,[]])
                # it may be that some of the data aren't defined in singular anymore
                if [1 for _ in self.StdMon[nkey].values() if _.parent().eval('defined(%s)'%_.name())=='1']:
                    for monkey in self.StdMon[nkey].keys():
                        StdMon[-1][1].append([monkey, [s.strip() for s in str(self.StdMon[nkey][monkey]).split(',')]])
        # self._HP can be found (on disk or wherever) if its group description
        # and its GStem are.
        # But this is part of self._key, thus, is in self._property_dict
        return MODCOHO_unpickle, (self._prime, GEN, self.Rel, self.RelG, self.lastRel, self.lastRelevantDeg, self.knownDeg, self.suffDeg, self.completed, self.Dickson, DuflotRegSeq, self.alpha, Triangular, StdMon, DG, self._gapBackup, self._SubgpBackup, self._SylowGpBackup, SubgroupList, PtoPcapCPdirect, PtoPcapCPtwist, PtoPcapCPdirectSing, PtoPcapCPtwistSing, self._Order, self._POrder, sgpDickson, pickle_gap_data(list(self._property_dict.items())), self.SingularTime, pickle_gap_data(list(self._decorator_cache.items())))

    def set_ring(self):
        """
        Set the underlying ring in the Singular interface.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(48,48,prime=2, from_scratch=True)
            sage: H.make(2)
            sage: H.set_ring()

        This is the underlying ring out to degree 2::

            sage: singular('basering')
            polynomial ring, over a field, global ordering
            // coefficients: ZZ/2
            // number of vars : 3
            //        block   1 : ordering M
            //                  : names    c_2_3 b_1_0 c_1_1
            //                  : weights      2     1     1
            //                  : weights     -1     0    -1
            //                  : weights     -1     0     0
            //        block   2 : ordering C

        There are more generators in higher degree::

            sage: H.make()
            sage: H.set_ring()
            sage: singular('basering')
            polynomial ring, over a field, global ordering
            // coefficients: ZZ/2
            // number of vars : 4
            //        block   1 : ordering M
            //                  : names    c_2_3 b_1_0 c_1_1 c_3_6
            //                  : weights      2     1     1     3
            //                  : weights     -1     0    -1    -1
            //                  : weights     -1     0     0     0
            //                  : weights      0    -1     0     0
            //        block   2 : ordering C

        A Groebner basis of the cohomology ring's relation ideals
        is available as follows::

            sage: H.relation_ideal()
            b_1_0*c_3_6+c_2_3*b_1_0*c_1_1

        """
        if self.lastRelevantDeg:
            try:
                singular.eval('setring %sr(%d)'%(self.prefix,self.lastRelevantDeg))
                return
            except:
                self.reconstruct_singular()
                singular.eval('setring %sr(%d)'%(self.prefix,self.lastRelevantDeg))
        return

    def autosave_name(self):
        """
        Return the default file name for saving ``self``.

        NOTE:

        The default folder is in the current workspace.
        The file name is derived from the given group name.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_workspace(tmp)
            sage: X = CohomologyRing(720,763,prime=2)
            sage: G = libgap.SymmetricGroup(6)
            sage: Y = CohomologyRing(G,prime=2,GroupName='SymmetricGroup(6)', from_scratch=True)
            sage: X.autosave_name().startswith(tmp.replace('//','/'))
            True
            sage: X.autosave_name()
            '.../H720gp763mod2.sobj'
            sage: Y.autosave_name()
            '.../HSymmetricGroup_6_mod2.sobj'

        """
        return os.path.join(self.workspace, 'H'+self.GStem + 'mod%d.sobj'%self._prime)

    def group(self):
        """
        Return a permutation group equivalent to the one defining ``self``.

        NOTE:

        "Equivalent" means that mapping an initial segment of the list
        of generators results in a group isomorphism. It is cached. If
        GAP crashes, the group is reconstructed.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(720,763,prime=2)
            sage: G = X.group()
            sage: G
            Group([ (1,2), (1,2,3,4,5,6) ])
            sage: G is X.group()
            True

        """
        if self._gap_group is None:
            self._gap_group = gap.eval(self._gapBackup)
        return self._gap_group

    def sylow_subgroup(self):
        """
        Return the Sylow subgroup which is used to compute ``self``

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(1440,80,prime=2)
            sage: H.sylow_subgroup().IdGroup()
            [ 32, 3 ]
            sage: H.sylow_cohomology()
            H^*(SmallGroup(32,3); GF(2))
            sage: H.group().IsSubgroup(H.sylow_subgroup())
            true

        """
        if self._SylowGp is None:
            self._SylowGp = gap.eval(self._SylowGpBackup)
        return self._SylowGp

    def subgroup(self):
        """
        Return the subgroup to which the stable element method is applied.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(1440,80,prime=2)
            sage: H.subgroup().IdGroup()
            [ 288, 46 ]
            sage: H.subgroup_cohomology()
            H^*(SmallGroup(288,46); GF(2))
            sage: H.group().IsSubgroup(H.subgroup())
            true
            sage: H.subgroup().IsSubgroup(H.sylow_subgroup())
            true

        """
        try:
            self._Subgp._check_valid()
        except:
            self._Subgp = gap.eval(self._SubgpBackup)
        return self._Subgp

    def duflot_regular_sequence(self):
        """
        Return a Duflot regular sequence.

        NOTE:

        A Duflot regular sequence is a sequence of elements
        that restricts to a regular sequence in the cohomology
        of the greatest central elementary abelian subgroup
        of a Sylow subgroup. It is known that a Duflot regular
        sequence of length equal to the rank of the centre of
        a Sylow subgroup exists.

        A Duflot regular sequence is actually regular, but in
        general the length of a maximal regular sequence exceeds
        the length of a Duflot regular sequence.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(720,763,prime=2)
            sage: X.make()
            sage: X.duflot_regular_sequence()
            ['c_1_0', 'c_2_1']

        Actually, the cohomology ring is Cohen-Macaulay, hence,
        we have a regular sequence of length three::

            sage: X.filter_regular_parameters()
            ['c_1_0', 'c_2_1', 'b_3_3+c_3_2']
            sage: X.a_invariants()
            [-Infinity, -Infinity, -Infinity, -3]

        However, this regular sequence is not Duflot regular,
        because the restriction to the first special
        subgroup, which is the greatest central elementary
        abelian subgroup of the Sylow subgroup, does not form
        a regular sequence::

            sage: from pGroupCohomology.cohomology import is_filter_regular_parameter_system
            sage: r = X.restriction_maps()[1][1]
            sage: r
            Induced homomorphism of degree 0 from H^*(SmallGroup(720,763); GF(2)) to H^*(SmallGroup(4,2); GF(2))
            sage: rest = [r(X(p)).as_polynomial() for p in X.filter_regular_parameters()]; rest
            ['c_1_0', 'c_1_1^2', 'c_1_0*c_1_1^2']
            sage: singular(r.codomain()).set_ring()

        The fact that the annulator of the last parameter has dimension one in
        degrees zero and one means that the last parameter is filter regular,
        but not regular.

            sage: is_filter_regular_parameter_system('std(0)', rest)
            [[0], [0], [1, 1], [1, 1]]

        Often, a Duflot regular sequence can be formed by generators
        of the cohomology ring. Actually, to some extent this is how
        the generators are chosen. However, in general the Duflot
        regular elements returned by this method are not generators::

            sage: H = CohomologyRing(48,50, prime=2)
            sage: H.make()
            sage: H.duflot_regular_sequence()
            ['c_2_3', 'c_2_2', 'c_3_1', 'c_3_7+(c_3_0)']

        """
        return [t.name() for t in self._DuflotRegSeq]

    def sylow_cohomology(self):
        """
        Return the cohomology ring of a Sylow subgroup.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(1440,80,prime=2)
            sage: H.sylow_subgroup().IdGroup()
            [ 32, 3 ]
            sage: H.sylow_cohomology()
            H^*(SmallGroup(32,3); GF(2))

        """
        return self._HSyl

    def subgroup_cohomology(self):
        """
        Return the cohomology of the subgroup to which the stable element method is applied.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_workspace(tmp)
            sage: H = CohomologyRing(1440,80,prime=2)
            sage: H.subgroup().IdGroup()
            [ 288, 46 ]
            sage: H.subgroup_cohomology()
            H^*(SmallGroup(288,46); GF(2))
            sage: H.group().IsSubgroup(H.subgroup())
            true
            sage: H.subgroup().IsSubgroup(H.sylow_subgroup())
            true

        """
        return self._HP

######################################
# Methods to simplify computations
######################################

    def _simplifyMapData(self):
        """
        Remove redundant stability conditions.

        NOTE:

        This method will be automatically invoked when creating a modular
        cohomology ring of a non prime power group. We therefore give a
        rather artificial test.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(48,50, prime=2)
            sage: len(H.Cosets)
            2
            sage: H._PtoPcapCPtwist.extend(H._PtoPcapCPtwist)
            sage: H._PtoPcapCPdirect.extend(H._PtoPcapCPdirect)
            sage: H.Cosets.extend(H.Cosets)
            sage: len(H.Cosets)
            4
            sage: H._simplifyMapData()
            sage: len(H.Cosets)
            2

        """
        cdef int l = len(self._PtoPcapCPdirect)
        cdef int i
        IDList = []
        singular = self.GenS.parent()
        for i from 1 <= i <= l:
            singular(self._PtoPcapCPdirect[-i].codomain()).set_ring()
            if singular.eval('matrix(ideal(%s))==matrix(ideal(%s))'%(singular(self._PtoPcapCPdirect[-i]).name(),singular(self._PtoPcapCPtwist[-i]).name()))=='1':
                self._PtoPcapCPdirect[-i] = None
                self._PtoPcapCPtwist[-i] = None
                self.Cosets[-i] = None
            else:
                ID = (id(self._PtoPcapCPdirect[-i].codomain()), set([singular.eval('print(ideal(%s))'%singular(self._PtoPcapCPdirect[-i]).name()), singular.eval('print(ideal(%s))'%singular(self._PtoPcapCPtwist[-i]).name())]))
                if ID in IDList:
                    self._PtoPcapCPdirect[-i] = None
                    self._PtoPcapCPtwist[-i] = None
                    self.Cosets[-i] = None
                else:
                    IDList.append(ID)
        self._PtoPcapCPdirect = [X for X in self._PtoPcapCPdirect if X is not None]
        self._PtoPcapCPtwist = [X for X in self._PtoPcapCPtwist if X is not None]
        self.setprop('Cosets',[X for X in self.Cosets if X is not None])
        self._PtoPcapCPdirectSing = [singular(f) for f in self._PtoPcapCPdirect]
        self._PtoPcapCPtwistSing = [singular(f) for f in self._PtoPcapCPtwist]
        if len(self._PtoPcapCPdirect)<l:
            l = len(self._PtoPcapCPdirect)
            if l==1:
                coho_logger.info( "Only one map is relevant for stability", self)
            elif l==0:
                coho_logger.info( "No stability conditions - all elements are stable", self)
            else:
                coho_logger.info( "Only %d maps are relevant for stability", self, l)

    def _copy_from_subgroup(self):
        """
        Copy the ring structure from the cohomology of the underlying subgroup.

        NOTE:

        - If there are stability conditions, then nothing is done, since copying
          the ring structure only makes sense if all cocycles of the subgroup are
          stable.
        - This method is automatically invoked when a ring is created.

        TESTS:

        In this test, we make the program believe that there is no stability
        condition. The result is nonsense, but good for testing.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(48,50,prime=2)
            sage: len(H._PtoPcapCPdirect)
            2

        So, there are stability conditions. We compute the correct ring structure::

            sage: H.make()
            sage: len(H.Gen)
            12
            sage: len(H.Rel)
            35

        Now, we pretend that there is no stability condition, and copy from the subgroup.
        The result is nonsense, but indeed isomorphic to the cohomology of the subgroup.

            sage: H._PtoPcapCPdirect = []
            sage: H._copy_from_subgroup()
            sage: len(H.Gen)
            4
            sage: len(H.Rel)
            0
            sage: print(H._HP)
            Cohomology ring of Small Group number 14 of order 16 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_1_0: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
             c_1_2: 1-Cocycle in H^*(SmallGroup(16,14); GF(2)),
             c_1_3: 1-Cocycle in H^*(SmallGroup(16,14); GF(2))]
            Minimal list of algebraic relations:
            []
            sage: print(H)
            Cohomology ring of SmallGroup(48,50) with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_1_0: 1-Cocycle in H^*(SmallGroup(48,50); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(48,50); GF(2)),
             c_1_2: 1-Cocycle in H^*(SmallGroup(48,50); GF(2)),
             c_1_3: 1-Cocycle in H^*(SmallGroup(48,50); GF(2))]
            Minimal list of algebraic relations:
            []

        """
        if len(self._PtoPcapCPdirect):
            return
        if not self._HP.completed:
            raise RuntimeError("The cohomology ring of the underlying subgroup must be known")
        from pGroupCohomology.resolution import coho_options
        from pGroupCohomology.cochain import MODCOCH
        from pGroupCohomology import CohomologyRing
        _cache = CohomologyRing._cache
        coho_logger.info( "Copying ring structure from %r",self, self._HP)
        # self._prime must already be OK
        # MODCOCH and  string data
        singular = self._HP.GenS.parent()
        self._HP.set_ring() # needed?
        self.Gen = [MODCOCH(self,t.name(),deg=t.deg(),name=t.name(),rdeg=t.rdeg(),ydeg=t.ydeg(), S=singular, is_polyrep=True) for t in self._HP.Gen]
        self.degvec = [t.deg() for t in self.Gen]
        self.firstOdd = self._HP.firstOdd
        self.Rel = [t for t in self._HP.Rel]
        self.RelG= [t for t in self._HP.RelG]
        if isinstance(self._HP,MODCOHO):
            self.Dickson = [t for t in self._HP.Dickson]
        else:
            self.Dickson = [t.name() for t in self._HP.Gen if t.rdeg()]+[t for t in self._HP.Dickson]
        self.lastRel = self._HP.lastRel
        self.lastRelevantDeg = max(self.degvec+[self.lastRel])
        self.knownDeg = self._HP.knownDeg
        self.suffDeg = self._HP.suffDeg
        self.completed = True
        if self._HP._DuflotRegSeq:
            self._DuflotRegSeq = [MODCOCH(self,t.name(),deg=t.deg(),name=t.name(),rdeg=t.rdeg(),ydeg=t.ydeg(),S=singular, is_polyrep=True) for t in self._HP._DuflotRegSeq]
        else:
            self._DuflotRegSeq = [MODCOCH(self,t,name=t,rdeg=1,S=singular, is_polyrep=True) for t in self._HP.duflot_regular_sequence()]
        self.alpha = self._HP.alpha
        # GAP data don't need to be rebased (I think)
        # Singular data
        if self._HP.use_dp:
            self.setprop('use_dp',self._HP.use_dp)
            if len(self.degvec)==1:
                singular.eval('ring tmp = %d,(%s),%s'%(self._prime, ','.join([x.name() for x in self.Gen]), '(a(%d),dp)'%(self.degvec[0])))
            else:
                singular.eval('ring tmp = %d,(%s),%s'%(self._prime, ','.join([x.name() for x in self.Gen]), '(wp%s)'%(str(tuple(self.degvec)))))
        else:
            self.delprop('use_dp')
            self._makeOrderMatrix_()
            singular.eval('ring tmp = %d,(%s),M(%sM)'%(self._prime, ','.join([x.name() for x in self.Gen]), self.prefix))
        if self._prime!=2 and self.firstOdd<len(self.Gen):   # non-commutative case
            singular.eval('degBound = 0')
            singular.eval('def %sr(%d) = superCommutative(%d,%d)'%(self.prefix,self.lastRelevantDeg,self.firstOdd+1, len(self.Gen)))
        else:
            singular.eval('def %sr(%d) = tmp'%(self.prefix,self.lastRelevantDeg))
        self._HP.set_ring()
        SHP = singular('basering')
        has_DG = singular.eval('defined(%sDG)'%self._HP.prefix)
        self.set_ring()
        self.GenS = singular('basering')
        if self.RelG:
            singular.eval(('ideal %sI = '%self.prefix)+','.join(self.RelG))
        else:
            singular.eval('ideal %sI'%self.prefix)
        if has_DG=='1':
            singular.eval('ideal %sDG = imap(%s,%sDG)'%(self.prefix,SHP.name(),self._HP.prefix))
        else:
            singular.eval('ideal %sDG'%self.prefix)
        # we disregard the standard monomials. After all, it is
        # relatively cheap to reconstruct
        self.StdMon = {0:{'1':singular('1')}}
        if self._HP.fdt is not None:
            self.setprop('fdt',self._HP.fdt)
        if self._HP.completeGroebner is not None:
            self.setprop('completeGroebner',self._HP.completeGroebner)
        if self._HP.A_INV_Expos is not None:
            self.setprop('A_INV_Expos',self._HP.A_INV_Expos)
        from pGroupCohomology.resolution import coho_options
        if coho_options['save']:
            safe_save(self,self.autosave_name())

    # if the degree is too low, we won't lift the parameters. Hence,
    # no "@permanent_result"
    # But @temporary_result isn't good either: If the parameters do
    # lift then they can be kept.
    #@temporary_result
    def parameters_from_sylow_subgroup(self):
        """
        Try to obtain filter regular parameters from those of a Sylow subgroup.

        THEORY:

        In the case of a prime power group, a filter regular homogeneous
        system of parameters can be obtained by starting with the Duflot
        generators (they form a regular sequence) together with lifts of
        Dickson elements in the cohomology of maximal elementary abelian
        subgroups, restricted to a complement of the center.

        For non prime power groups, the situation is more difficult. We
        do find a Duflot regular sequence, but it is, in general, not
        formed by generators --- see :meth:`duflot_regular_sequence`.
        And in general, it is impossible to lift the Dickson elements
        restricted to a complement of the centre of the Sylow subgroup.
        Therefore, the default construction of a filter regular homogeneous
        system of parameters relies on the Dickson elements, without
        restriction.

        These may be of rather high degree. Therefore, we always try
        whether by chance the restricted Dickson elements found for
        the Sylow subgroup happen to be stable.  If only the last
        parameter can not be lifted,
        :meth:`~pGroupCohomology.cohomology.COHO.find_small_last_parameter`
        may help to find a filter regular homogeneous system of
        parameters in small degrees.

        EXAMPLE:

        Since the construction depends on data in the cohomology
        ring of a subgroup, we ensure that this ring is not simply
        taken from the local sources, and compute it from scratch::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(64,138,from_scratch=True)
            sage: H = CohomologyRing(576,204,prime=2)
            sage: H.make()

        In this example, all but the last parameter from the Sylow
        subgroup can be lifted. A last parameter can be easily found.
        Theorems imply that, we thus obtain a filter regular system
        of parameters, which we can verify::

            sage: P = H.parameters_from_sylow_subgroup(); P
            ['c_4_6',
             'b_1_0*b_3_0+b_1_0^4+b_2_2^2+b_2_0^2',
             'b_3_1*b_3_2+b_3_1^2+b_3_0^2+b_1_0^3*b_3_0+b_2_2*b_1_0*b_3_0+b_2_2^2*b_1_0^2+b_2_0*b_2_2^2+b_2_0^3+c_4_6*b_1_0^2',
             None]
            sage: P[-1] = H.find_small_last_parameter(P)
            sage: P
            ['c_4_6',
             'b_1_0*b_3_0+b_1_0^4+b_2_2^2+b_2_0^2',
             'b_3_1*b_3_2+b_3_1^2+b_3_0^2+b_1_0^3*b_3_0+b_2_2*b_1_0*b_3_0+b_2_2^2*b_1_0^2+b_2_0*b_2_2^2+b_2_0^3+c_4_6*b_1_0^2',
             'b_1_0']
            sage: H.raw_filter_degree_type(P)
            ([-1, -1, -1, 9, 11],
             [[0],
              [0],
              [0],
              [0, 0, 1, 3, 2, 4, 4, 2, 3, 1],
              [1, 0, 2, 4, 2, 5, 5, 2, 4, 2, 0, 1]],
             [4, 4, 6, 1])

        The degrees are 4, 4, 6, 1. The degrees of the original
        parameters, namely obtained by unrestricted Dickson
        elements, are 8, 12, 14, 15, the last Dickson element
        being replacable by a factor in degree 1::

            sage: H.find_dickson()
            True
            sage: H.Dickson
            ['b_1_0^2*b_3_0^2+b_1_0^8+b_2_2^4+b_2_0^4+c_4_6*b_1_0*b_3_0+b_2_2*c_4_6*b_1_0^2+c_4_6^2',
             'b_3_1^3*b_3_2+b_1_0^3*b_3_0^3+b_1_0^6*b_3_0^2+b_6_9*b_3_0^2+b_6_9^2+b_2_2*b_1_0*b_3_0^3+b_2_2*b_6_9*b_1_0*b_3_0+b_2_2^2*b_1_0^2*b_3_0^2+b_2_2^3*b_3_0^2+b_2_2^4*b_1_0^4+b_2_0^2*b_2_2^4+b_2_0^3*b_3_1^2+b_2_0^6+c_4_6*b_1_0^2*b_3_0^2+c_4_6*b_1_0^5*b_3_0+c_4_6*b_6_9*b_1_0^2+b_2_2*c_4_6*b_1_0^6+b_2_2^2*c_4_6*b_1_0*b_3_0+c_4_6^2*b_1_0*b_3_0+c_4_6^2*b_1_0^4+b_2_2^2*c_4_6^2+b_2_0^2*c_4_6^2',
             'b_1_0^5*b_3_0^3+b_6_9*b_1_0^2*b_3_0^2+b_6_9^2*b_1_0^2+b_2_2*b_1_0^3*b_3_0^3+b_2_2*b_6_9*b_1_0^3*b_3_0+b_2_2^2*b_1_0^4*b_3_0^2+b_2_2^3*b_1_0^2*b_3_0^2+c_4_6*b_1_0*b_3_0^3+c_4_6*b_1_0^4*b_3_0^2+c_4_6*b_6_9*b_1_0^4+c_4_6^2*b_3_1*b_3_2+c_4_6^2*b_3_1^2+c_4_6^2*b_3_0^2+b_2_2*c_4_6^2*b_1_0*b_3_0+b_2_2*c_4_6^2*b_1_0^4+b_2_2^2*c_4_6^2*b_1_0^2+b_2_0*b_2_2^2*c_4_6^2+b_2_0^3*c_4_6^2+c_4_6^3*b_1_0^2',
             'b_1_0']

        """
        if self._params_from_sylow is not None:
            OUT = [t for t in self._params_from_sylow]
            return OUT
        if len(self._DuflotRegSeq)<(self.PCenterRk or self.pRank):
            return None
        HS = self._HSyl
        singular = self.GenS.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        HS.set_ring()
        try:
            if self.knownDeg < max([int(singular.eval('deg(%s)'%p)) for p in HS.Dickson if p is not None] or [0]):
                return None
            if br is not None:
                br.set_ring()
            coho_logger.info( "Trying to lift the parameters of %r",self, HS)
            from pGroupCohomology.cochain import MODCOCH
            D = [self.small_factor(self.stable_to_polynomial(MODCOCH(HS,t,name=t,S=self.GenS.parent(), is_polyrep=True), verify=True)) if t is not None else None for t in HS.Dickson]
            if D.count(None)==1:
                coho_logger.info( "One parameter could not be lifted", self)
            elif D.count(None)==0:
                coho_logger.info( "All parameters could be lifted", self)
            else:
                coho_logger.info("%d parameters could not be lifted",self, D.count(None))
            self.setprop('_params_from_sylow',[t.name() for t in self._DuflotRegSeq]+D)
            return [t.name() for t in self._DuflotRegSeq]+D
        finally:
            try:
                br.set_ring()
            except:
                pass

    #################################
    #
    # The mathematical essence:
    # Computation of Stable Elements
    #
    #################################


##     ## The following methods are pretty fast, but (partially due to bugs in Singular)
##     ## require too much memory.
##     def _mon_image(self,mon,i):
##         "difference of images of monomial mon (string) under i-th maps"
##         singular = self.GenS.parent()
##         if singular.eval('defined(basering)')=='1':
##             br = singular('basering')
##         else:
##             br = None
##         if self._mon_images1 is None:
##             self._mon_images1 = {}
##             self._mon_images2 = {}
##             for j in range(len(self._PtoPcapCPdirect)):
##                 self._mon_images1[j]={}
##                 self._mon_images2[j]={}
##                 singular(self._PtoPcapCPdirect[j].codomain()).set_ring()
##                 for k in range(len(self._HP.Gen)):
##                     self._mon_images1[j][self._HP.Gen[k].name()] = self._PtoPcapCPdirectSing[j][k+1]
##                     self._mon_images2[j][self._HP.Gen[k].name()] = self._PtoPcapCPtwistSing[j][k+1]
##         if self._mon_images1[i].has_key(mon):
##             if br is not None:
##                 br.set_ring()
##             return self._mon_images1[i][mon], self._mon_images2[i][mon]
##         if '*' in mon:
##             mon1,mon2 = mon.split('*',1)
##             ind1 = self._mon_image(mon1,i)
##             ind2 = self._mon_image(mon2,i)
##             singular(self._PtoPcapCPdirect[i].codomain()).set_ring()
##             self._mon_images1[i][mon] = singular('NF(%s*%s,std(0))'%(ind1[0].name(),ind2[0].name()))
##             self._mon_images2[i][mon] = singular('NF(%s*%s,std(0))'%(ind1[1].name(),ind2[1].name()))
##             if br is not None:
##                 br.set_ring()
##             return self._mon_images1[i][mon], self._mon_images2[i][mon]
##         else:
##             mon1,d = mon.split('^')
##             if d=='1':
##                 return self._mon_images1[i][mon1], self._mon_images2[i][mon1]
##             if d=='2':
##                 ind1 = self._mon_image(mon1,i)
##                 singular(self._PtoPcapCPdirect[i].codomain()).set_ring()
##                 self._mon_images1[i][mon] = singular('NF(%s^2,std(0))'%ind1[0].name())
##                 self._mon_images2[i][mon] = singular('NF(%s^2,std(0))'%ind1[1].name())
##                 if br is not None:
##                     br.set_ring()
##                 return self._mon_images1[i][mon], self._mon_images2[i][mon]
##             d1 = int(d)/2
##             d2 = int(d)-d1
##             ind1 = self._mon_image(mon1+'^%d'%d1,i)
##             ind2 = self._mon_image(mon1+'^%d'%d2,i)
##             singular(self._PtoPcapCPdirect[i].codomain()).set_ring()
##             self._mon_images1[i][mon] = singular('NF(%s*%s,std(0))'%(ind1[0].name(),ind2[0].name()))
##             self._mon_images2[i][mon] = singular('NF(%s*%s,std(0))'%(ind1[1].name(),ind2[1].name()))
##             if br is not None:
##                 br.set_ring()
##             return self._mon_images1[i][mon], self._mon_images2[i][mon]

##     def __stable_space(self, int n):
##         """
##         return a basis for the subspace of stable elements in self._HP of degree `n`.

##         OUTPUT:
##         - a list of cochains (:class:`~pGroupCohomology.cochain.MODCOCH`),
##           that form a basis for the space of stable elements
##         - a list of standard monomials of the underlying cohomology ring
##           of a subgroup
##         - a list of those standard monomials of the underlying cohomology
##           ring of a subgroup that occur as leading monomials of stable
##           elements

##         """
##         cdef int i,j,l,m,k,nr,a,b
##         from sage.all import get_memory_usage
##         singular = self.GenS.parent()
##         cdef int SizePieces
##         try:
##             SizePieces = min(max(int(coho_options.get('SingularCutoff',50)*(get_memory_usage()*1024*512)/int(singular.eval
## ('memory(2)'))),2),100)
##         except: # may happen on non-linux non-osx
##             SizePieces = coho_options.get('SingularCutoff',50)
##         print "SizePieces =", SizePieces

##         # standard monomials for the Sylow subgroup
##         coho_logger.info("Determining stable subspace in degree %d"%n, self)
##         self._HP._makeStdMon(n,"%sMon"%self.prefix)
##         self._HP.set_ring()
##         rHP = singular('basering')
##         singular.eval('%sMon=sort(%sMon)[1]'%(self.prefix,self.prefix))
##         cdef list Monomials = [singular.eval("print(%sMon[%d])"%(self.prefix,i)).strip() for i in range(1,int(singular.eval('size(%sMon)'%self.prefix))+1)] # stable and unstable monomials
##         # = singular.eval("print(%sMon)"%self.prefix).split(',\n') # stable and unstable monomials
##         cdef list MonExp
##         cdef dict tmpD
##         cdef list tmpL
##         l = len(self._PtoPcapCPdirect)

##         m = len(Monomials)
##         if m==0:
##             return [],[],[]

##         # Shipping the monomials to the quotient ring, so that we can map them
##         # There is a memory leak in Singular when mapping ideals, so, we
##         # do it with polys
##         singular(self._HP).set_ring()
##         if m>1:
##             singular.eval('poly %sP(1..%d) = imap(%s,%sMon)'%(self.prefix, m, rHP.name(), self.prefix))
##         else:
##             singular.eval('poly %sP(1) = imap(%s,%sMon)[1]'%(self.prefix, rHP.name(), self.prefix))
##         #print "P start"
##         #print singular.eval('%sP(1..%d)'%(self.prefix,m))
##         coho_logger.info('> found %d monomials for the Sylow subgroup'%m, self)

##         cdef list L, Restr, Mon, Coefs, Terms, NegTerms
##         cdef dict SubgpMonomials = {} # will be a dictionary COHO._key -> monomial dictionary

##         cdef int maxSubgpGen = 0
##         # Go through all monomials of self._HP, apply the direct and twisted induced maps, express
##         # their difference as a polynomial, and read off a list from it.
##         # 1. ideal formed by the images
##         if singular.eval('defined(%s_i)'%self.prefix)=='0':
##             singular.eval('int %s_i'%self.prefix)
##         for i from 0 <= i < l: #f in self._PtoPcapCPdirect:
##             f = self._PtoPcapCPdirect[i]
##             if len(f.codomain().Gen)>maxSubgpGen:
##                 maxSubgpGen=len(f.codomain().Gen)
##         # We construct a ring that comprises everything, so that we can determine the
##         # stable space by elimination
##         r = singular.ring(self._prime,'(@t(1..%d),@x(1..%d))'%(maxSubgpGen,l),'dp')
##         maxI = singular('maxideal(1)')
##         rQP = singular(self._HP)
##         self._HP.set_ring()
##         rP = singular('basering')
##         R = r+rP
##         R.set_ring()
##         I = singular('imap(%s,%sMon)'%(rHP.name(),self.prefix))
##         #print I
##         for i from 0 <= i < l: # subgps distinguished by @x(i+1)
##             coho_logger.info("Conjugator isomorphism %d"%i, self)
##             for j from 0<= j < m:
##                 im1,im2 = self._mon_image(Monomials[j],i)
##                 rname = singular(self._PtoPcapCPdirect[i].codomain()).name()
##                 singular.eval('%s[%d]=%s[%d]+@x(%d)*(fetch(%s,%s)-fetch(%s,%s))'%(I.name(),j+1,I.name(),j+1,i+1,rname,im1.name(),rname,im2.name()))

##         # determine stable elements by elimination.
##         # Those that don't have '@' in them are stable; note that we
##         # rely on tthe fact that in the cohomology rings no variable
##         # name contains '@'
##         coho_logger.info("> Extracting the stable subspace",self)
##         singular.eval('%s=interred(%s)'%(I.name(),I.name())) # this should be sorted -- hopefully it is...
##         maxI = singular('imap(%s,%s)'%(r.name(),maxI.name()))
##         singular.eval('for (%s_i=ncols(%s);%s_i>0;%s_i--){ if (NF(%s[%s_i],%s)<>%s[%s_i]){%s[%s_i]=0;}}'%(self.prefix,I.name(),self.prefix,self.prefix, I.name(),self.prefix,maxI.name(),I.name(),self.prefix, I.name(),self.prefix))
##         k = int(singular.eval('ncols(%s)'%I.name()))

##         singular(self._HP).set_ring()
##         if singular.eval('defined(%sMon)'%self.prefix)=='0':
##             singular.eval('ideal %sMon=NF(imap(%s,%s),std(0))'%(self.prefix,R.name(),I.name()))
##         else:
##             singular.eval('%sMon=NF(imap(%s,%s),std(0))'%(self.prefix,R.name(),I.name()))
##         cdef list OUT = []
##         cdef list Pivots = []
##         from pGroupCohomology.cochain import MODCOCH
##         for i from 1<=i<=k:
##             if singular.eval('%sMon[%d]==0'%(self.prefix,i))!='1': # it is stable:
##                 OUT.append(MODCOCH(self, singular('%sMon[%d]'%(self.prefix,i)), deg=n, name='Gen%d'%i, is_NF=True))
##                 Pivots.append(singular.eval('leadmonom(%sMon[%d])'%(self.prefix,i)))
##         singular.eval('kill %sMon'%(self.prefix))
##         singular.eval('kill %s_i'%self.prefix)
##         # Monomials and %sMon are ascendingly sorted. We want them descendingly.
##         Monomials.reverse()
##         OUT.reverse()
##         Pivots.reverse()
##         return OUT, Monomials, Pivots

##     def _stable_space(self, int n):
##         """
##         return a basis for the subspace of stable elements in self._HP of degree `n`.

##         OUTPUT:

##         - a list of cochains (:class:`~pGroupCohomology.cochain.MODCOCH`),
##           that form a basis for the space of stable elements
##         - a list of standard monomials of the underlying cohomology ring
##           of a subgroup
##         - a list of those standard monomials of the underlying cohomology
##           ring of a subgroup that occur as leading monomials of stable
##           elements

##         """
##         cdef int i,j,l,m,k,nr,a,b
##         if self._totalRing is None:
##             self._make_mapper()
##         from sage.all import get_memory_usage
##         singular = self.GenS.parent()
##         #cdef int SizePieces
##         #try:
##         #    SizePieces = min(max(int(coho_options.get('SingularCutoff',50)*(get_memory_usage()*1024*512)/int(singular.eval('memory(2)'))),2),100)
##         #except: # may happen on non-linux non-osx
##         #    SizePieces = coho_options.get('SingularCutoff',50)
##         #print "SizePieces =", SizePieces

##         # standard monomials for the Sylow subgroup
##         coho_logger.info("Determining stable subspace in degree %d"%n, self)
##         self._HP._makeStdMon(n,"%sMon"%self.prefix)
##         self._HP.set_ring()
##         rHP = singular('basering')
##         singular.eval('%sMon=sort(%sMon)[1]'%(self.prefix,self.prefix))
##         cdef list Monomials = [singular.eval("print(%sMon[%d])"%(self.prefix,i)).strip() for i in range(1,int(singular.eval('size(%sMon)'%self.prefix))+1)] # stable and unstable monomials
##         l = len(self._PtoPcapCPdirect)
##         m = len(Monomials)
##         if m==0:
##             return [],[],[]
##         coho_logger.info('> found %d monomials for the Sylow subgroup, that are now to be mapped'%m, self)
##         Ring = self._totalRing+rHP
##         self._totalRing.set_ring()
##         MonI = singular('NF(ideal(matrix(fetch(%s,%sMon))*(@s(1)-@s(2))*sum(@g(1..%d))),%sMapper)'%(rHP.name(),self.prefix,l,self.prefix))
##         singular.eval('%s=NF(%s,std(ideal(@s(1)-1,@s(2)-1)))'%(MonI.name(),MonI.name()))
##         Ring.set_ring()
##         MonI = singular('ideal(matrix(fetch(%s,%s))+matrix(imap(%s,%sMon)))'%(self._totalRing.name(),MonI.name(),rHP.name(),self.prefix))

##         # determine stable elements by elimination.
##         # Those that don't have '@' in them are stable; note that we
##         # rely on tthe fact that in the cohomology rings no variable
##         # name contains '@'
##         coho_logger.info("> Extracting the stable subspace", self)
##         singular.eval('%s=interred(%s)'%(MonI.name(),MonI.name())) # this should be sorted -- hopefully it is...
##         maxI = singular('ideal(@g(1..%d))'%l)
##         singular.eval('int %s_i'%self.prefix)
##         singular.eval('for (%s_i=ncols(%s);%s_i>0;%s_i--){ if (NF(%s[%s_i],%s)<>%s[%s_i]){%s[%s_i]=0;}}'%(self.prefix,MonI.name(),self.prefix,self.prefix, MonI.name(),self.prefix,maxI.name(),MonI.name(),self.prefix, MonI.name(),self.prefix))
##         k = int(singular.eval('ncols(%s)'%MonI.name()))

##         singular(self._HP).set_ring()
##         if singular.eval('defined(%sMon)'%self.prefix)=='0':
##             singular.eval('ideal %sMon=NF(imap(%s,%s),std(0))'%(self.prefix,Ring.name(),MonI.name()))
##         else:
##             singular.eval('%sMon=NF(imap(%s,%s),std(0))'%(self.prefix,Ring.name(),MonI.name()))
##         cdef list OUT = []
##         cdef list Pivots = []
##         from pGroupCohomology.cochain import MODCOCH
##         for i from 1<=i<=k:
##             if singular.eval('%sMon[%d]==0'%(self.prefix,i))!='1': # it is stable:
##                 OUT.append(MODCOCH(self, singular('%sMon[%d]'%(self.prefix,i)), deg=n, name='Gen%d'%i, is_NF=True))
##                 Pivots.append(singular.eval('leadmonom(%sMon[%d])'%(self.prefix,i)))
##         singular.eval('kill %s_i'%self.prefix)
##         # Monomials and %sMon are ascendingly sorted. We want them descendingly.
##         Monomials.reverse()
##         OUT.reverse()
##         Pivots.reverse()
##         return OUT, Monomials, Pivots

    def stable_space(self, int n):
        """
        return a basis for the subspace of stable cocycles of the underlying subgroup in a given degree.

        INPUT:

        ``n``, the degree (integer)

        OUTPUT:

        - a list of elements (:class:`~pGroupCohomology.cochain.MODCOCH`) of ``self``
          whose restriction to the underlying subgroup yield a basis for the space
          of stable elements in degree ``n``.
        - a list of standard monomials of the underlying cohomology ring
          of a subgroup
        - a list of those standard monomials of the underlying cohomology
          ring of a subgroup that occur as leading monomials of stable
          elements

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.MathieuGroup(11)
            sage: H = CohomologyRing(G,prime=2,GroupName='M11', from_scratch=True)

        It may easily be that there are no stable cocycles in a given degree::

            sage: H.stable_space(1)
            ([], [], [])
            sage: H.stable_space(2)
            ([], [], [])

        The first stable element, yielding the first generator of ``H``, can
        be found in degree 3::

            sage: g,M,MS = H.stable_space(3)
            sage: g
            [Gen1: 3-Cocycle in H^*(M11; GF(2))]
            sage: M
            ['b_3_0', 'b_1_0^3']
            sage: M == H._HP.standard_monomials(3)
            True
            sage: g[0].val_str()
            'b_3_0'

        Here, the stable element of ``H._HP`` happens to be a monomial. This is
        not always the case::

            sage: g,M,MS = H.stable_space(4)
            sage: g[0].val_str()
            'b_1_0^4+c_4_2'
            sage: MS
            ['b_1_0^4']

        """
        cdef int i,j,l,m,k,nr,a,b
        cdef int SizePieces = coho_options.get('SingularCutoff',50)

        # standard monomials for the Sylow subgroup
        coho_logger.info( "Determining stable subspace in degree %d",self, n)
        singular = self.GenS.parent()
        self._HP._makeStdMon(n,"%sMon"%self.prefix)
        self._HP.set_ring()
        RHP = singular('basering')
        singular.eval('%sMon=sort(%sMon)[1]'%(self.prefix,self.prefix))
        cdef list Monomials = [singular.eval("print(%sMon[%d])"%(self.prefix,i)).strip() for i in range(1,int(singular.eval('size(%sMon)'%self.prefix))+1)] # stable and unstable monomials
        cdef list MonExp
        cdef dict tmpD
        cdef list tmpL
        l = len(self._PtoPcapCPdirect)
        if l:
            try:
                self._PtoPcapCPdirectSing[0]._check_valid()
            except:
                self._simplifyMapData()
        m = len(Monomials)

        # shipping the monomials to the quotient ring, so that we can map it
        if m==0:
            return [],[],[]
        singular(self._HP).set_ring()
        if m>1:
            singular.eval('poly %sP(1..%d) = imap(%s,%sMon)'%(self.prefix, m, RHP.name(), self.prefix))
        else:
            singular.eval('poly %sP(1) = imap(%s,%sMon)[1]'%(self.prefix, RHP.name(), self.prefix))
        singular.eval('ideal %sMon=imap(%s,%sMon)'%(self.prefix, RHP.name(), self.prefix))
        coho_logger.debug( '> found %d monomials for the subgroup', self,m)
        cdef list L, Restr, Mon, Coefs, Differences, Terms, NegTerms, tmpL1, tmpL2
        cdef dict SubgpMonomials = {} # will be a dictionary COHO._key -> monomial dictionary

        # Go through all monomials of self._HP, apply the direct and twisted induced maps, express
        # their difference as a polynomial, and read off a list from it.
        # 1. get strings from the differences that have been computed above
        Differences = []
        SubgpMonomials[self._HP._key] = dict(zip(Monomials, [j for j in range(len(Monomials))]))
        for i from 0 <= i < l:
            f = self._PtoPcapCPdirect[i]
            fd = self._PtoPcapCPtwist[i]
            if not f.codomain()._key in SubgpMonomials:
                f.codomain()._makeStdMon(n,"%sMon"%f.codomain().prefix)
                f.codomain().set_ring()
                L = [singular.eval('print(%sMon[%d])'%(f.codomain().prefix,k)).strip() for k in range(1,int(singular.eval('size(%sMon)'%f.codomain().prefix))+1)]
                SubgpMonomials[f.codomain()._key] = dict(zip(L, [j for j in range(len(L))]))
                singular.eval('kill %sMon'%f.codomain().prefix)
            coho_logger.debug( "> Considering conjugator isomorphism %d"%i, self)
            singular(f.codomain()).set_ring()
            # The following is working around a memory leak in Singular
            # and a bug in the Singular interface
            tmpP = singular.poly(0)
            tmpL2 = []
            for k from 1<=k<=m:
                tmpL1=[]
                singular.eval('%s=NF(%s(%sP(%d))-%s(%sP(%d)),std(0))'%(tmpP.name(),self._PtoPcapCPdirectSing[i].name(),self.prefix,k, self._PtoPcapCPtwistSing[i].name(),self.prefix,k))
                a = int(singular.eval('size(%s)'%tmpP.name()))
                nr = int(a/SizePieces)
                for j from 0<=j<nr:
                    tmpL1.append(singular.eval('print(%s[%d..%d])'%(tmpP.name(),j*SizePieces+1,(j+1)*SizePieces)).strip())
                if nr*SizePieces<a:
                    tmpL1.append(singular.eval('print(%s[%d..%d])'%(tmpP.name(),nr*SizePieces+1,a)).strip())
                tmpL2.append(tmpL1)
            Differences.append(tmpL2)


        for f in self._PtoPcapCPdirect:
            if f.codomain() is not self._HP:
                f.codomain().set_ring()
                if singular.eval('defined(%sMon)'%f.codomain().prefix)=='1':
                    singular.eval('kill %sMon'%f.codomain().prefix)

        singular(self._HP).set_ring()
        coho_logger.info( "Setting up conditions to determine stable elements", self)
        Restr = []
        for j from 0 <= j < m:
            Restr.append([])
            for i from 0 <= i < l:
                f = self._PtoPcapCPdirect[i]
                tmpD = SubgpMonomials[f.codomain()._key]
                L = len(tmpD.keys())*[0]
                Coefs = []
                Mon = []
                tmpL1 = Differences[i][j]
                for p in tmpL1:
                    NegTerms = p.split('-')
                    Terms = NegTerms.pop(0).split('+')
                    if Terms == ['']:
                        Terms = []
                    while NegTerms:
                        Terms.extend( ('-' + NegTerms.pop(0)).split('+'))
                    if Terms!=['0']:
                        while Terms:
                            tm = Terms.pop(0)
                            if (tm[0]=='-'):
                                if tm[1].isdigit():
                                    cf,mn = tm.split('*',1)
                                else:
                                    cf = -1
                                    mn = tm[1:]
                            else:
                                if tm[0].isdigit():
                                    cf,mn = tm.split('*',1)
                                else:
                                    cf = 1
                                    mn = tm
                            Coefs.append(int(cf))
                            Mon.append(mn)
                k = len(Mon)
                for nr from 0 <= nr < k:
                    try:
                        L[tmpD[Mon[nr]]] = Coefs[nr]
                    except:
                        raise
                Restr[-1].extend(L)
        coho_logger.info( "Solving equations", self)
        if Restr and Restr[0]:
            M = new_mtx(MatNullSpace__(rawMatrix(self._prime, Restr)), None)
        else:
            M = new_mtx(MatId(self._prime, len(Monomials)), None)
        if M.nrows():
            L = [M._rowlist_(i) for i in range(M.nrows())]
        else:
            return [],[],[]
        # Create MODCOCH instances, which avoids lifting of cocycles and
        # and computation of higher terms of the resolution of self._HP
        # Use '%sMon'%self.prefix!
        singular(self._HP).set_ring()
        if singular.eval('defined(%stmpI)'%self.prefix)=='0':
            singular.eval('ideal %stmpI'%self.prefix)
        else:
            singular.eval('%stmpI=ideal(0)'%self.prefix)
        cdef list OUT = []
        from pGroupCohomology.cochain import MODCOCH
        l = len(L)
        singular.eval('%stmpI[%d]=0'%(self.prefix,l))
        for j from 0 < j <= l:
            Coefs = L[j-1]
            for i from 0 <= i < m:
                if Coefs[i]!=0:
                    singular.eval('%stmpI[%d]=%d*%sP(%d)+%stmpI[%d]'%(self.prefix, j, Coefs[i], self.prefix, i+1, self.prefix, j))
        singular.eval('kill %sP(1..%d)'%(self.prefix,m))

        singular.eval('%stmpI=sort(%stmpI)[1]'%(self.prefix,self.prefix))
        # interreduction does not work in quotient rings. Hence, we must go through the "proper" basering of self_HP
        self._HP.set_ring()
        tmpBR = singular('basering')
        tmpI = singular('imap(%s,%stmpI)'%(singular(self._HP).name(),self.prefix))
        singular.eval('%s=NF(%s,%sI)'%(tmpI.name(),tmpI.name(),self._HP.prefix))
        singular.eval('%s=interred(%s)'%(tmpI.name(),tmpI.name()))
        singular(self._HP).set_ring()
        singular.eval('%stmpI=imap(%s,%s)'%(self.prefix,tmpBR.name(),tmpI.name()))
        l = int(singular.eval('size(%stmpI)'%self.prefix))+1
        OUT = [MODCOCH(self, singular('%stmpI[%d]'%(self.prefix,i)), deg=n, name='Gen%d'%i, is_NF=True) for i in range(1,l)]
        OUT.reverse()
        Pivots = [t.strip() for t in singular.eval('print(normalize(lead(%stmpI)))'%self.prefix).split(',')]
        Pivots.reverse()
        singular.eval('kill %stmpI'%self.prefix)
        Monomials.reverse()
        return OUT, Monomials, Pivots


    ################################
    # Ingredients for Benson's test
    ################################

    def dickson_in_subgroup(self, id): # since self.CenterRk=0, we have the *full* Dickson invariants
        """
        Compute Dickson classes for an elementary abelian group, considered as subgroup of the group of ``self``.

        INPUT:

        - ``id``: the small groups address (pair of integers) of some
          elementary abelian subgroup of self

        OUTPUT:

        Let `G` be the finite group whose cohomology ring ``self``
        represents. The attribute ``subgbDickson`` of self is changed
        and contains elements of degree `p^{r}-p^{r-i}` of the
        cohomology ring of the elementary abelian group `V` described
        by ``id``, where `r` is the `p`-rank of `G`, and `i =
        1,...,r`.  These elements are constructed using Dickson
        invariants in the polynomial part of the cohomology of `V`.

        NOTE:

        For the completeness criteria we are using, it is essential to
        construct homogeneous systems of parameters for the ring
        approximation that give rise to parameters of the cohomology
        ring. Using simultaneous lifts of (powers of) the Dickson
        elements in the special subgroups found with
        dickson_in_subgroup, one can even find a hsop that is filter
        regular. However, if `p^{r}-p^{r-i}` is too large, one should
        use :meth:`~pGroupCohomology.cohomology.COHO.find_dickson`,
        that avoids the construction of elements of high degrees.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(162,19,prime=3)
            sage: sorted(H.subgroups().items())
            [((3, 1), H^*(SmallGroup(3,1); GF(3))),
             ((9, 2), H^*(SmallGroup(9,2); GF(3))),
             ((27, 5), H^*(SmallGroup(27,5); GF(3)))]
            sage: H.dickson_in_subgroup((9,2))
            sage: H.dickson_in_subgroup((27,5))
            sage: sorted(H.subgpDickson.items())
            [((9, 2),
              [D_0: 36-Cocycle in H^*(SmallGroup(9,2); GF(3)),
               D_1: 48-Cocycle in H^*(SmallGroup(9,2); GF(3)),
               D_2: 52-Cocycle in H^*(SmallGroup(9,2); GF(3))]),
             ((27, 5),
              [D_0: 36-Cocycle in H^*(SmallGroup(27,5); GF(3)),
               D_1: 48-Cocycle in H^*(SmallGroup(27,5); GF(3)),
               D_2: 52-Cocycle in H^*(SmallGroup(27,5); GF(3))])]

        """
        G = self.subgps[id]
        if G.knownDeg<2:
            G.make()
        if self.subgpDickson is None:
            self.subgpDickson = {}
        p = self._prime
        r = self.pRank
        z = self.CenterRk
        if p%2:
            sgprank = len(G.Gen)/2
        else:
            sgprank = len(G.Gen)
        t = sgprank - z
        if t<0:
            raise RuntimeError("The p-rank of the center must not exceed the rank of a maximal elementary abelian subgroup")
        if t==0:
            return
        coho_logger.info("Computing Dickson invariants in elementary abelian subgroup of rank %d"%sgprank, self)

        # construct the Dickson invariants in the qring of the special subgroup
        singular(G._HP or G).set_ring()
        if singular.eval('defined(tmp_i)')=='0':
            singular.eval('int tmp_i')
        if singular.eval('defined(%sDI)'%self.prefix)=='0':
            singular.eval('ideal %sDI'%(self.prefix))
            singular.eval('for (tmp_i=%d;tmp_i>=1;tmp_i--) { %sDI[tmp_i] = Delta(%d,%d,%d,tmp_i); }'%(r-z,self.prefix,r,z,t))
        singular.eval('kill tmp_i')
        from pGroupCohomology.cochain import MODCOCH
        self.subgpDickson[id] = [MODCOCH(G, singular('%sDI[%d]'%(self.prefix,k+1)), deg=(p**(r-z)-p**(r-z-k-1))*(2 if p%2 else 1), name='D_%d'%k) for k in range(r-z)]
        tmp = [t.val_str() for t in self.subgpDickson[id]] # supports data reconstruction after crash

    def InitSubgroups(self):
        """
        Initialize data that are related with `p`-elementary abelian subgroups.

        NOTE:

        This method should only be of internal use.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(48,50,prime=2, from_scratch=True)

        We destroy the subgroup information...
        ::

            sage: H.subgps = None
            sage: H.subg = None

        ... and reconstruct it::

            sage: H.InitSubgroups()
            sage: sorted(H.subgpDickson.items())
            [((16, 14),
              [D_0: 8-Cocycle in H^*(SmallGroup(16,14); GF(2)),
               D_1: 12-Cocycle in H^*(SmallGroup(16,14); GF(2)),
               D_2: 14-Cocycle in H^*(SmallGroup(16,14); GF(2)),
               D_3: 15-Cocycle in H^*(SmallGroup(16,14); GF(2))])]
            sage: sorted(H.subgps.items())
            [((16, 14), H^*(SmallGroup(16,14); GF(2)))]

        """
        coho_logger.info( "Initialising subgroups", self)
        cdef ChMap Map, Tmp
        gap = self._Subgp.parent()
        if self._HP.PCenterRk: # this should only be the case for MODCOHO
            self.PCenterRk = self._HP.PCenterRk
        else:
            self.PCenterRk = self._HP.CenterRk # self._HP is COHO
        if self.PCenterRk is None: # the underlying group is abelian
            Syl = self._HP.group().SylowSubgroup(self._prime)
            self.pRank = CenterRk = int(Syl.RankPGroup())
            # Construct the maximal p-elementary abelian group in self._Subgp
            ExpL = Syl.GeneratorsOfGroup().List(gap.Order).sage()[:CenterRk]
               # = gap('List(GeneratorsOfGroup(%s),Order)'%Syl.name()).sage()[:CenterRk]
            SylGens = Syl.GeneratorsOfGroup()
            V = gap.Group([SylGens[i]**(ExpL[i]/self._prime) for i in range(CenterRk)])
            phi = V.GroupHomomorphismByImages(self._HP.group(), V.GeneratorsOfGroup(), V.GeneratorsOfGroup())
            q = self._prime**CenterRk
            n = Integer(gap.eval('NumberSmallGroups(%d)'%q))
            HV = CohomologyRing(q,n)
            if not HV.completed:
                HV.make()
            self.subgps = {(q,n): HV}
            self.RestrMaps = { 1 : [(q,n), self.hom(self._HP.hom(phi,HV).G_map(), HV)] }
            self.MaxelPos = [1]
            self.MaxelRk = [CenterRk]
            self.CElPos = 1
        else:
            self._HP.reconstructSubgroups()
            self.MaxelPos = self._HP.MaxelPos
            self.MaxelRk = self._HP.MaxelRk
            self.pRank = self._HP.pRank
            self.CElPos = self._HP.CElPos
            self.RestrMaps = {}
            self.subgps = self._HP.subgps
            for i,L in self._HP.RestrMaps.items():
                Map = L[1]
                Tmp = self.hom(Map.G_map(),Map.codomain())
                Tmp.Data = [Map[j] for j in range(Map.knownDeg()+1)]
                self.RestrMaps[i] = [L[0], Tmp]

        self.CenterRk = 0  # cohomology.pyx knows: CenterRk==0 means that we do not have a p-group
        if self.Dickson == [] or self.Dickson is None:
            self.Dickson = self.pRank*[None]
        #TODO: Heuristic to choose between elimination and linear algebra.
        # Probably elimination will be better -- since we must not modify
        # the Dickson classes (namely zero on the center of the Sylow subgroup)
        # the invariants are of very high degree.
        # On the other hand, if they are of high degree, then we will usually
        # have to reach very high degrees anyway, so, there is no harm in
        # lifting the Dickson elemnts on the fly
        if self.useElimination is None:
            if (1+(self._prime%2))*(self._prime**self.pRank) > 20:
                self.setprop('useElimination',True)
            else:
                self.setprop('useElimination',False)
        if not self.useElimination:
            for n in self.MaxelPos:
                self.dickson_in_subgroup(self.RestrMaps[n][0]) # since self.CenterRk=0, we have the *full* Dickson invariants
                # For p-groups, we could modify the Dickson invariants so that they vanish in the center.


    ###############################################################
    ##        Completion tests
    ###############################################################
    ## We use separate tests for generators and for relations

    def generator_degbound(self):
        """
        Find a bound for the degree of cohomology generators.

        THEORY:

        IF ``H`` is a modular cohomology ring of a non prime power group,
        computed as a sub-ring of ``H.subgroup_cohomology()``, then the latter
        is a finitely generated module over the former, via the restriction
        map. One can show that a minimal generating set of ``H`` has degrees
        bounded by the maximal degree of a module generator of
        ``H.subgroup_cohomology()``.

        OUTPUT:

        ``None``. Attributes ``degbound_for_gens`` (the currently found maximal
        possible degree of a generator) and ``all_generators_found`` (``True``,
        if there will be no further generators) are set, and there is some log.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.MathieuGroup(11)
            sage: H = CohomologyRing(G,prime=2,GroupName='M11', from_scratch=True)
            sage: H.make(4)
            sage: CohomologyRing.global_options('info')
            sage: H.generator_degbound()
            H^*(M11; GF(2)):
                      New generators will be found at most in degree 5
            sage: CohomologyRing.global_options('warn')
            sage: H.degbound_for_gens
            5
            sage: print(H.all_generators_found)
            None

        So, there may be further generators in degree 5. Indeed, there are::

            sage: H.make(5)
            sage: H.generator_degbound()
            sage: H.all_generators_found
            True
            sage: sorted(H.gens())
            [1,
             b_3_0: 3-Cocycle in H^*(M11; GF(2)),
             c_4_0: 4-Cocycle in H^*(M11; GF(2)),
             b_5_0: 5-Cocycle in H^*(M11; GF(2))]

        These are all generators, and completeness of the ring
        structure is proved in degree 10::

            sage: H.make()
            sage: H.knownDeg
            10
            sage: sorted(H.gens())
            [1,
             b_3_0: 3-Cocycle in H^*(M11; GF(2)),
             c_4_0: 4-Cocycle in H^*(M11; GF(2)),
             b_5_0: 5-Cocycle in H^*(M11; GF(2))]

        """
        if self.all_generators_found:
            return
        if self.degbound_for_gens:
            if self.knownDeg>=self.degbound_for_gens:
                self.setprop('all_generators_found',True)
                return
            coho_logger.info("New generators will be found at most in degree %d"%(self.degbound_for_gens), self)
            return
        if len(self._DuflotRegSeq) < (self.PCenterRk or self.pRank):
            return
        coho_logger.info( "Try to find a bound for the degree of generators", self)
        L = [singular(t.as_cocycle_in_subgroup()) for t in self.Gen]
        if not L:
            coho_logger.info("> No degree bound available, yet", self)
            return
        try:
            br = singular('basering')
        except TypeError:
            br = None
        singular(self._HP).set_ring()
        try:
            I = singular.ideal(L).groebner()
            if singular.eval('vdim(%s)'%I.name()) == '-1':
                br.set_ring()
                return
            m = max([Integer(singular.eval('deg(%s)'%t.name())) for t in I.kbase()])
            br.set_ring()
            self.setprop('degbound_for_gens', m)
            if self.knownDeg>=m:
                coho_logger.info("> The generating set is complete", self)
                self.setprop('all_generators_found',True)
            else:
                coho_logger.info( "> New generators will be found at most in degree %d"%(m), self)
        finally:
            try:
                br.set_ring()
            except:
                pass

    def test_for_completion(self,forced = False):
        """
        Perform completion tests.

        OUTPUT:

        ``True`` (complete), ``False`` (incomplete), ``None`` (can't be decided yet)
        The attribute ``completed`` is set accordingly.

        NOTE:

        This method first invokes
        :meth:`~pGroupCohomology.modular_cohomology.MODCOHO.generator_degbound`
        to test whether all generators are known. If this is the case, the
        last degree of relations is estimated.  Eventually, either
        :meth:`~pGroupCohomology.cohomology.COHO.SymondsTest` or
        :meth:`~pGroupCohomology.modular_cohomology.MODCOHO.HilbertPoincareTest`
        is called.

        EXAMPLES:

        This example shows what happens behind the scenes when ``H.make()``
        is called. We use ``MathieuGroup(11)``.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.MathieuGroup(11)
            sage: H = CohomologyRing(G,prime=2,GroupName='M11', from_scratch=True)
            sage: H.make(3)
            sage: H.test_for_completion()
            False

        The reason is that there is no maximal Duflot regular sequence yet::

            sage: H.duflot_regular_sequence()
            []

        So, we proceed to degree 4::

            sage: H.next()
            sage: H.duflot_regular_sequence()
            ['c_4_0']

        We have a Duflot regular sequence, but it is possible that there are
        more generators in degree 5::

            sage: CohomologyRing.global_options('info')
            sage: H.test_for_completion()
            H^*(M11; GF(2)): Try to find a bound for the degree of generators
                    > New generators will be found at most in degree 5
            False

        In degree 5, it turns out that parameters can be found. But,
        since we expect a relation at least in degree 10, the
        completion criterion is still not invoked. However, there
        are now nice filter regular parameters::

            sage: CohomologyRing.global_options('warn')
            sage: H.next()
            sage: CohomologyRing.global_options('info')
            sage: H.test_for_completion()
            H^*(M11; GF(2)): We expect a relation in degree at least 10
            sage: H.filter_regular_parameters()
                      Compute filter_regular_parameters
                      Trying to lift the parameters of H^*(SD16; GF(2))
            H^*(SmallGroup(48,29); GF(2)):
                      Exploring relations in degree 1
                      Determine degree 1 standard monomials
                      Express 1 standard monomial as cocycle
                      Found 0 relations in degree 1
            H^*(M11; GF(2)):
                      One parameter could not be lifted
                      Testing whether parameters of the cohomology ring can be found
                      > Yes
                      Compute find_small_last_parameter
                      Computing complete Groebner basis
                      Compute _parameter_restrictions
            Induced homomorphism of degree 0 from H^*(M11; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                      Compute restricted parameters
            H^*(M11; GF(2)):
                      Compute _get_obvious_parameter
                      Compute _parameter_restrictions
                      compute radicals of restricted parameter ideal
                      Compute _parameter_restrictions
            Induced homomorphism of degree 0 from H^*(M11; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                      Compute restricted parameters
            H^*(M11; GF(2)):
                      Determine degree 1 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 2 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 3 standard monomials
                      --> Last parameter found in degree 3
            ['c_4_0', 'b_3_0']

        We continue out to degree 10, and then test again. In this
        case, the Symonds criterion is chosen for the test::

            sage: CohomologyRing.global_options('warn')
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: CohomologyRing.global_options('info')
            sage: H.test_for_completion()
            H^*(M11; GF(2)):
                      Compute dependent_parameters
                      Try to find a set of generators over which the cohomology ring is finite.
                      Computing complete Groebner basis
                      Trying Symonds' criterion
                      Successful application of the Symonds criterion
            True
            sage: CohomologyRing.global_options('warn')
            sage: H.completed
            True

        In the following example, it occurs that the ring approximation out
        to degree 10 does contain elements that give rise to parameters for the
        cohomology ring::

            sage: H = CohomologyRing(864*2,206,prime=2)
            sage: H.make(10)
            sage: H.verify_parameters_exist()
            True
            sage: H.dependent_parameters()
            ['b_1_0', 'c_6_13', 'c_4_5', 'c_2_1']


        But the dependent parameters of the ring approximation are not enough
        to apply the Symonds criterion::

            sage: H.SymondsTest(H.dependent_parameters(), [1,6,6,4,2]) is None
            True

        In fact, it turns out that the simultaneous lifts of Dickson
        invariants, that are guaranteed to yield parameters of the cohomology
        ring, are not parameters of the ring approximation::

            sage: H.find_dickson()
            True
            sage: H.Dickson
            ['...b_1_0^8+...',
             '...c_4_5^2*b_1_0^4+...',
             '...c_2_1*c_6_12^2+...',
             'b_1_0']
            sage: H.set_ring()
            sage: singular.ideal(H.Dickson+H.rels()).groebner().dim() > 0
            True

        we can find smaller elements that are guaranteed to yield parameters
        of the complete cohomology ring, but of course the ring approximation
        is not complete yet::

            sage: H.parameters()
            ['c_2_1', 'c_4_5', 'c_6_13', 'b_1_0']
            sage: H.test_for_completion()
            False

        It turns out that the last relation is in fact found in degree 12, and
        then of course the complete cohomology ring is finite over both the
        elements obtained from the Dickson invariants and the system of
        parameters in smaller degrees::

            sage: H.make()
            sage: H.last_interesting_degree()
            12
            sage: H.rels()[-1]
            '...c_6_12^2+...'
            sage: H.parameters()
            ['c_2_1', 'c_4_5', 'c_6_13', 'b_1_0']
            sage: H.set_ring()
            sage: singular.ideal(H.Dickson+H.rels()).groebner().dim()
            0
            sage: singular.ideal(H.parameters()+H.rels()).groebner().dim()
            0

        """
        if self.suffDeg>-1 and self.knownDeg >= self.suffDeg:
            self.completed=True
            return True
        self.generator_degbound()
        if not self.all_generators_found:
            return False
        if (self.expect_last_relation() > self.knownDeg) and not forced:
            coho_logger.info("We expect a relation in degree at least %d"%self.expect_last_relation(), self)
            return
        #########
        ## try Symonds' criterion first: It is particularly good
        ## when "easy" parameters can be found.
        DepPars = self.dependent_parameters()
        if DepPars is None:
            coho_logger.info("The ring approximation does not contain parameters for the complete ring.", self)
            return False
        self.set_ring()
        Depdv = [Integer(singular.eval("deg(%s)"%(x))) for x in DepPars]  # this is the real degree vector
        if sum([t-1 for t in Depdv]) < self.knownDeg:
            Pars = DepPars
            dv = Depdv
            Symonds = self.SymondsTest(Pars,dv, forced = forced)
            if Symonds:
                coho_logger.info("Successful application of the Symonds criterion", self)
                self.completed = True
                self.setprop('_parameters_for_criterion',[t for t in Pars])
                self.setprop('_method','Symonds')
                return True
            elif Symonds is False:
                coho_logger.info("The parameters are no parameters for the ring approximation, which is thus incomplete.", self)
                return False
            coho_logger.info("The Symonds criterion is inconclusive.", self)
        else:
            coho_logger.info("We found parameters, but they would not allow for an application of Symonds' criterion.", self)
            # The following has been removed, as in the case of non-prime-power groups, it is
            # typically a lot easier to compute the ring structure to a very high degree than to
            # try and find a way to prove completeness in a very low degree.
#~             coho_logger.info("Trying to find better parameters in a more costly way.", self)
#~             try:
#~                 Pars = self.parameters()
#~             except ValueError:
#~                 # This is just to be on the safe side. There can only be a value error if the
#~                 # cohomology ring approximation has no generator.
#~                 coho_logger.info("The approximation is incomplete (no parameters found).", self)
#~                 return False
            #########
#~             if Pars is None:
#~                 # This probably can not happen.
#~                 Pars = DepPars
#~             if Pars is None:
#~                 coho_logger.info("The ring approximation does not contain parameters for the complete ring.", self)
#~                 return False
#~             self.set_ring()
#~             dv = [Integer(singular.eval("deg(%s)"%(x))) for x in Pars]  # this is the real degree vector
#~             if sum([t-1 for t in dv]) > sum([t-1 for t in Depdv]):
#~                 Pars = DepPars
#~                 dv = Depdv

        #########
        ## There may still be the chance to use an existence proof!
        self.set_ring()
        try:
            HilbertPoincare = self.HilbertPoincareTest(forced=forced)
        except KeyboardInterrupt:
            coho_logger.warning("The Hilbert-Poincare completion test was interrupted.", self)
            HilbertPoincare=None
        if HilbertPoincare:
            coho_logger.info("Successful application of the Hilbert-Poincare criterion", self)
            self.completed = True
            self.setprop('_final_parameters',[t for t in self.filter_regular_parameters()])
            self.setprop('_method','Hilbert-Poincar&eacute;')
        elif HilbertPoincare is None:
            coho_logger.info("No conclusion on the completeness of this cohomology ring.", self)
        elif HilbertPoincare is False:
            coho_logger.info("By the Hilbert-Poincare test, the ring is incomplete.", self)
        return HilbertPoincare # which is none if the existence proof was not good enough

    @temporary_result
    def parameter_degrees_over_field_extension(self, forced=False):
        r"""
        Returns the degrees of parameters over a field extension.

        INPUT:

        - forced: If True then the cache is overridden.

        OUTPUT:

        - A tuple of integers providing the degrees of a homogeneous system
          of algebraically independent parameters that exist when replacing
          the base field of this cohomology ring by a finite field extension.
        - An integer, providing a lower bound for the depth of this cohomology
          ring.
        - A bool, which is True if an existence proof was used, and False if
          the parameters have actually been constructed without extending the
          base field.

        Three times None is returned, if no parameters could be found.

        TODO:

        Find a better example! Here, we do parts of the quest for parameters
        in a non-automatic way. This is to get a good example, in which it is
        possible to benefit from an existence proof of parameters over a
        finite extension field. However, the automatically chosen parameters
        happen to be good enough, so that an application of Symonds'
        completeness criterion, without using an existence proof, is the
        easiest way to prove completeness.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(384,5602, prime=2, from_scratch=True)

        In the following line, we are cheating a bit. Without it, other
        parameters would be found for `H`. ::

            sage: H.sylow_cohomology().find_dickson()
            True
            sage: H.make(3)

        The degree is too low, hence, no parameters can be found::

            sage: H.parameter_degrees_over_field_extension()
            (None, None, None)

        After computing out to degree six, parameters in degrees
        4, 6, 1 and 4 can be explicitly constructed::

            sage: H.make(6)
            sage: H.parameters()
            ['b_1_1^4+b_1_0^3*b_1_1+b_1_0^4+b_2_4*b_1_1^2+b_2_4*b_1_0^2+b_2_4^2+b_2_3^2',
             'b_3_9^2+b_3_1^2+b_1_0*b_1_1^2*b_3_1+b_1_0^6+b_2_4*b_1_0*b_3_1+b_2_4*b_1_0*b_3_0+b_2_4*b_1_0*b_1_1^3+b_2_4*b_1_0^4+b_2_4^2*b_1_1^2+b_2_4^3+b_2_3*b_2_4^2+b_2_3^2*b_2_4',
             'b_1_1+b_1_0',
             'c_4_15']

        But it can be shown that there exists a field extension over
        which there exist parameters in smaller degrees::

            sage: H.sylow_cohomology().depth()
            3
            sage: H.parameter_degrees_over_field_extension()
            ((4, 1, 4, 3), 3, True)

        These return values tell us that there is a finite field extension
        over which there exists parameters in degrees 4, 1, 4, 3,
        that the depth of the cohomology ring is at least three (which is the
        depth of the cohomology ring of a Sylow 2-subgroup), and that such low
        parameter degrees seem impossible to achieve without extending the base
        field. By the Hilbert-Poincaré criterion, we may hope to prove completeness
        of the ring presentation in degree `4+1+4+3-3`, hence, in degree 9. This
        is indeed possible::

            sage: H.make()
            sage: H.knownDeg
            9
            sage: H._method
            'Hilbert-Poincar&eacute;'
            sage: CohomologyRing.set_local_sources(False)

        """
        # Prove the existence of parameters over a finite field extension.
        # This is for application of the Hilbert-Poincare criterion. Hence,
        # we stop the search if a sufficiently small bound has been found.
        # Returns a tuple of degrees.
        if not self.verify_parameters_exist():
            return None,None,None
        # It is impossible that the Hilbert-Poincare criterion
        # is better than the Symonds criterion using dependent
        # parameters: These are subsets of generators, hence,
        # can't be improved by our existence proof.
        # We thus start with algebraically independent parameters.
        # Since we assume that all generators are found, the following
        # parameters for the ring *approximation* give rise to
        # parameters for the whole ring.
        try:
            br = singular('basering')
        except TypeError:
            br = None
        try:
            D = self._HP._lower_bound_depth()
            if isinstance(D,list):
                D = D[0]
                self.set_ring()
            hsop = self.parameters_from_sylow_subgroup()
            try:
                if (hsop is None) or (hsop.count(None)>1):
                    hsop = self.parameters(forced=forced)
                    if hsop is None and self.find_dickson():
                        hsop = self.parameters(forced=self.last_interesting_degree()==self.knownDeg)
            except KeyboardInterrupt,msg:
                coho_logger.warning("The existence proof of parameters over a field extension has been interrupted.", self)
                return None,None,None

            # At this point, it should be impossible that hsop is None.
            # To be on the safe side:
            if hsop is None:
                coho_logger.info("There should be parameters, but apparently it is too difficult to find them.", self)
                return None, None, None
            try:
                hsop[-1] = self.find_small_last_parameter(hsop, self.knownDeg)
            except KeyboardInterrupt:
                pass # hence, we may use suboptimal parameters
            self.make_groebner()
            self.set_ring()
            dv = [Infinity if t is None else Integer(singular.eval('deg(%s)'%t)) for t in hsop]
            ## try to prove that there are smaller parameters
            ## over a finite field extension.
            dgb = singular.eval('degBound')
            singular.eval('degBound=0')
            I = singular(self.prefix+'I')
            Hit = []
            # We will prove the existence of parameters at most out to this degree:
            maxd = min(max(dv), self.knownDeg)
            sumd = sum(dv)
            datapairs = zip(hsop,dv)
            # This is the bound that we will get without existence proof.
            optimalbound = sumd - D
            if optimalbound <= self.knownDeg:
                return tuple(dv), D, False # False means: Existence proof hasn't been used.
            hsopdata = (hsop,0)
            for subpairs in subsets(datapairs):
                if (None,Infinity) not in subpairs:
                    J = singular(I.name())
                    new_sumd = -D
                    for x,y in subpairs:
                        singular.eval('%s=std(%s,%s)'%(J.name(),J.name(),x))
                        new_sumd += y
                    nb_further_params = len(datapairs)-len(subpairs)
                    for n in range(1,maxd):
                        # Would we improve the degree bound by finding
                        # parameters in degree n?
                        if new_sumd + n*nb_further_params < optimalbound:
                            self._makeStdMon(n,self.prefix+'Mon')
                            if singular('vdim(std(%s,%sMon))'%(J.name(),self.prefix))!=-1:
                                optimalbound = new_sumd + n*nb_further_params
                                hsopdata = (subpairs,n)
                                break
                        if optimalbound <= self.knownDeg:
                            break
            singular.eval('degBound='+dgb)
            if hsopdata[1]:
                return tuple([y for x,y in hsopdata[0]]+[hsopdata[1]]*(len(hsop)-len(hsopdata[0]))), D, True
            return tuple(dv), D, False
        finally:
            try:
                br.set_ring()
            except:
                pass

    def HilbertPoincareTest(self, forced=None):
        r"""
        Try to prove completeness of the ring structure using the Poincaré series.

        OUTPUT:

        ``True``, ``False`` or ``None``, depending on whether the
        Hilbert-Poincaré criterion proves completeness or incompleteness of
        the ring approximation or was not conclusive.

        ASSUMPTION:

        The generating set is already complete.

        THEORY:

        If the cohomology ring has depth at least `D` and has a homogeneous
        system of parameters of degrees `d_1,...,d_r` , and if the current
        approximation of the cohomology ring has a complete generating set
        and is known at least out to degree `\sum d_i-D`, then the
        approximation is complete if and only if its Poincaré series
        multiplied by `\prod (1-t^{d_i})` is a polynomial of degree at
        most `\sum d_i-D`. See [King]_ for more details.

        EXAMPLES:

        We compute a cohmology ring step by step, in order to demonstrate what
        happens behind the scenes when launching :meth:`make`. Be aware that this
        is *not* recommended. ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(384, 5602, prime=2, from_scratch=True)

        In the following line, we are cheating a bit: Without it, other
        parameters would be found for `H`. ::

            sage: H.sylow_cohomology().find_dickson()
            True
            sage: H.make(4)

        In the current ring approximation, a degree bound for the generators
        was determined by :meth:`generator_degbound` and stored in
        some attribute. Apparently, all generators have been found::

            sage: H.degbound_for_gens
            4
            sage: H.all_generators_found
            True
            sage: H.degvec
            [2, 2, 4, 1, 1, 3, 3, 3]

        We did not bother to find filter regular parameters yet::

            sage: H.filter_regular_parameters()

        Indeed, we expect a relation in degree 6::

            sage: H.expect_last_relation()
            6

        Nevertheless, it is possible to find filter regular parameters for the
        cohomology ring in this approximation. Again, this function would not
        be called in an automatic computation, thus resulting in different
        parameters::

            sage: H.find_dickson()
            True
            sage: H.filter_regular_parameters()
            ['b_1_1^2*b_3_1^2+...',
             'b_3_9^4+...',
             'b_1_1^2*b_3_1^4+...',
             'b_1_0^3*b_3_0^2*b_3_1^2+...']

        So, they live in degrees 4, 12, 14 and 15. It would be possible to find
        a last filter-regular parameter in degree 1, but that would still not
        allow to apply the Benson criterion. When we invest considerably
        more time, we could find algebraically independent (but not necessarily
        filter-regular) parameters in much smaller degrees 4, 12, 2 and 1,
        by calling ::

            sage: H.parameters()                    # not tested
            ['b_1_1^4+b_1_0^3*b_1_1+b_1_0^4+b_2_4*b_1_1^2+b_2_4*b_1_0^2+b_2_4^2+b_2_3^2+c_4_15',
             'b_3_9^4+b_3_1^4+b_3_0^4+b_1_1^6*b_3_1^2+b_1_0^2*b_1_1^4*b_3_1^2+b_1_0^3*b_3_0^2*b_3_1+b_1_0^4*b_1_1^8+b_1_0^6*b_3_1^2+b_1_0^6*b_3_0*b_3_1+b_1_0^6*b_3_0^2+b_1_0^8*b_1_1^4+b_2_4*b_1_0^4*b_3_0*b_3_1+b_2_4*b_1_0^7*b_3_1+b_2_4^2*b_1_1^2*b_3_1^2+b_2_4^2*b_1_0^2*b_3_0^2+b_2_4^2*b_1_0^2*b_1_1^6+b_2_4^2*b_1_0^8+b_2_4^4*b_1_1^4+b_2_4^4*b_1_0^2*b_1_1^2+b_2_4^4*b_1_0^4+b_2_3*b_1_0^4*b_3_0^2+b_2_3*b_2_4*b_1_0^5*b_3_0+b_2_3^2*b_1_0^2*b_3_0^2+b_2_3^4*b_1_0^4+c_4_15*b_1_1^2*b_3_1^2+c_4_15*b_1_1^5*b_3_1+c_4_15*b_1_0*b_1_1^4*b_3_1+c_4_15*b_1_0*b_1_1^7+c_4_15*b_1_0^2*b_3_1^2+c_4_15*b_1_0^5*b_3_0+b_2_4*c_4_15*b_1_1^3*b_3_1+b_2_4*c_4_15*b_1_1^6+b_2_4*c_4_15*b_1_0*b_1_1^5+b_2_4*c_4_15*b_1_0^2*b_1_1*b_3_1+b_2_4^2*c_4_15*b_1_1*b_3_1+b_2_4^2*c_4_15*b_1_0*b_3_0+b_2_4^3*c_4_15*b_1_1^2+b_2_4^3*c_4_15*b_1_0*b_1_1+b_2_3*c_4_15*b_1_0^3*b_3_0+b_2_3*b_2_4*c_4_15*b_1_0^4+b_2_3^2*c_4_15*b_1_0*b_3_0+b_2_3^3*c_4_15*b_1_0^2+c_4_15^2*b_1_1*b_3_1+c_4_15^2*b_1_0*b_3_0+c_4_15^2*b_1_0^4+b_2_4*c_4_15^2*b_1_0*b_1_1+b_2_4*c_4_15^2*b_1_0^2+b_2_4^2*c_4_15^2+b_2_3^2*c_4_15^2',
             'b_2_4+b_2_3',
             'b_1_1+b_1_0']

        However, all the above effort was in vain (that's why we removed that test),
        as The Poincaré series shows that the approximation cannot be complete:
        The Poincaré series' denominator does not divide `(1-t^{4})(1-t^{12})(1-t^{2})(1-t)`,
        where the exponents are given by the degrees of the above set of algebraically
        independent parameters::

            sage: p = H.poincare_series()
            sage: t = p.parent().gen()
            sage: (p*(1-t^4)*(1-t^12)*(1-t^2)*(1-t)).denominator().monic()
            t^6 - 2*t^3 + 1

        Let us continue the computation step by step. Of course, normally we
        would just do ``H.make()`` instead. ::

            sage: H.next()
            sage: H.next()
            sage: H.knownDeg
            6

        The parameters found above are of high degrees, and hence it seems
        hopeless to apply any of our criteria with them. But we do find
        algebraically dependent parameters in relatively small degrees::

            sage: H.dependent_parameters()
            ['b_1_0', 'b_1_1', 'c_4_15', 'b_3_1', 'b_3_9', 'b_2_3', 'b_2_4']


        With these parameters, the Symonds criterion (see :meth:`SymondsTest`)
        has a chance to apply in degrees strictly greater than `0 + 0 + 3 + 2
        + 2 + 1 + 1 = 9`. However, in this example we could do better, with the
        Hilbert\--Poincaré criterion and an existence proof of parameters over
        a finite extension field. Again, since the test would take a very
        long time, we remove it from our test suite. ::

            sage: H.parameter_degrees_over_field_extension()    # not tested
            ((4, 2, 1, 3), 3, True)

        This would indeed take so long that in practical computations one would
        be better off to apply an easier completeness criterion in higher degree
        see below.

        Anyway, there is a finite extension field over which there is some hsop
        in degrees 4, 2, 1, and 3, the depth of the cohomology ring is at
        least three, and our heuristics did not find parameters in these
        degrees, *i.e.*, we use an existence result of parameters over a
        finite extension field. Since `4 + 2 + 1 + 3 - 3 = 7`, we still can not
        prove completeness of the current degree six ring approximation, and thus
        compute the next degree. In order to avoid automatic application of a
        completeness criterion, we use the method :meth:`next`. There are no further
        relations in degree 7, but finally the Poincaré series satisfies the
        condition of the completeness criterion::

            sage: H.next()
            sage: H.knownDeg
            7
            sage: H.last_interesting_degree()
            6
            sage: p = H.poincare_series()
            sage: (p*(1-t^4)*(1-t^2)*(1-t)*(1-t^3)).denominator()
            1
            sage: H.knownDeg > (p*(1-t^4)*(1-t^2)*(1-t)*(1-t^3)).numerator().degree()
            True

        Thus the Hilbert\--Poincaré criterion proves the completeness of the
        ring approximation, using parameters (over an extension field) in
        degrees 4, 2, 1, and 3.

        It should be noted that the above example was rather artificial and
        does *not* show how one should compute a cohomology ring. So, in a last
        step, we compute the same ring again from scratch using the default
        algorithms. ::

            sage: CohomologyRing.doctest_setup()
            sage: Hdefault = CohomologyRing(384, 5602, prime=2, from_scratch=True)
            sage: Hdefault.make()
            sage: H == Hdefault
            True
            sage: Hdefault._method      # indirect doctest
            'Hilbert-Poincar&eacute;'
            sage: H.knownDeg
            7
            sage: Hdefault.knownDeg
            9

        The default way of computation verifies completeness only in degree 9,
        whereas our manual computation succeeded in degree 7. Nonetheless, the
        default computations is a lot faster, since the time spent to compute
        better parameters outweighs the time spent to compute two additional
        degrees of the ring structure. Interestingly, our heuristics to compute
        algebraically independent parameters can provide better parameters when
        using default algorithms, and is faster::

            sage: Hdefault.parameters()
            ['c_4_15',
             'b_1_0^2+b_2_4+b_2_3',
             'b_3_9+b_3_1+b_3_0+b_2_4*b_1_0',
             'b_1_1+b_1_0']

        """
        coho_logger.info("Trying the Hilbert-Poincare criterion", self)
        dv, D, use_existence_proof = self.parameter_degrees_over_field_extension()
        if dv is None:
            coho_logger.info("No parameters were found, the ring approximation is incomplete.", self)
            return False
        optimalbound = sum(dv) - D
        if self.knownDeg<optimalbound:
            if optimalbound<Infinity:
                coho_logger.info("We expect that the Hilbert-Poincare criterion will not apply before degree %d"%optimalbound, self)
                return
            coho_logger.info("No parameters were found, the ring approximation is incomplete.", self)
            return False
        p = self._poincare_without_parameters()
        R = p.parent()
        t = R.gen(0)
        denom = R(1)
        for e in dv:
            denom = denom*(1-t**e)
        numer = p*denom
        if hasattr(numer.denominator(),'degree') and numer.denominator().degree():
            coho_logger.info( "There will be further relations", self)
            return False
        if numer.numerator().degree()<=optimalbound:
            self.suffDeg = optimalbound
            self.setprop('POINCARE',p)
            # now, we have the optimal bound, or one that is sufficiently good
            if use_existence_proof:
                self.setprop('WhatHSOP',[repr(t) for t in dv])
            return True
        coho_logger.info( "There will be further relations", self)
        return False

    def _construct_fr_parameters(self):
        """
        Try to construct reasonably small filter regular parameters.

        OUTPUT:

        ``True`` or ``False``, if parameters can be found or not.
        The attribute ``_current_parameters`` is assigned to a list
        of parameters (given by strings).
fi
        NOTE:

        This is an auxiliary function for
        :meth:`~pGroupCohomology.cohomology.COHO.filter_regular_parameters`
        and should not be called directly.

        EXAMPLES:

        Since the construction depends on the cohomology ring of
        a subgroup, we compute it from scratch, in order to have
        a well defined behaviour in this doctest::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(81,7, from_scratch=True)
            sage: X.make()
            sage: H = CohomologyRing(324,39, prime=3, from_scratch=True)
            sage: H.make(12)

        Dickson invariants in a complement of the centre of a Sylow 3-subgroup
        are of degrees 12 and 16. Since we know ``H`` only out to degree 12,
        the degree 16 parameter is not available yet. But actually it
        has not been computed for the subgroup either::

            sage: H.sylow_cohomology().Dickson
            ['b_4_6^3-b_2_2^2*b_4_6^2-b_2_2^6-b_2_0^6+b_2_2^3*c_6_11', None]

        The degree 12 parameter for the cohomology of the Sylow subgroup
        is actually stable, i.e., yields an element of ``H``, so that
        a Duflot regular element together with this element and a yet
        to determine last parameter will form a filter regular hsop::

            sage: H.parameters_from_sylow_subgroup()
            ['c_12_7', 'b_4_2^3-b_4_1*b_8_4+b_4_1^3+b_4_0^2*b_4_1-b_4_0^3', None]

        .. TODO::

            A previous version of our heuristics to find parameters was able to
            find a parameter in degree 4 that extends the above sequence. The new
            heuristics can not find it, but succeeds in many other examples. Try
            to find a heuristics that combines the advantages of both approaches!

        When we now construct filter regular parameters, the first few
        parameters are in much higher degree than needed::

            sage: CohomologyRing.global_options('info')
            sage: H._construct_fr_parameters()
            H^*(SmallGroup(324,39); GF(3)):
                      Testing whether parameters of the cohomology ring can be found
                      > Yes
                      Compute find_small_last_parameter
                      Computing complete Groebner basis
                      Compute _parameter_restrictions
            Induced homomorphism of degree 0 from H^*(SmallGroup(324,39); GF(3)) to H^*(SmallGroup(9,2); GF(3)):
                      Compute restricted parameters
            Induced homomorphism of degree 0 from H^*(SmallGroup(324,39); GF(3)) to H^*(SmallGroup(27,5); GF(3)):
                      Compute restricted parameters
            H^*(SmallGroup(324,39); GF(3)):
                      Compute _get_obvious_parameter
                      Compute _parameter_restrictions
            Induced homomorphism of degree 0 from H^*(SmallGroup(324,39); GF(3)) to H^*(SmallGroup(9,2); GF(3)):
                      Compute restricted parameters
            Induced homomorphism of degree 0 from H^*(SmallGroup(324,39); GF(3)) to H^*(SmallGroup(27,5); GF(3)):
                      Compute restricted parameters
            H^*(SmallGroup(324,39); GF(3)):
                      Determine degree 1 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 2 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 3 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 4 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 5 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 6 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 7 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 8 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 9 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 10 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 11 standard monomials
                      Compute _get_obvious_parameter
                      Determine degree 12 standard monomials
                      The given last parameter could not be improved
                      Compute find_dickson
                      Try to lift Dickson invariants using elimination methods
                      Lift Dickson invariants of the 2nd special subgroup
            H^*(SmallGroup(9,2); GF(3)):
                      Compute nil_radical
                      Compute order_matrix
            H^*(SmallGroup(324,39); GF(3)):
                      Compute order_matrix
            Induced homomorphism of degree 0 from H^*(SmallGroup(324,39); GF(3)) to H^*(SmallGroup(9,2); GF(3)):
                      Compute preimages by elimination
            H^*(SmallGroup(324,39); GF(3)):
                      Lift Dickson invariants of the 3rd special subgroup
            H^*(SmallGroup(27,5); GF(3)):
                      Compute nil_radical
                      Compute order_matrix
            Induced homomorphism of degree 0 from H^*(SmallGroup(324,39); GF(3)) to H^*(SmallGroup(27,5); GF(3)):
                      Compute preimages by elimination
            H^*(SmallGroup(324,39); GF(3)):
                      Factorising an element; it can be interrupted with Ctrl-c
                      Factorising an element; it can be interrupted with Ctrl-c
                      Factorising an element; it can be interrupted with Ctrl-c
                      We succeeded to lift Dickson invariants!
            True
            sage: CohomologyRing.global_options('warn')
            sage: P1 = H._current_parameters; P1
            ['b_4_2^9+b_4_1^9+b_4_0^6*b_4_1^3-b_4_0^9-b_4_1^4*b_8_4*c_12_7+b_4_0*b_4_1^3*b_8_4*c_12_7-b_4_0^2*b_4_1^2*b_8_4*c_12_7+b_4_0^2*b_4_1^4*c_12_7+b_4_0^3*b_4_1^3*c_12_7+b_4_0^4*b_4_1^2*c_12_7+b_4_1*b_8_4*c_12_7^2+b_4_1^3*c_12_7^2-b_4_0*b_4_1^2*c_12_7^2+b_4_0^2*b_4_1*c_12_7^2+c_12_7^3',
             'b_4_0^6*b_4_1^6-b_4_0^9*b_4_1^3-b_4_1^7*b_8_4*c_12_7+b_4_0*b_4_1^6*b_8_4*c_12_7+b_4_0^2*b_4_1^5*b_8_4*c_12_7+b_4_0^2*b_4_1^7*c_12_7+b_4_0^3*b_4_1^6*c_12_7-b_4_0^4*b_4_1^5*c_12_7+b_4_0^5*b_4_1^2*b_8_4*c_12_7-b_4_0^7*b_4_1^2*c_12_7+b_4_1^6*c_12_7^2+b_4_0*b_4_1^3*b_8_4*c_12_7^2+b_4_0*b_4_1^5*c_12_7^2-b_4_0^3*b_4_1*b_8_4*c_12_7^2+b_4_0^3*b_4_1^3*c_12_7^2-b_4_0^4*b_4_1^2*c_12_7^2-b_4_0^5*b_4_1*c_12_7^2+b_4_2^3*c_12_7^3-b_4_1*b_8_4*c_12_7^3+b_4_0^2*b_4_1*c_12_7^3-b_4_0^3*c_12_7^3',
             'b_4_1']

        These elements of degrees 36, 24 and 4 are not parameters of the
        current approximation, though::

            sage: H.set_ring()
            sage: I = H.relation_ideal()
            sage: singular.eval('degBound=0')
            ''
            sage: (I+singular.ideal(H.parameters())).groebner().GKdim()
            2

        But they *are* filter regular parameters for the complete cohomology ring,
        as we will verify below. The ring approximation is thus incomplete, and
        in fact We expect relations in degree at least 22::

            sage: H.expect_last_relation()
            22

        We thus compute out to degree 22.
        ::

            sage: H.make(22)

        Indeed, we find that the above sequence ``P1`` is filter regular::

            sage: H.raw_filter_degree_type(P1)
            ([-1, -1, 79, 85],
             [[0], [0], [0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 2, 1, 0, 1, 3, 2, 0, 1, 3, 2, 0, 2, 4, 2, 0, 2, 5, 3, 0, 2, 5, 3, 0, 3, 6, 3, 0, 3, 6, 3, 0, 3, 6, 3, 0, 3, 6, 3, 0, 3, 5, 2, 0, 3, 5, 2, 0, 2, 4, 2, 0, 2, 3, 1, 0, 2, 3, 1, 0, 1, 2, 1, 0, 1, 1, 0, 0, 1, 1], [1, 0, 0, 3, 2, 0, 2, 5, 3, 1, 5, 8, 4, 1, 7, 11, 5, 2, 9, 13, 6, 3, 12, 16, 7, 3, 14, 19, 8, 4, 16, 21, 9, 5, 19, 24, 9, 5, 21, 24, 9, 6, 21, 24, 9, 6, 21, 24, 8, 6, 21, 21, 7, 6, 19, 19, 6, 5, 16, 16, 5, 5, 14, 13, 4, 4, 12, 11, 3, 3, 9, 8, 2, 3, 7, 5, 1, 2, 5, 3, 0, 1, 2, 0, 0, 1]],
             [36, 48, 4])

        Note that now, as the ring structure is completely known, we are
        able to find filter regular parameters in very low degrees, which
        we couldn't before knowing that the ring structure is complete::

            sage: P2 = H.filter_regular_gready_parameters(); P2
            ['c_12_7', 'b_4_2+b_4_0', 'b_4_1']
            sage: H.raw_filter_degree_type(P2)
            ([-1, -1, 11, 17],
             [[0],
              [0],
              [0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1],
              [1, 0, 0, 3, 1, 0, 2, 2, 1, 1, 3, 3, 0, 0, 2, 0, 0, 1]],
             [12, 4, 4])

        """
        if self._final_parameters:
            return True
        if len(self._DuflotRegSeq)<(self.PCenterRk or self.pRank):
            coho_logger.info("We need to find more Duflot generators", self)
            return False
        # First approach: take parameters from the subgroup, since this will yield small degrees.
        Par = self.parameters_from_sylow_subgroup()
        if Par is not None:
            if not Par.count(None):
                self.setprop('_current_parameters',[t for t in Par])
                self.setprop('_parameters_do_exist',True)
                return True
            if not self.verify_parameters_exist():
                return False
            if Par.count(None)==1 and Par[-1] is None:
                Par[-1] = self.find_small_last_parameter(Par, self.knownDeg)
                if not Par.count(None):
                    self.setprop('_current_parameters',[t for t in Par])
                    return True
        # If we arrive at this point, we must deal with the "big" Dickson elements
        Par = [t for t in self.Dickson]
        if not Par.count(None):
            self.setprop('_current_parameters',[t for t in Par])
            return True
        if Par.count(None)==1 and Par[-1] is None:
            Par[-1] = self.find_small_last_parameter(Par, self.knownDeg)
            if not Par.count(None):
                self.setprop('_current_parameters',[t for t in Par])
                return True
        if self.useElimination or self.completed: # the latter may occur if completeness was proved without filter regular parameters
            self.find_dickson()
            if not self.Dickson.count(None):
                self.setprop('_current_parameters',[t for t in self.Dickson])
                return True
            # it does not happen that only a part of the Dicksons is lifted. So, return False.
        return False

    # This method does the real work for next()
    def find_relations(self, n, rank=None):
        """
        Determine cohomology relations and optionally a basis for the decomposable subspace in a given degree.

        INPUT:

        - ``n`` (integer): The degree to be studied.
        - ``rank`` (optional integer, default ``None``): The dimension of the ``n``-th
          cohomology group (if this happens to be known).

        OUPUT:

        The relation ideal in the underlying Singular session is updated,
        and two lists ``D`` and ``R`` are returned, where ``D`` can also
        be ``None``.

        If the optional parameter ``rank`` is provided, then it will be
        assumed that it is the dimension of the ``n``-th cohomology group
        (considered as a vector space). If it is found that all stable
        elements in the cohomology of the underlying subgroup are
        decomposable and if ``rank`` is ``None``, then ``D`` is ``None``,
        indicating that the cohomology ring being studied has no minimal
        generator in degree ``n``. Otherwise, ``D`` is a list of
        :class:`~pGroupCohomology.cochain.MODCOCH` providing a basis for
        the decomposable subspace of the `n`-th cohomology group.

        The list ``R`` provides algebraic relations in degree ``n`` that
        hold between the cohomology generators.

        NOTE:

        This method should only be of internal use. The relation ideal
        in the Singular interface is updated (since it reduces traffic
        in the interface if this is done as soon as the relations are
        computed), but the list of relations is *not* updated. This may
        yield unexpected behaviour.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2, from_scratch=True)

        There are no generators yet, and by consequence there are no
        decomposable elements or relations::

            sage: H.find_relations(1)
            ([], [])

        After computing degree 1, it turns out that the only decomposable
        element (i.e., an element that can be expressed as a polynomial
        of previously found generators) is the degree-1 generator, and
        there are of course no relations::

            sage: H.make(1)
            sage: H.find_relations(1)
            ([c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))], [])

        We happen to know that the dimension of `H^2` is two. So, in
        degree two, the decomposable elements are returned, since there
        will be a generator in that degree::

            sage: H.find_relations(2, rank=2)
            ([c_1_0^2: 2-Cocycle in H^*(SmallGroup(720,763); GF(2))], [])

        We happen to know that the last generator is in degree three,
        while the dimension of `H^6` is ten. There is a relation in
        degree six. Since there are no generators in degree six, the
        decomposable subspace is not provided::

            sage: H.make(3)
            sage: H.find_relations(6, rank=10)
            (None, ['b_3_3*c_3_2+c_2_1*c_1_0*b_3_3'])

        The ideal in the Singular session is updated, but the list of relations isn't::

            sage: H.rels()
            []
            sage: H.set_ring()
            sage: H.relation_ideal()
            b_3_3*c_3_2+c_2_1*c_1_0*b_3_3

        Therefore, when we now repeat the quest for relations, we don't
        find any. However, this method can still be used for getting
        the decomposable subspace, by dropping the optional parameter::

            sage: H.find_relations(6)
            ([c_1_0^3*b_3_3: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              c_3_2^2+c_2_1*c_1_0*c_3_2: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              b_3_3^2: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              c_2_1*c_1_0*b_3_3: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              c_3_2^2+c_2_1*c_1_0*c_3_2+c_1_0^3*c_3_2: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              c_3_2^2: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              c_3_2^2+c_2_1^2*c_1_0^2: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              c_2_1*c_1_0^4: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              b_3_3^2+c_3_2^2+c_2_1*c_1_0*c_3_2+c_2_1^3: 6-Cocycle in H^*(SmallGroup(720,763); GF(2)),
              c_3_2^2+c_2_1^2*c_1_0^2+c_1_0^6: 6-Cocycle in H^*(SmallGroup(720,763); GF(2))],
             [])

        """
        singular = self.GenS.parent()
        try:
            br = singular('basering')
            dgb = singular.eval('degBound')
            singular.eval('degBound=0')
        except TypeError:
            br = None
        if not self.Gen:
            return [],[]
        # First, get standard monomials
        coho_logger.info("Exploring relations in degree %d"%n, self)
        self._makeStdMon(n,"Mon")
        cdef int nMon, lenHP, lenSelf, i
        cdef list PValues, SelfValues, Indicators
        try:
            self.set_ring()
            nMon = int(singular.eval('size(Mon)'))
            if nMon==0:
                coho_logger.info( "There are no standard monomials in degree %d, thus, no relations"%n, self)
                return [],[]
            tmp_r = singular('basering')
            if nMon>1:
                coho_logger.info( "Express %d standard monomials as cocycles"%nMon, self)
            else:
                coho_logger.info( "Express 1 standard monomial as cocycle", self)
            # copy the partially constructed ring of self, but with "safe" names:
            if self._property_dict.get('use_dp'):
                if len(self.degvec)==1:
                    r = singular.ring(self._prime,'(%s)'%(','.join(['@'+X.name() for X in self.Gen])), '(a(%d),dp)'%(self.degvec[0]))
                else:
                    r = singular.ring(self._prime,'(%s)'%(','.join(['@'+X.name() for X in self.Gen])), '(wp%s)'%(str(tuple(self.degvec))))
            else:
                self._makeOrderMatrix_()
                r = singular.ring(self._prime,'(%s)'%(','.join(['@'+X.name() for X in self.Gen])),'M(%sM)'%(self.prefix))
            singular.eval('ideal Mon = fetch(%s,Mon)'%tmp_r.name()) # hopefully fetch has no memory leak...
            rQP = singular(self._HP)
            self._HP.set_ring()
            rP = singular('basering')
            # Singular does not do proper interreduction in quotient rings.
            # Hence, we go to the ring. Hopefully this also works non-commutatively...
            R = rP + r # hence, interreduction eliminates the "value" of MODCOCH instances
            R.set_ring()
            PRels = singular('imap(%s,%sI)'%(rP.name(),self._HP.prefix))
            if nMon>1:
                singular.eval('poly p(1..%d) = imap(%s,Mon)'%(nMon,r.name())) # hopefully imap has no memory leak...
            else:
                singular.eval('poly p(1) = imap(%s,Mon)[1]'%(r.name())) # hopefully imap has no memory leak...
            singular.eval('ideal GenI=maxideal(1)')
            lenHP=len(self._HP.Gen)
            lenSelf=len(self.Gen)
            singular.eval('GenI=GenI[1..%d]'%lenHP)
            for i from 0<=i<lenSelf:
                singular.eval('GenI[%d]=imap(%s,%s)'%(i+1+lenHP,rQP.name(),self.Gen[i].value().name()))
            singular.eval('map Gen=basering,NF(GenI,%s)'%PRels.name())
            # These are the decomposable generators, with their values in self._HP and in self
            singular.eval('ideal DecGen')
            # without normal form computation, the memory consumption grows insanely high for Alternatinggroup(8) mod 2
            singular.eval('for(int %s_i=%d;%s_i>0;%s_i--){DecGen[%s_i]=NF(Gen(p(%s_i))+p(%s_i),%s);}'%(self.prefix,nMon,self.prefix,self.prefix,self.prefix,self.prefix,self.prefix,PRels.name()))
            coho_logger.debug( "> Interreduction", self)
            singular.eval('DecGen=interred(DecGen)')
            coho_logger.debug( "> Determining decomposable subspace", self)
            rQP.set_ring()
            # This is how the interreduced standard monomials look in self._HP:
            # Values[k]=='0' <=> DecGen[k+1] is a relation
            PVal=singular('imap(%s,DecGen)'%R.name())
            PValues=[PVal[i+1] for i in range(nMon)]
            Indicators=[singular.eval('%s==0'%x.name()) for x in PValues]
            r.set_ring() # names with '@'
            singular.eval('ideal DecGen=imap(%s,DecGen)'%R.name())
            self.set_ring()
            DG = singular('fetch(%s,DecGen)'%r.name()) # usual names - hopefully fetch is correct...

            # It is a bad idea to ship these new relations to the ring of self
            # VIA STRINGS. So, we do it here internally in Singular.
            lenOldRel=int(singular.eval('size(%sI)'%self.prefix))+1
            j=0
            for i from 0<=i<nMon:
                if Indicators[i]=='1':
                    singular.eval('%sI[%d]=%s[%d]'%(self.prefix,lenOldRel+j,DG.name(),i+1))
                    j+=1
            # "rank is None" means: we request the decomposables.
            # Otherwise, decomposables are computed only if there are generators in this degree
            if (rank is None) or (self.all_generators_found is None and (nMon-Indicators.count('1')<rank)):
                # If there are new generators or if we really want it (rank = None), compute all values
                # The relations correspond to '1' in the list "Indicators".
                coho_logger.debug( "> Extracting decomposable cocycles and relations", self)
                # This is how the interreduced standard monomials look in self:
                SelfValues = [t.strip() for t in singular.eval('print(%s)'%DG.name()).split(',')]
                Rels = [SelfValues[i] for i in range(nMon) if Indicators[i]=='1']
                from pGroupCohomology.cochain import MODCOCH
                DecGen = [MODCOCH(self, PValues[i], deg=n, name=SelfValues[i], S=singular, is_polyrep=True, is_NF=True) for i in range(nMon) if Indicators[i]=='0']
            else:
                # only extract the relations
                coho_logger.debug( "> Extracting relations", self)
                DecGen = None
                Rels = [singular.eval(DG.name()+'[%d]'%(i+1)) for i in range(nMon) if Indicators[i]=='1']
            singular.eval('kill %s_i,%s,%s,%s'%(self.prefix,R.name(),r.name(),tmp_r.name()))
            coho_logger.info("Found %d relations in degree %d", self, len(Rels), n)
            return DecGen, Rels
        finally:
            try:
                br.set_ring()
                singular.eval('degBound='+dgb)
            except:
                pass

    def decomposable_classes(self, int n, forced=False):
        """
        Vector space basis of the degree `n` part of ``self``, expressed as polynomials.

        INPUT:

        - ``n`` (integer): The degree to be studied.
        - ``forced`` (optional boolean, default ``False``): If ``True``,
          force re-computation.

        OUTPUT:

        A list of degree-``n`` elements of ``self`` that are expressed as
        polynomials in the generators of ``self`` and form a vector space
        basis for the ``n``-th cohomology group.

        ASSUMPTION:

        The ring structure must be known at least out to degree ``n``.
        Otherwise, a ``RuntimeError`` is raised.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2, from_scratch=True)

        We compute the ring structure only to degree 2 and then ask for
        the decomposable classes in degree 3, which yields an error::

            sage: H.make(2)
            sage: H.decomposable_classes(3)
            Traceback (most recent call last):
            ...
            RuntimeError: Ring structure in degree 3 is not known yet

        We fool ``H`` into believing that it is known in degree 3, and try again::

            sage: H.knownDeg = 3
            sage: sorted(H.decomposable_classes(3))
            [c_2_1*c_1_0: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_2_1*c_1_0+c_1_0^3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))]

        This result is wrong, since there are further cohomology elements in
        degree 3. But the result is cached. So, when we now *really* compute
        the ring structure in degree 3 and ask again, we still get the wrong
        answer::

            sage: H.knownDeg = 2
            sage: H.next()
            sage: sorted(H.decomposable_classes(3))
            [c_2_1*c_1_0: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_2_1*c_1_0+c_1_0^3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))]

        The correct answer is given when we force re-computation, and then the
        correct result is in the cache::

            sage: sorted(H.decomposable_classes(3,forced=True))
            [b_3_3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_3_2: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_3_2+c_2_1*c_1_0: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_3_2+c_2_1*c_1_0+c_1_0^3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))]
            sage: sorted(H.decomposable_classes(3))
            [b_3_3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_3_2: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_3_2+c_2_1*c_1_0: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_3_2+c_2_1*c_1_0+c_1_0^3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))]

        """
        if self.knownDeg<n and (not self.completed):
            raise RuntimeError("Ring structure in degree %d is not known yet"%n)
        cdef list DecGen = self.Triangular.get(n)
        if (DecGen is not None) and not forced:
            return DecGen
        self.Triangular[n], R = self.find_relations(n)
        assert not R, "Theoretical error: We found a new relation, contradicting the assertion that the ring structure is known in degree %d"%n
        return self.Triangular[n]

    def stable_to_polynomial(self, c, verify=True):
        """
        Express a stable cohomology element of a subgroup as a polynomial in the generators of ``self``.

        INPUT:

        - ``c``: an element of ``self`` or of the cohomology ring of one of the
          subgroups used to compute ``self``.
        - ``verify`` (optional boolean): If true (default), test whether ``c``
          really is stable, before trying to express it in ``self``.

        OUTPUT:

        An element of ``self`` (type :class:`~pGroupCohomology.cochain.MODCOCH`)
        corresponding to ``c``, or ``None`` if ``c`` is not stable and if
        ``verify`` is true. If ``c`` is not stable and ``verify`` is not true,
        then an error is raised.

        EXAMPLES:

        We work with the mod-2 cohomology of the Mathieu group `M_{12}`.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()   # Reset and disallow web access
            sage: G = libgap.eval('Group([(1,2,3,4,5,6,7,8,9,10,11), (3,7,11,8)(4,10,5,6), (1,12)(2,11)(3,6)(4,8)(5,9)(7,10)])')
            sage: H = CohomologyRing(G,prime=2,GroupName='M12', from_scratch=True)
            sage: H.make()
            sage: HS = H.sylow_cohomology()
            sage: HU = H.subgroup_cohomology()

        We first consider elements of ``HS`` and ``HU`` that are stable::

            sage: H.stable_to_polynomial(HS('b_1_2^6+b_1_1^2*b_1_2^4+b_1_1^6+b_2_4^2*b_1_1*b_1_2+b_2_4^3'))
            b_3_0*b_3_1+b_2_0^3: 6-Cocycle in H^*(M12; GF(2))
            sage: H.stable_to_polynomial(HU('b_2_0*b_2_2*b_3_4+c_4_6*b_3_1'))
            c_4_0*b_3_1: 7-Cocycle in H^*(M12; GF(2))

        An element of ``H`` is simply expressed as a polynomial, changing
        its name accordingly::

            sage: cG = H.1*H.2+H.3+H.4*H.5
            sage: cG.setname('foobar')
            sage: cG
            foobar: 6-Cocycle in H^*(M12; GF(2))
            sage: H.stable_to_polynomial(cG)
            b_3_0*b_3_1+b_6_3+b_2_0*c_4_0: 6-Cocycle in H^*(M12; GF(2))
            sage: cG
            b_3_0*b_3_1+b_6_3+b_2_0*c_4_0: 6-Cocycle in H^*(M12; GF(2))

        By default, it is tested whether the input is stable. If it isn't,
        it is stated in the log, and ``None`` is returned.
        ::

            sage: cS2 = HS('b_2_4^2*b_1_1*b_1_2+b_2_4^2*b_2_5+b_2_4^3+c_4_14*b_1_2^2')
            sage: CohomologyRing.global_options('debug')
            sage: print(H.stable_to_polynomial(cS2))
            H^*(M12; GF(2)):
                      Try to express a supposedly stable element of H^*(Syl2(M12); GF(2)) as a polynomial
            H^*(SmallGroup(192,1494); GF(2)):
                      Try to express a supposedly stable element of H^*(Syl2(M12); GF(2)) as a polynomial
                      Stability condition #0 is violated
            None
            sage: CohomologyRing.global_options('warn')
            sage: cS3 = HS('c_4_14*b_1_0')
            sage: CohomologyRing.global_options('debug')
            sage: print(H.stable_to_polynomial(cS3))
            H^*(M12; GF(2)):
                      Try to express a supposedly stable element of H^*(Syl2(M12); GF(2)) as a polynomial
            H^*(SmallGroup(192,1494); GF(2)):
                      Try to express a supposedly stable element of H^*(Syl2(M12); GF(2)) as a polynomial
                      Input is indeed stable in this ring...
            H^*(M12; GF(2)):
                      Stability condition #0 is violated
            None
            sage: CohomologyRing.global_options('warn')

        According to the log, ``cS3`` can be expressed in ``HU`` (not in ``H``,
        however), and indeed::

            sage: HU.stable_to_polynomial(cS3)
            c_4_6*b_1_0: 5-Cocycle in H^*(SmallGroup(192,1494); GF(2))

        Using the option ``verify=False`` will be a little faster,
        since it is not verified whether the input is stable before
        trying to lift. If it isn't, an error is raised.
        ::

            sage: HU.stable_to_polynomial(cS3, verify=False)
            c_4_6*b_1_0: 5-Cocycle in H^*(SmallGroup(192,1494); GF(2))
            sage: H.stable_to_polynomial(cS3, verify=False)
            Traceback (most recent call last):
            ...
            ValueError: Apparently the given cochain does not belong to H^*(M12; GF(2))

        """
        if c is None:
            return None
        # return a cocycle of self, whose name is a defining polynomial
        if not hasattr(c,'parent'):
            raise ValueError("Cocycle of a subgroup expected")
        coho_logger.debug("Try to express a supposedly stable element of %r as a polynomial", self, c.parent())
        singular = self.GenS.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        if c.parent() is self:
            try:
                return self.element_as_polynomial(c)
            except ValueError:
                coho_logger.debug( "Apparently the given cocycle cannot be expressed by the current generators", self)
                return None
        if  c.parent() is not self._HP:
            c = self._HP.stable_to_polynomial(c,verify=verify)
        if c is None:
            return None
        if verify:
            for i in range(len(self._PtoPcapCPdirect)):
                if self._PtoPcapCPdirect[i](c) != self._PtoPcapCPtwist[i](c):
                    coho_logger.debug( "Stability condition #%s is violated"%(i), self)
                    if br is not None:
                        br.set_ring()
                    return None
            coho_logger.debug( "Input is indeed stable in this ring", self)
        from pGroupCohomology.cochain import MODCOCH
        singular(self._HP).set_ring()
        s = singular.eval('NF({},std(0))'.format(singular(c).name()))
        c2 = MODCOCH(self,s,deg=c.deg(), name='tmpcycle',S=singular,rdeg=c.rdeg(),ydeg=c.ydeg(),is_NF=True)
        if br is not None:
            br.set_ring()
        try:
            return self.element_as_polynomial(c2)
        except ValueError:
            if verify:
                coho_logger.debug( "Apparently the given cocycle does not belong to this ring", self)
                return None
            raise

    def element_as_polynomial(self, c):
        """
        Express an element of ``self`` as a polynomial in the generators.

        INPUT:

        ``c`` of type :class:`~pGroupCohomology.cochain.MODCOCH`: An element of ``self``

        OUTPUT:

        ``c``, after changing its name so that it describes ``c`` as a polynomial.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: c = H.1*H.2+H.3+H.4
            sage: c.setname('foobar')
            sage: c
            foobar: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: H.element_as_polynomial(c)
            b_3_3+c_3_2+c_2_1*c_1_0: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: c
            b_3_3+c_3_2+c_2_1*c_1_0: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))

        """
        from pGroupCohomology.cochain import MODCOCH
        if (not isinstance(c,MODCOCH)) or (c.parent() is not self):
            raise TypeError("element of %s expected"%repr(self))
        if not self.Gen:
            raise RuntimeError("no generators known for "+repr(self))
        singular = c._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        try:
            n = c.deg()
            DecGen = self.decomposable_classes(n)
            self.set_ring()
            outS = singular.poly(0)
            singular(self._HP).set_ring()
            outP = singular.poly(0)
            c._NF_()
            for X in DecGen:
                singular(self._HP).set_ring()
                if outP==c._Svalue:
                    break
                coef = c.coef(X.lm())
                if coef:
                    singular.eval("%s=%s+%d*%s"%(outP.name(),outP.name(),coef,X.value().name()))
                    self.set_ring()
                    singular.eval("%s=%s+%d*%s"%(outS.name(),outS.name(),coef,X.name()))

            singular(self._HP).set_ring()
            if outP!=c._Svalue:
                raise ValueError("Apparently the given cochain does not belong to "+repr(self))
            self.set_ring()
            c.setname(singular.eval('print(%s)'%outS.name()).strip(), is_polyrep=True)
            return c
        finally:
            try:
                br.set_ring()
            except:
                pass

    def PrescribedRestrictions(self, L):
        """
        Try to construct a cochain of ``self`` that has given restrictions to the elementary abelian subgroups.

        INPUT:

        - ``L``: a list of elements of the form ``[i,C]``, where

          * ``i``: the number of a special subgroup
          * ``C``: a cochain (type <MODCOCH>) of the ``i``-th special subgroup

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2, from_scratch=True)
            sage: H.make(4)

        We now want to construct an element of ``H`` that restricts to
        a Dickson element ``D`` of degree 4 in the maximal elementary
        abelian subgroups, which are all of rank 3.
        ::

            sage: r1 = H.restriction_maps()[2][1]
            sage: r2 = H.restriction_maps()[3][1]
            sage: V = r1.codomain()
            sage: from pGroupCohomology.cochain import MODCOCH
            sage: D = MODCOCH(V,'c_1_2^4+c_1_1^2*c_1_2^2+c_1_1^4+c_1_0*c_1_1*c_1_2^2+c_1_0*c_1_1^2*c_1_2+c_1_0^2*c_1_2^2+c_1_0^2*c_1_1*c_1_2+c_1_0^2*c_1_1^2+c_1_0^4',name='D')
            sage: D
            D: 4-Cocycle in H^*(SmallGroup(8,5); GF(2))
            sage: H.PrescribedRestrictions([[2,D],[3,D]])
            (c_1_0)*(b_3_3)+((c_1_0)*(c_3_2))+((c_2_1)^2)+((c_1_0)^4): 4-Cocycle in H^*(SmallGroup(720,763); GF(2))

        """
        if not self.Gen:
            return None
        if not L:
            return None
        try:
            br0 = singular('basering')
        except TypeError:
            br0 = None
        cdef int j
        try:
            self.set_ring()
            rSelf = singular('basering')
            self._HP.set_ring()
            rP = singular('basering')
            n = L[0][1].deg()
            DecGen = self.decomposable_classes(n)
            if not DecGen:
                return None
            # create a ring for each of the values
            rList = []
            if singular.eval('defined(%s_i)'%self.prefix)=='0':
                singular.eval('int %s_i'%self.prefix)
            if singular.eval('defined(%s_j)'%self.prefix)=='0':
                singular.eval('int %s_j'%self.prefix)
            for i,C in L:
                if self.RestrMaps[i][1].codomain() is not C.parent():
                    raise ValueError("Cocycle "+repr(C)+" should belong to "+repr(self.RestrMaps[i][1].codomain()))
                rList.append(singular.ring(self._prime,'(@x(%d)(1..%d))'%(i,len(self.RestrMaps[i][1].codomain().Gen)),'dp')) # the ring order shouldn't matter
                name = singular(C.parent()).name()
                tmpRest = [self.RestrMaps[i][1](X) for X in DecGen]
                rList[-1].set_ring()
                singular.eval('poly p=fetch(%s,%s)'%(name,C._Svalue.name()))
                singular.eval('ideal Rest')
                for j from len(DecGen)>j>=0:
                    singular.eval('Rest[%d]=fetch(%s,%s)'%(j+1,name,tmpRest[j]._Svalue.name()))
            # Combine all the restrictions of DecGen into one ideal, and do interreduction
            singular.eval('setring '+rList[-1].name())
            Rtotal = singular('+'.join([X.name() for X in rList]) + '+'+rSelf.name())
            Rtotal.set_ring()
            tmpRest = [singular('imap(%s,Rest)'%X.name()) for X in rList]
            G = singular.ideal(0)
            singular.eval('%s[%d]=0'%(G.name(),len(DecGen)))
            for X in tmpRest:
                singular.eval('for (%s_i=%d;%s_i>0;%s_i--){%s[%s_i]=%s[%s_i]+%s[%s_i];}'%(self.prefix,len(DecGen),self.prefix,self.prefix, G.name(),self.prefix, G.name(),self.prefix, X.name(),self.prefix))
            for i in range(len(DecGen)):
                singular.eval('%s[%d]=%s[%d]-(%s)'%(G.name(),i+1, G.name(),i+1, DecGen[i].name()))
            singular.eval('%s=interred(%s)'%(G.name(),G.name()))
            singular.eval('attrib(%s,"isSB",1)'%G.name())
            # Now, a reduction by G does the lifting!
            # So, we combine the given values to one polynomial in Rtotal
            v = singular.poly(0)
            for X in rList:
               singular.eval('%s=%s+imap(%s,p)'%(v.name(),v.name(),X.name()))
            LiftStr = singular.eval('print(NF(%s,%s))'%(v.name(),G.name()))
            if '@' in LiftStr:
                return None
            return self(LiftStr)
        finally:
            try:
                br0.set_ring()
            except:
                pass

    def _extend_Duflot_reg_seq(self,d):
        """
        Find new Duflot regular elements in degree `d`.

        NOTE:

        This method is of internal use only.

        EXAMPLES:

        In order to produce an example, we need to destroy some internal data.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(48,50,prime=2, from_scratch=True)
            sage: H.make(3)
            sage: singular(H.restriction_maps()[1][1].codomain()).set_ring()
            sage: singular.eval('kill '+H.prefix+'RegTest')
            ''
            sage: H._DuflotRegSeq.pop(-1)
            c_3_7+(c_3_0): 3-Cocycle in H^*(SmallGroup(48,50); GF(2))

        Now, the Duflot regular sequence is cut off, but we can reconstruct the
        last element::

            sage: H.duflot_regular_sequence()
            ['c_2_3', 'c_2_2', 'c_3_1']
            sage: CohomologyRing.global_options('info')
            sage: H._extend_Duflot_reg_seq(3)
            H^*(SmallGroup(48,50); GF(2)):
                      Try to find new Duflot-regular element in degree 3
            explore_one_parameter:
                      32 = (2-1)^2*2^5 parameter candidates
                      We found a parameter.
                      > It is regular.
            H^*(SmallGroup(48,50); GF(2)):
                      Found extension of the Duflot regular sequence
            sage: CohomologyRing.global_options('warn')
            sage: H.duflot_regular_sequence()
            ['c_2_3', 'c_2_2', 'c_3_1', 'c_3_7+(c_3_0)']

        TEST:

        At some point, we had trouble finding a Duflot element in the following
        very easy case.
        ::

            sage: H = CohomologyRing(12, 3, prime=2)
            sage: H.make(3)
            sage: H._DuflotRegSeq
            [c_2_0: 2-Cocycle in H^*(SmallGroup(12,3); GF(2)),
             c_3_1: 3-Cocycle in H^*(SmallGroup(12,3); GF(2))]

        """
        if len(self._DuflotRegSeq)==(self.PCenterRk or self.pRank):
            return
        dgb = singular.eval('degBound')
        singular.eval('degBound = 0')
        self.set_ring()
        d = int(d)
        if d<1:
            raise ValueError("degree (positive integer) expected")
        coho_logger.info("Try to find new Duflot-regular element in degree %d"%d, self)
        # find a basis of new Duflot elements in degree d
        NDList = [t.name() for t in self.Gen if not t.rdeg()]+[t.name() for t in self._DuflotRegSeq]
        if NDList:
            NonDuf = singular.ideal(NDList).std()
        else:
            NonDuf = singular.ideal(0)
        B = NonDuf.weightKB(d, singular.intvec(*self.degvec))
        Bstr = [s.strip() for s in singular.eval('print(%s)'%B.name()).split(',')]
        rmap = self.RestrMaps[self.CElPos][1]
        L = [rmap(self(s)).value() for s in Bstr]
        HG = rmap.codomain()
        HGS = singular(HG)
        HGS.set_ring()
        if singular.eval('defined(%sRegTest)'%self.prefix)=='0':
            if self._DuflotRegSeq:
                singular.eval('ideal %sRegTest'%self.prefix)
                singular.eval('%sRegTest[%d]=0'%(self.prefix,len(self._DuflotRegSeq)))
                for i in range(len(self._DuflotRegSeq)):
                    vs = rmap(self._DuflotRegSeq[i]).value()
                    HGS.set_ring()
                    singular.eval('%sRegTest[%d]=%s'%(self.prefix,i+1,vs.name()))
                singular.eval('%sRegTest=groebner(%sRegTest)'%(self.prefix,self.prefix))
            else:
                singular.eval('ideal %sRegTest = std(0)'%self.prefix)
        from pGroupCohomology.cohomology import explore_one_parameter
        HGS.set_ring()
        HP0 = first_hilbert_series(singular.ideal('%sRegTest'%self.prefix))
        while(1):
            val, Coef, reg_vec = explore_one_parameter(singular('%sRegTest'%self.prefix), L, self._prime, regularity=2, H1=HP0, is_monomial=False)
            if val:
                coho_logger.info('Found extension of the Duflot regular sequence', self)
                self.set_ring()
                v = singular.eval('+'.join(['(%d)*(%s)'%(Coef[i],Bstr[i]) for i in range(len(L)) if Coef[i]]))
                self._DuflotRegSeq.append(self(v))
                if len(self._DuflotRegSeq)==(self.PCenterRk or self.pRank):
                    singular.eval('degBound='+dgb)
                    return
                HGS.set_ring()
                singular.eval('%sRegTest=std(%sRegTest,%s)'%(self.prefix,self.prefix,val.name()))
                HP0 = first_hilbert_series(singular.ideal('%sRegTest'%self.prefix))
            else:
                singular.eval('degBound='+dgb)
                return


    ###############################################################
    ##
    ##       Computing the Ring Structure
    ##
    ###############################################################

    def next(self, Forced=False, KeepDecomposables=False):
        """
        Compute the next degree of the cohomology ring approximation.

        NOTE:

        There is no comppletion test performed.

        EXAMPLES:

        First, we take care that the state of the cohomology rings of
        the elementary abelian subgroups and of the Sylow subgroup are
        in a well defined state, independent of the content of the
        local sources. In this example, we also illustrate logging.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(4,2, from_scratch=True)
            sage: X.make()
            sage: X = CohomologyRing(8,5, from_scratch=True)
            sage: X.make()
            sage: X = CohomologyRing(16,11, from_scratch=True)
            sage: X.make()
            sage: H = CohomologyRing(720,763,prime=2, from_scratch=True)
            sage: CohomologyRing.global_options('info')
            sage: H.next()
            H^*(SmallGroup(720,763); GF(2)):
                      Computing ring approximation in degree 1
                      Determining stable subspace in degree 1
            H^*(D8xC2; GF(2)):
                      Determine degree 1 standard monomials
            H^*(SmallGroup(8,5); GF(2)):
                      Determine degree 1 standard monomials
            H^*(SmallGroup(4,2); GF(2)):
                      Determine degree 1 standard monomials
            H^*(SmallGroup(720,763); GF(2)):
                      Setting up conditions to determine stable elements
                      Solving equations
                      We have to choose 1 new generator in degree 1
            H^*(SmallGroup(4,2); GF(2)):
                      Determine degree 1 standard monomials
            H^*(SmallGroup(8,5); GF(2)):
                      Determine degree 1 standard monomials
            H^*(SmallGroup(720,763); GF(2)):
                      > There are 0 nilpotent generators in degree 1
                      > There are 0 "boring" generators in degree 1
                      > There is 1 Duflot generator in degree 1
                      Try to find new Duflot-regular element in degree 1
            explore_one_parameter:
                      1 = (2-1)^1 parameter candidates
                      We found a parameter.
                      > It is regular.
            H^*(SmallGroup(720,763); GF(2)):
                      Found extension of the Duflot regular sequence
                      Degree 1 of the visible ring structure is computed!
                      Storing ring approximation
            sage: H.next()
                      Computing ring approximation in degree 2
                      Determining stable subspace in degree 2
            H^*(D8xC2; GF(2)):
                      Determine degree 2 standard monomials
            H^*(SmallGroup(8,5); GF(2)):
                      Determine degree 2 standard monomials
            H^*(SmallGroup(4,2); GF(2)):
                      Determine degree 2 standard monomials
            H^*(SmallGroup(720,763); GF(2)):
                      Setting up conditions to determine stable elements
                      Solving equations
                      Exploring relations in degree 2
                      Determine degree 2 standard monomials
                      Express 1 standard monomial as cocycle
                      Found 0 relations in degree 2
                      We have to choose 1 new generator in degree 2
            H^*(SmallGroup(4,2); GF(2)):
                      Determine degree 2 standard monomials
            H^*(SmallGroup(8,5); GF(2)):
                      Determine degree 2 standard monomials
            H^*(SmallGroup(720,763); GF(2)):
                      > There are 0 nilpotent generators in degree 2
                      > There are 0 "boring" generators in degree 2
                      > There is 1 Duflot generator in degree 2
                      Try to find new Duflot-regular element in degree 2
            explore_one_parameter:
                      1 = (2-1)^1 parameter candidates
                      We found a parameter.
                      > It is regular.
            H^*(SmallGroup(720,763); GF(2)):
                      Found extension of the Duflot regular sequence
                      Degree 2 of the visible ring structure is computed!
                      Storing ring approximation

        So, apparently the stable subspace of the cohomology ring of the
        underlying subgroup ``D8xC2`` is computed in each degree, then it
        is determined how much of it is decomposable, and new generators
        are chosen accordingly.

        We continue the computation out to degree 5, turning off the log.
        There is still no relation::

            sage: CohomologyRing.global_options('warn')
            sage: H.make(5)
            sage: print(H)
            Cohomology ring of SmallGroup(720,763) with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 5
            Minimal list of generators:
            [c_2_1: 2-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             b_3_3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
             c_3_2: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))]
            Minimal list of algebraic relations:
            []

        Resuming logging, we compute the next degree. Meanwhile the program
        has tested that it found all generators. Thus, it is not needed to
        compute the stable subspace in advance, as can be seen in the log.
        ::

            sage: CohomologyRing.global_options('info')
            sage: H.next()
            H^*(SmallGroup(720,763); GF(2)):
                      Computing ring approximation in degree 6
                      All generators are known
                      Exploring relations in degree 6
                      Determine degree 6 standard monomials
                      Express 11 standard monomials as cocycles
                      Found 1 relations in degree 6
                      There is no new generator in degree 6
                      Try to lift 1st power of 1st Dickson invariant
                      Exploring relations in degree 6
                      Determine degree 6 standard monomials
                      Express 10 standard monomials as cocycles
                      Found 0 relations in degree 6
                      Factorising an element; it can be interrupted with Ctrl-c
                      Degree 6 of the visible ring structure is computed!
                      Storing ring approximation

        There is no completion test performed. But in fact, the
        completion test is successful::

            sage: H.completed
            False
            sage: H.test_for_completion()
                      Compute dependent_parameters
                      Try to find a set of generators over which the cohomology ring is finite.
                      Computing complete Groebner basis
                      Trying Symonds' criterion
                      Successful application of the Symonds criterion
            True
            sage: H.completed
            True

        """
        cdef RESL R = self.Resl
        from sage.all import add
        if self.completed and (not Forced):
            return
        if self.SUBGPS:
            self.reconstructSubgroups()

        n = self.knownDeg + 1
        cdef int i,k,m,cf
        cdef FEL f
        cdef int lenDecGen,lenMonExp
        cdef int loopbound
        SHP = singular(self._HP)
        coho_logger.info("Computing ring approximation in degree %d"%n,self)

        ######################################
        ## Main Procedure
        ######################################
        cdef list L, Monomials, StableList, StablePivots
        cdef MTX Stables, NondecStables, NilNonDec
        cdef Matrix_t *tmpMatrix_t
        cdef Matrix_t *tmpProduct
        NewDuflot = None
        # StableList: list of MODCOHO, forming interreduced basis of the stable space
        # StablePivots: list of leading monomials of StableList, used to keep track of computations
        # Monomials: list of degree n standard monomials of self._HP -- starting with StablePivots!
        #
        # Easy case: All generators are allready known.
        if self.all_generators_found:
            coho_logger.info("All generators are known", self)
            StableList   = []
            Monomials    = []
            StablePivots = []
        else:
            StableList, Monomials, StablePivots = self.stable_space(n)
        Monomials = StablePivots + [X for X in Monomials if X not in StablePivots]
        if not self.all_generators_found:
            coho_logger.debug("> dim H^%d = %d"%(n,len(StableList)), self)
        if (not StableList) and (not self.Gen):
            coho_logger.debug("No cocycles in degree %d"%n, self)
            self.knownDeg = self.knownDeg + 1
            if (self.suffDeg > 0) and (self.knownDeg >= self.suffDeg):
                self.completed = True
            return

        m = len(StablePivots)
        cdef list DecGen=[]  # will be a triangular basis of the sub space of decomposables of H^n
        cdef list pivot=[] # those pivots (here: Monomials of self._HP as a string)
                           # that have already been used by decomposable classes
        cdef list StableNonDec
        cdef tuple PivotsNilDec

        cdef list MonExp,lastPiv, newRelations
        if self.Gen!=[]:  # there can only be decomposables if there are generators, yet
            ####################################
            # We must lift self.RelG to the new degree.
            # First, switch to the previous ring
            self.set_ring()
            if len(self.Rel)==0:
                singular.eval('ideal %sI = std(0)'%(self.prefix))
            else:
                # At least for J3mod3, it turns out to be better to compute
                # the complete GB, if there were no relations in the previous
                # degree.
                if (self.lastRel < n-1):
                    self.make_groebner()
                else:
                    self.make_groebner(n)
            ##########
            # determine decomposable cocycles and relations
            DecGen, newRelations = self.find_relations(n,rank=len(StableList))
            if newRelations:
                self.delprop('completeGroebner')
                self.delprop('_small_last_parameter_attempted')
                self.delprop('_current_parameters')
                self.delprop('lastTested')
                self.delprop('potential_bound')
                if self.original_parameters: # should only happen if the last parameter was replaced
                    self.Dickson = self.original_parameters
                self.lastRel = n
            self.Rel.extend(newRelations)
            SHP.set_ring()
            if DecGen is not None:
                for Cand in DecGen:
                    j = Cand.lm() # this is a singular element
                    pivot.append(j)
                    StablePivots[StablePivots.index(str(j))] = None
            # The new relations are already added to the relation ideal.
            # This is done in find_relations(n), without passing string
            # representations over the Singular interface
            self.set_ring()

        ###################
        ## RESULT:
        ## I. MODCOCH types
        self.knownDeg=n

        ###################
        ## CHOOSING NEW RING GENERATORS
        ##################

        cdef list NewGen = []
        cdef dict ZN_comp = {} # indexed by the pivots (string representing a monomial) of stable elements.
                               # Value 1 (in the beginning) if not pivot of a decomposable class
                               # Value 2 if pivot of a new nilpotent generator
                               # Value 4 if pivot of a boring generator
        cdef dict SubgpMonomials = {}
        if DecGen is None:
            NrNewGen = 0
        else:
            NrNewGen = m - StablePivots.count(None) # m was defined above == len(StablePivots)
        SHP.set_ring()
        if NrNewGen==0:
            coho_logger.info("There is no new generator in degree %d"%(n), self)
        cdef Matrix_t *tmpMTX0
        cdef Matrix_t *tmpMTX
        cdef Matrix_t *tmpMTXout
        if NrNewGen>0:  # there are new ring generators.
            self.delprop('completeGroebner')
            self.delprop('_small_last_parameter_attempted')
            self.delprop('_current_parameters')
            self.delprop('lastTested')
            self.delprop('potential_bound')
            if self.degbound_for_gens is not None and self.degbound_for_gens>n:
                self.delprop('degbound_for_gens')
            if self.original_parameters: # should only happen if the last parameter was replaced
                self.Dickson = self.original_parameters
            from pGroupCohomology.cochain import MODCOCH
            if NrNewGen==1:
                coho_logger.info("We have to choose 1 new generator in degree %d"%(n), self)
            else:
                coho_logger.info("We have to choose %d new generators in degree %d"%(NrNewGen,n), self)

            # Get standard monomials of the subgroups
            for X,Y in self.subgps.items():
                SubgpMonomials[X] = Y.standard_monomials(n)
            SHP.set_ring()
            lenMonExp = len(Monomials) # recycling
            ## 1. New generators with nilpotent restriction on all
            ## maximal elementary abelian subgroups
            ## --> These are nilpotent!
            for X in StablePivots:
                if X is not None:
                    ZN_comp[X] = 1
            if self.MaxelPos:
                # NilDec is a basis in (semi)echelon form of the subspace of decomposable nilpotent classes of degree n
                if DecGen: # there are decomposables, so let's intersect with the nilpotents:
                    tmpMTX0 = rawMatrix(R.G_Alg.Data.p, [X.coef_list(Monomials) for X in DecGen])
                    tmpMTX = MatNullSpace__(rawMatrix(self._prime,[add([(self.RestrMaps[mpos][1]*X).nilreduce().coef_list(SubgpMonomials[self.RestrMaps[mpos][0]]) for mpos in self.MaxelPos],[]) for X in DecGen]))
                    tmpMTXout = MatAlloc(tmpMTX.Field, tmpMTX.Nor, tmpMTX0.Noc)
                    assert MatMulStrassen(tmpMTXout, tmpMTX, tmpMTX0)!=NULL, "Strassen multiplication failed"
                    MatFree(tmpMTX)
                    MatFree(tmpMTX0)
                    NilDec = new_mtx(tmpMTXout, None)
                    NilDec.echelonize()
                    NilDec.set_immutable()
                    PivotsNilDec = NilDec.pivots() # these are indices of the list 'Monomials'
                else:
                    PivotsNilDec = ()
                for i in PivotsNilDec:
                    ZN_comp[Monomials[i]]=0
                    StablePivots[i] = None

                # Now we compute a basis in (semi)echelon form of a complement of
                # decomposable nilpotent classes in the stable nilpotent classes
                # using the basis given by those elements of "StableList" that have
                # no "decomposable" pivot.
                SHP.set_ring()
                StablesNonDec = new_mtx(rawMatrix(self._prime, [X.coef_list(Monomials) for X in StableList if ZN_comp.get(X.lm_string(),0)==1]), None)
                StablesNonDec.set_immutable()
                tmpMTX = MatNullSpace__(rawMatrix(self._prime,[add([(self.RestrMaps[mpos][1]*X).nilreduce().coef_list(SubgpMonomials[self.RestrMaps[mpos][0]]) for mpos in self.MaxelPos],[]) for X in StableList if ZN_comp.get(X.lm_string(),0)==1]))
                tmpMTXout = MatAlloc(tmpMTX.Field, tmpMTX.Nor, StablesNonDec.Data.Noc)
                assert MatMulStrassen(tmpMTXout, tmpMTX, StablesNonDec.Data)!=NULL, "Strassen multiplication failed"
                NilNonDec = new_mtx(tmpMTXout, StablesNonDec)
                NilNonDec.echelonize()
                MatFree(tmpMTX)
                # The rows of this matrix yield (ydeg=1,rdeg=0)-generators
                # (i.e., nilpotent but nondecomposable classes).
                loopbound = NilNonDec.nrows()
                FfSetNoc(NilNonDec.Data.Noc)
                for i from 0 <= i < loopbound:
                    j = FfFindPivot(MatGetPtr(NilNonDec.Data, i), &f)
                    assert j>=0
                    # a new normalised generator with nilpotent restriction:
                    NewGen.append(MODCOCH(self, '('+'+'.join(['('+str(NilNonDec[i,k])+')*'+Monomials[k] for k in range(lenMonExp) if NilNonDec[i,k]])+')/%d'%f, deg=n, name='a_%d_%d'%(n,j), S=singular, ydeg=1,rdeg=0, is_polyrep=True, is_NF=True))
                    StablePivots[j]=None
                # we will now disregard those stable basis elements whose
                # pivot occurs in the nilpotent generators we just found
                PivotsNilDec = NilNonDec.pivots() # recycling...
                for i in PivotsNilDec:
                    ZN_comp[Monomials[i]]=2  # 0 was decomposable and nilpotent,
                                             # 2 is indecomposable nilpotent
                NrNewGen = NrNewGen-len(NewGen)
                if list(ZN_comp.values()).count(2)!=len(NewGen):
                    raise ArithmeticError("%d==%d -- that seems strange"%(list(ZN_comp.values()).count(2),len(NewGen)))
                if len(NewGen)==1:
                    coho_logger.info("> There is 1 nilpotent generator in degree %d"%(n), self)
                else:
                    coho_logger.info("> There are %d nilpotent generators in degree %d"%(len(NewGen),n), self)

            ## 2. New generators with nilpotent restriction on the
            ## greatest elementary abelian central subgroup
            if (self.CElPos in self.RestrMaps and NrNewGen):
                # Now we compute a basis in (semi)echelon form of a complement of
                # decomposable or nilpotent classes in the stable classes intersect
                # with those that have nilpotent restriction to the greatest
                # elementary abelian subgroup in the center of the Sylow group,
                # using the basis given by StableList
                StablesNonDec = new_mtx(rawMatrix(self._prime, [X.coef_list(Monomials) for X in StableList if ZN_comp.get(X.lm_string(),0)==1]), None)
                StablesNonDec.set_immutable()
                tmpMatrix_t = rawMatrix(R.G_Alg.Data.p,[(self.RestrMaps[self.CElPos][1]*X).nilreduce().coef_list(SubgpMonomials[self.RestrMaps[self.CElPos][0]]) for X in StableList if ZN_comp.get(X.lm_string(),0)==1])
                assert tmpMatrix_t != NULL, "Could not create matrix"
                tmpMatrix_t = MatNullSpace__(tmpMatrix_t)
                assert tmpMatrix_t != NULL, "Could not compute nullspace of a matrix"
                tmpProduct = MatAlloc(R.G_Alg.Data.p, tmpMatrix_t.Nor, StablesNonDec.Data.Noc)
                MatMulStrassen(tmpProduct, tmpMatrix_t, StablesNonDec.Data)
                MatFree(tmpMatrix_t)
                NilNonDec = new_mtx(tmpProduct, None)
                NilNonDec.echelonize()

                # The rows of this matrix yield boring (ydeg=rdeg=0)-generators
                # (i.e., non-nilpotent indecomposable classes with nilpotent restriction on the
                # central el.ab subgroups of the Sylow subgroup).
                loopbound = NilNonDec.rank()
                FfSetNoc(NilNonDec.Data.Noc)
                for i from 0 <= i < loopbound:
                    j = FfFindPivot(MatGetPtr(NilNonDec.Data, i), &f)
                    assert j>=0
                    # a new normalised generator with nilpotent restriction:
                    NewGen.append(MODCOCH(self, '('+'+'.join(['('+str(NilNonDec[i,k])+')*'+Monomials[k] for k in range(lenMonExp) if NilNonDec[i,k]])+')/%d'%f, deg=n, name='b_%d_%d'%(n,j), S=singular, ydeg=0,rdeg=0, is_polyrep=True, is_NF=True))
                    if StablePivots[j] is None:
                        raise RuntimeError("Pivots got messed up. Please inform the author")
                    StablePivots[j]=None

                # we will now disregard those stable basis elements whose
                # pivot occurs in the nilpotent generators we just found
                PivotsNilDec = NilNonDec.pivots() # recycling...
                for i in PivotsNilDec:
                    ZN_comp[Monomials[i]]=3  # 0 or 2 was decomposable or nilpotent,
                                             # 3 is nilpotent restriction on CElAb

                if list(ZN_comp.values()).count(3)==1:
                    coho_logger.info('> There is 1 "boring" generator in degree %d'%(n), self)
                else:
                    coho_logger.info('> There are %d "boring" generators in degree %d'%(list(ZN_comp.values()).count(3),n), self)
                NrNewGen = NrNewGen - list(ZN_comp.values()).count(3)

            if (NrNewGen != list(ZN_comp.values()).count(1)):
                raise RuntimeError("Error in the quest for regular generators")
            NewDuflot = bool(NrNewGen)
            if NrNewGen:
                for i from 0 <= i < m:
                    if StablePivots[i] is not None:
                        StableList[i].setname('c_%d_%d'%(n,i))
                        StableList[i]._rdeg=1
                        StableList[i]._ydeg=0
                        StableList[i]._polyrep=True
                        StableList[i]._NF=True
                        NewGen.append(StableList[i])
                        NrNewGen -= 1
                if NrNewGen!=0:
                    raise RuntimeError("Error in choosing regular generators")

                if list(ZN_comp.values()).count(1)==1:
                    coho_logger.info("> There is 1 Duflot generator in degree %d"%(n), self)
                else:
                    coho_logger.info("> There are %d Duflot generators in degree %d"%(list(ZN_comp.values()).count(1),n), self)

        ## Insert the new generators:
        if n%2:
            firstNew = len(self.Gen)
            self.Gen.extend(NewGen)
            self.degvec.extend(len(NewGen)*[n])
        else:
            firstNew = self.firstOdd
            for CO in NewGen:
                self.Gen.insert(self.firstOdd, CO)
                self.degvec.insert(self.firstOdd, n)
                self.firstOdd+=1

        if (KeepDecomposables) and (self.lastRelevantDeg > 0):
            self.set_ring()   # The matrix DG in singular was to save name length. But we wouldn't save DG
            for X in (DecGen or []):  # Hence: We need to change the names into clear names.
                X.setname(singular.eval('print(%s)'%X.name()))
        ###################
        ## We can not simply extend self.Triangular by NewGen, since they are in general not triangular
        SHP.set_ring()
        for Cand in NewGen:
            f = Cand.lc()
            j = Cand.lm()
            lenDecGen = len(DecGen)
            if f:
                for k from 0 <= k < lenDecGen:
                    if (j >= pivot[k]):
                        cf = Cand.coef(pivot[k])
                        if cf:
                            Cand = Cand - (DecGen[k])*cf
                            f = Cand.lc()
                            j = Cand.lm()
                if not f:
                    raise RuntimeError("New 'Generator' is in fact decomposable")
                DecGen.append(Cand/f)
                pivot.append(j)

        ####################
        ## II. put the new generators into the dictionary of monomials
        ## Not needed here.
##        for i from 0 <= i < len(self.Gen):
##            self.Monomials[self.Gen[i].name()] = self.Gen[i]

        ####################
        ## III. Update Singular
        if self._property_dict.get('use_dp'):
            if len(self.degvec)==1:
                singular.eval('ring tmp = %d,(%s),%s'%(R.G_Alg.Data.p, ','.join([x.name() for x in self.Gen]), '(a(%d),dp)'%(self.degvec[0])))
            else:
                singular.eval('ring tmp = %d,(%s),%s'%(R.G_Alg.Data.p, ','.join([x.name() for x in self.Gen]), '(wp%s)'%(str(tuple(self.degvec)))))
        else:
            self._makeOrderMatrix_()
            singular.eval('ring tmp = %d,(%s),M(%sM)'%(R.G_Alg.Data.p, ','.join([x.name() for x in self.Gen]), self.prefix))
        if R.G_Alg.Data.p!=2 and self.firstOdd<len(self.Gen):   # non-commutative case
            singular.eval('degBound = 0')
            singular.eval('def %sr(%d) = superCommutative(%d,%d)'%(self.prefix,n,self.firstOdd+1, len(self.Gen)))
        else:
            singular.eval('def %sr(%d) = tmp'%(self.prefix,n))
        singular.eval('setring %sr(%d)'%(self.prefix,n))
        singular.eval('kill tmp')
        # keep standard monomials of lower degrees:
        if not n in self.StdMon:
            self.StdMon[n]={}
        for i from 0<i<=n:
            if i in self.StdMon:
                for ITEM in self.StdMon[i].items():
                    self.StdMon[i][ITEM[0]]=singular('%sr(%d)'%(self.prefix,self.lastRelevantDeg)).imap(ITEM[1])
        # ... and don't forget that the new generators are standard monomials!
        for X in self.Gen:
            if X.Deg==n:
                self.StdMon[n][X.name()]=singular.ideal(X.name())
        if self.lastRelevantDeg>0:
            singular.eval('ideal %sI = imap(%sr(%d),%sI)'%(self.prefix,self.prefix,self.lastRelevantDeg,self.prefix))
            # keep track of decomposable generators --
            # We need them for lifting the Dickson invariants!
            singular.eval('ideal %sDG = imap(%sr(%d),%sDG)'%(self.prefix,self.prefix,self.lastRelevantDeg,self.prefix))
        else:
            singular.eval('ideal %sI'%(self.prefix))
            singular.eval('ideal %sDG'%(self.prefix))
        if KeepDecomposables:
            self.GenS = singular('%sr(%d)'%(self.prefix,n))
            self.RelG = [s.strip() for s in singular.eval('print(%sI)'%(self.prefix)).split(',')]

        #####################
        ## Empty the dustbin!
        if self.lastRelevantDeg:
            singular.eval('setring %sr(%d)'%(self.prefix,self.lastRelevantDeg))
            singular.eval('kill %sI'%(self.prefix))
            singular.eval('kill %sDG'%self.prefix)
            singular.eval('kill Mon')
            singular.eval('setring %sr(%d)'%(self.prefix,n))
            singular.eval('kill %sr(%d)'%(self.prefix,self.lastRelevantDeg))
        self.lastRelevantDeg = n
        # Lifting the Dickson classes works only *after* updating singular
        if NewDuflot:
            self._extend_Duflot_reg_seq(n)
        if self.pRank == (self.PCenterRk or self.pRank):
            self.set_ring()
            self.Dickson = [singular.eval('print(%s)'%X.name()) for X in self._DuflotRegSeq]
        else:
            if not self.useElimination:
                if len(self.Dickson)<self.pRank:
                    self.Dickson = [None for i in range(self.pRank)]
                Ddg = Integer(self._prime)**self.pRank
                switch = (2 if self._prime%2 else 1)
                for i from 0<i<=self.pRank:
                    if self.Dickson[i-1] is None:
                        for j in Integer(self._Order).divisors():
                            if self.knownDeg < (switch*(Ddg - Integer(self._prime)**(self.pRank-i)))*j:
                                break
                            if self.knownDeg == (switch*(Ddg - Integer(self._prime)**(self.pRank-i)))*j:
                                SHP.set_ring()
                                PotentialDicksonLift = self.lift_dickson(i-1,j)
                                if PotentialDicksonLift is not None:
                                    if self.useFactorization:
                                        self.Dickson[i-1] = self.small_factor(PotentialDicksonLift)
                                    else:
                                        self.set_ring()
                                        self.Dickson[i-1] = singular.eval('print(%s)'%PotentialDicksonLift.name())
                                break
                            j+=1

        coho_logger.info("Degree %d of the visible ring structure is computed!"%(n), self)
        if coho_options['save']:
            coho_logger.info("Storing ring approximation", self)
            safe_save(self, self.autosave_name())

    def make(self, max_deg=-1):
        r"""
        Compute the cohomology ring structure, either completely or out to a specific degree.

        INPUT:

        ``max_deg`` (optional integer): If provided, compute at most out to
        this degree.

        EXAMPLES:

        The group we are using in this example is ``MathieuGroup(12)``.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.eval('Group([(1,2,3,4,5,6,7,8,9,10,11),(3,7,11,8)(4,10,5,6),(1,12)(2,11)(3,6)(4,8)(5,9)(7,10)])')
            sage: H = CohomologyRing(G,prime=3,GroupName='M12', from_scratch=True)

        We let compute the ring structure out to degree 16. The program
        tries to find parameters and tests whether there will be further
        generators.
        ::

            sage: H.make(16)
            sage: H.filter_regular_parameters()
            ['b_4_0^3-c_12_0', 'b_16_3-b_16_1+b_4_0^4-b_4_0*c_12_0']
            sage: H.all_generators_found
            True

        Using ``make`` without an optional argument results in a complete
        computation. Completeness is proved in degree 32, which is exactly
        where the last relation can be found::

            sage: H.make()
            sage: H.completed
            True
            sage: H.knownDeg
            32
            sage: H.lastRel
            32

        We devise two methods to prove completeness of the ring structure for
        non prime power groups: The Hilbert\--Poincaré criterion and the Symonds
        criterion. We start with Hilbert\--Poincaré::

            sage: p = H.poincare_series(); p
            (t^24 - 2*t^23 + 3*t^22 - 3*t^21 + 5*t^20 - 6*t^19 + 7*t^18 - 7*t^17 + 9*t^16 - 9*t^15 + 12*t^14 - 11*t^13 + 12*t^12 - 11*t^11 + 12*t^10 - 9*t^9 + 9*t^8 - 7*t^7 + 7*t^6 - 6*t^5 + 5*t^4 - 3*t^3 + 3*t^2 - 2*t + 1)/(t^26 - 2*t^25 + 3*t^24 - 4*t^23 + 5*t^22 - 6*t^21 + 7*t^20 - 8*t^19 + 9*t^18 - 10*t^17 + 11*t^16 - 12*t^15 + 12*t^14 - 12*t^13 + 12*t^12 - 12*t^11 + 11*t^10 - 10*t^9 + 9*t^8 - 8*t^7 + 7*t^6 - 6*t^5 + 5*t^4 - 4*t^3 + 3*t^2 - 2*t + 1)
            sage: H.parameters()
            ['b_4_0^3-c_12_0', 'b_16_3-b_16_1+b_4_0^4-b_4_0*c_12_0']
            sage: t = p.parent().gen(0)
            sage: p*(1-t^12)*(1-t^16)
            t^26 + t^23 + 2*t^22 + t^21 + t^19 + 2*t^18 + 2*t^17 + 3*t^16 + 4*t^15 + 2*t^14 + 2*t^13 + 2*t^12 + 4*t^11 + 3*t^10 + 2*t^9 + 2*t^8 + t^7 + t^5 + 2*t^4 + t^3 + 1
            sage: H.knownDeg >= (12 + 16) - H.depth()
            True
            sage: 26 <= H.knownDeg
            True

        The last few lines actually prove that the ring structure is
        complete\---see :meth:`HilbertPoincareTest` for the background.
        In this example, the Hilbert Poincaré test has actually been used
        when calling ``make()``::

            sage: H._method
            'Hilbert-Poincar&eacute;'

        We have parameters in degree 12 and 16. We need to know the ring
        structure at least out to degree `(12-1)+(16-1)+1=27`, and we need to
        show that as a module over these parameters, the ring approximation is
        generated in at most the degree out to which we know the ring
        structure. This is indeed the case::

            sage: H.knownDeg
            32
            sage: H.set_ring()
            sage: B = (H.relation_ideal()+singular.ideal(H.parameters())).groebner().kbase()
            sage: max([int(p.deg()) for p in B])
            26

        Given these data, it may surprise why it was needed to compute out to
        degree 32 and not just 27. But simply there is a relation in degree
        32, and without the final relation, the module structure of the ring
        approximation would not be finitely generated::

            sage: (singular.ideal(H.rels()[:-1])+singular.ideal(H.parameters())).groebner().GKdim()
            1

        TESTS:

        In the following example, one of our criteria correctly determined the
        degree bound 19 when being called in degree 18. But after finding the
        last relation in degree 19, the previously obtained degree bound has
        not been used *and* the completion test has not been repeated. This is
        fixed now::

            sage: H = CohomologyRing(1620, 244, prime=3, from_scratch=True)
            sage: H.make()
            sage: H.knownDeg
            19
            sage: print(H)
            Cohomology ring of SmallGroup(1620,244) with coefficients in GF(3)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [a_2_1: 2-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             b_2_0: 2-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             c_4_3: 4-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_6_1: 6-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             c_8_4: 8-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             c_12_11: 12-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_3_0: 3-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_3_1: 3-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_3_4: 3-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_7_0: 7-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_7_4: 7-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_7_5: 7-Cocycle in H^*(SmallGroup(1620,244); GF(3)),
             a_11_4: 11-Cocycle in H^*(SmallGroup(1620,244); GF(3))]
            Minimal list of algebraic relations:
            [a_2_1^2,
             a_2_1*b_2_0,
             a_2_1*a_3_0,
             a_2_1*a_3_1,
             a_2_1*a_3_4,
             b_2_0*a_3_0,
             b_2_0*a_3_4,
             a_3_0*a_3_4,
             a_3_1*a_3_4-a_2_1*c_4_3,
             a_2_1*a_6_1,
             a_2_1*a_7_0,
             a_2_1*a_7_4,
             a_2_1*a_7_5,
             a_6_1*a_3_0,
             a_6_1*a_3_1-b_2_0*a_6_1*a_1_0,
             a_6_1*a_3_4,
             b_2_0*a_7_5,
             a_3_0*a_7_0,
             a_3_0*a_7_5,
             a_3_1*a_7_4-b_2_0*a_1_0*a_7_4,
             a_3_1*a_7_5+a_2_1*c_8_4,
             a_3_4*a_7_0,
             a_3_4*a_7_4+a_2_1*c_8_4,
             a_3_4*a_7_5,
             b_2_0^2*a_6_1-a_3_1*a_7_0+b_2_0*a_1_0*a_7_0+c_4_3*a_6_1,
             c_8_4*a_3_4+c_4_3*a_7_5,
             b_2_0^2*a_7_4-c_8_4*a_3_1+c_4_3*a_7_4+b_2_0*c_8_4*a_1_0,
             a_6_1^2,
             a_2_1*a_11_4,
             a_6_1*a_7_0,
             a_6_1*a_7_4,
             a_6_1*a_7_5,
             a_3_0*a_11_4,
             a_3_1*a_11_4-b_2_0*a_1_0*a_11_4-a_6_1*c_8_4,
             a_3_4*a_11_4,
             a_7_0*a_7_4+a_6_1*c_8_4,
             a_7_0*a_7_5,
             a_7_4*a_7_5+a_2_1*c_12_11,
             c_12_11*a_3_1-c_8_4*a_7_4-b_2_0*c_12_11*a_1_0,
             c_12_11*a_3_4+c_8_4*a_7_5,
             b_2_0^2*a_11_4-c_8_4*a_7_0+c_4_3*a_11_4,
             b_2_0^2*c_12_11-c_8_4^2+c_4_3*c_12_11,
             a_6_1*a_11_4,
             a_7_0*a_11_4,
             a_7_4*a_11_4-a_6_1*c_12_11,
             a_7_5*a_11_4,
             c_12_11*a_7_0-c_8_4*a_11_4]

        """
        if max_deg == 0:
            return
        TCT = cputime()
        TWT = walltime()
        if (not (isinstance(max_deg, int) or isinstance(max_deg, Integer))) or \
           (max_deg==0) or (max_deg<-1):
            raise IndexError("The degree bound must be a positive integer")
        if ((self.suffDeg>-1) and (self.knownDeg >= self.suffDeg)) or self.completed:
            coho_logger.info("Ring structure is completely known.", self)
            return
        if (max_deg!=-1) and (max_deg <= self.knownDeg):
            coho_logger.info( 'Ring approximation is known out to degree %d --- enough for now'%(self.knownDeg), self)
            return
        # If self belongs to an abelian group, then degree 2 suffices.
        if self.group_is_abelian():
            self.suffDeg = 2
        cdef RESL R = self.Resl
        if self.suffDeg == -1:
            coho_logger.info("We have no degree bound yet",self)
        else:
            coho_logger.info("We have the degree bound %d"%(self.suffDeg), self)
        if max_deg>0 and max_deg<self.suffDeg:
            coho_logger.info("We will compute at most out to degree %d"%(max_deg), self)
        while (1):
            self.next()
            if (self.suffDeg!=-1) and (self.knownDeg >= self.suffDeg):
                coho_logger.info("Computation went beyond a previously obtained degree bound",self)
                self.completed = True
            else:
                self.test_for_completion()
            if (self.completed) or ((max_deg!=-1) and (self.knownDeg>=max_deg)):
                break
        self.set_ring()
        self.GenS = singular('basering')
        if self.completed:
            self.make_groebner() # should be known by Benson's test, but not if other criteria were used
        self.RelG = [s.strip() for s in singular.eval('print(%sI)'%(self.prefix)).split(',')]
        self.SingularTime = singular.cputime(self.SingularTime)
        coho_logger.info("Computation of the ring approximation is finished\n", self)

        #####
        ## Verify Benson's strong regularity conjecture
        #####
        fdt = self.fdt
        if fdt:
            alpha = False
            for i in range(1,len(fdt)):
                if fdt[i] > -i:
                    alpha = True
            if fdt[-1] > -len(fdt)+1:
                alpha = True
            if fdt[-1] < -len(fdt)+1:
                raise RuntimeError("Theoretical error: We got a filter degree type %s, but the last value must not be smaller than %d!"%(repr(fdt),-len(fdt)+1))
            if self.alpha>-1:
                raise RuntimeError("""
This result contradicts the weak form
of Benson's regularity conjecture, that
was proved by Peter Symonds. So, there
is an error. Please inform the author!""")
            if alpha:
                print("###########################################")
                print("## COUNTEREXAMPLE FOR THE STRONG FORM OF ##")
                print("## BENSON'S REGULARITY CONJECTURE!!!     ##")
                print("###########################################")
                print("Please inform the author")

        if coho_options['save']:
            coho_logger.info("Storing ring approximation", self)
            safe_save(self, self.autosave_name())

###########################################################################
##
##   UNPICKLING
##
###########################################################################

def COHO_from_key(key):
    """
    Auxiliary function for getting a cohomology ring out of some internal description.

    NOTE:

    This function is only of internal use. In future, this function
    should be replaced by a relational data base. The function returns
    the *completed* cohomology ring.

    TESTS::

        sage: from pGroupCohomology import CohomologyRing
        sage: from pGroupCohomology.modular_cohomology import COHO_from_key
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(720,763,prime=2, from_scratch=True)
        sage: H.make(3)

    We remove ``H`` from the cache. The cohomology of its underlying
    subgroup is still there, and is returned by ``COHO_from_key``::

        sage: del CohomologyRing._cache[H._key]
        sage: H.subgroup_cohomology() is COHO_from_key(H.subgroup_cohomology()._key)
        True

    When calling for the cohomology key of ``H``, it can not be found
    in the cache. Instead, it is reloaded from disk::

        sage: H is COHO_from_key(H._key)
        False

    In fact, it is not only reloaded, but it is completely computed,
    in contrast to ``H``::

        sage: print(H)
        Cohomology ring of SmallGroup(720,763) with coefficients in GF(2)
        <BLANKLINE>
        Computed up to degree 3
        Minimal list of generators:
        [c_2_1: 2-Cocycle in H^*(SmallGroup(720,763); GF(2)),
         c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2)),
         b_3_3: 3-Cocycle in H^*(SmallGroup(720,763); GF(2)),
         c_3_2: 3-Cocycle in H^*(SmallGroup(720,763); GF(2))]
        Minimal list of algebraic relations:
        []
        sage: print(COHO_from_key(H._key))
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

    """
    from pGroupCohomology import CohomologyRing
    _cache = CohomologyRing._cache
    from pGroupCohomology.resolution import coho_options
    # The p-group case
    logging_level = coho_logger.getEffectiveLevel()
    CohomologyRing.global_options('warn')
    import os
    if len(key)==2: # HP will be COHO
        HProot = os.path.split(os.path.split(os.path.split(key[1])[0])[0])[0]  # this is '/'.join(key[1].split('/')[:-3])
        HPstem = os.path.split(os.path.split(os.path.split(key[1])[0])[0])[1]  # this is key[1].split('/')[-3]
        if len(key[0])==2: # SmallGroup
            HP = CohomologyRing(key[0][0],key[0][1], GStem=HPstem)
        else:
            HP = CohomologyRing(gap.eval(key[0][0]), GStem=HPstem)
        # This will work in any case, may compute it from scratch
        coho_logger.setLevel(logging_level)
        if not HP.completed:
            HP.make()
        return HP
    ####
    # By now, we can assume that we have a non primepower group
    # Cache: The easiest case
    HP = _cache.get(key)
    if HP is not None:
        coho_logger.setLevel(logging_level)
        return HP
    if len(key[0])==2:
        # SmallGroup is sufficiently easy, the constructor will do the job
        HP = CohomologyRing(key[0][0],key[0][1], prime=key[-1], GStem=key[1])
        coho_logger.setLevel(logging_level)
        if not HP.completed:
            HP.make()
        return HP
    # We try to help a bit by first loading the subgroup to the cache...
    HN = COHO_from_key(key[2])
    # ... and see if we are lucky enough to find stuff on disk
    from sage.all import load
    from pGroupCohomology.cohomology import COHO
    import os
    try:
        HP = load(os.path.join(COHO.workspace, 'H'+key[1]+'mod%d.sobj'%key[-1]))  # realpath here?
    except:
        HP = CohomologyRing(gap.eval(key[0][0]), prime=key[-1], GStem=key[1],SubgpCohomology=HN)
    coho_logger.setLevel(logging_level)
    if not HP.completed:
        HP.make()
    return HP

def MODCOHO_unpickle(*L):
    """
    Unpickling a cohomology ring.

    TESTS::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(720,763,prime=2, from_scratch=True)
        sage: H.make(3)
        sage: H is loads(dumps(H)) #indirect doctest
        True

    """
    if len(L)==28:
        _prime, GEN, Rel, RelG, lastRel, lastRelevantDeg, knownDeg, suffDeg, completed, Dickson, DuflotRegSeq, alpha, Triangular, StdMon, DG, _gap_group, _Subgp, _SylowGp, SubgroupList, PtoPcapCPdirect, PtoPcapCPtwist, PtoPcapCPdirectSing, PtoPcapCPtwistSing, _Order, _POrder, sgpDickson, _property_dict, SingularTime = L
        cache = []
    elif len(L)==29:
        _prime, GEN, Rel, RelG, lastRel, lastRelevantDeg, knownDeg, suffDeg, completed, Dickson, DuflotRegSeq, alpha, Triangular, StdMon, DG, _gap_group, _Subgp, _SylowGp, SubgroupList, PtoPcapCPdirect, PtoPcapCPtwist, PtoPcapCPdirectSing, PtoPcapCPtwistSing, _Order, _POrder, sgpDickson, _property_dict, SingularTime, cache = L
    else:
        raise ValueError("wrong number of arguments")

    OUT = MODCOHO(None,_prime,None,None) # It is initialised as a ring over GF(_prime), but nothing more.
    from pGroupCohomology.cochain import MODCOCH
    from pGroupCohomology import CohomologyRing
    _cache = CohomologyRing._cache
    OUT._property_dict = dict(unpickle_gap_data(_property_dict))
    OUT._decorator_cache = dict(unpickle_gap_data(cache))
    if OUT._key in _cache:
        return _cache[OUT._key]
    OUT.GStem = OUT._key[1]
    OUT._HP = COHO_from_key(OUT._key[-2])
    HS = OUT._HP
    while isinstance(HS,MODCOHO):
        HS = HS._HP
    OUT._HSyl = HS
    OUT.Resl = OUT._HP.Resl

    # (X.val_str(), X.Deg, X._name, X._rdeg, X._ydeg)
    OUT._prime = _prime
    OUT.Gen = [MODCOCH(OUT,val,deg=D,name=Name,rdeg=rdeg,ydeg=ydeg, is_polyrep=True) for val,D,Name,rdeg,ydeg in GEN]
    bla = [t.val_str() for t in OUT.Gen] # this helps to reconstruct data in the Singular interface after it crashed.
    OUT.degvec = [X.deg() for X in OUT.Gen]
    for firstOdd in range(len(OUT.Gen)):
        if OUT.degvec[firstOdd]%2:
            break
    OUT.firstOdd = int(firstOdd)
    OUT.Rel = Rel
    OUT.RelG = RelG
    OUT.lastRel = lastRel
    OUT.lastRelevantDeg = lastRelevantDeg
    OUT.knownDeg = knownDeg
    OUT.suffDeg = suffDeg
    OUT.completed = completed
    OUT._DuflotRegSeq = [MODCOCH(OUT,val,deg=D,name=Name,rdeg=rdeg,ydeg=ydeg, is_polyrep=True) for val,D,Name,rdeg,ydeg in DuflotRegSeq]
    OUT.alpha = alpha

    # Reconstruct data in GAP
    OUT._Subgp = gap.eval(_Subgp)
    OUT._SylowGp = gap.eval(_SylowGp)
    OUT._gap_group = gap.eval(_gap_group)
    OUT._SubgpBackup = _Subgp
    OUT._SylowGpBackup = _SylowGp
    OUT._gapBackup = _gap_group
    OUT._Order = _Order
    OUT._POrder = _POrder
    OUT.SingularTime = SingularTime
    OUT.Triangular = dict([(i, [MODCOCH(OUT,X[0],deg=X[1],name=X[2],rdeg=X[3],ydeg=X[4], is_polyrep=True) for X in Y]) for i,Y in Triangular])

    # Reconstruct data in Singular:
    if OUT._property_dict.get('use_dp'):
        if len(OUT.degvec)==1:
            singular.eval('ring tmp = %d,(%s),%s'%(_prime, ','.join([x.name() for x in OUT.Gen]), '(a(%d),dp)'%(OUT.degvec[0])))
        else:
            singular.eval('ring tmp = %d,(%s),%s'%(_prime, ','.join([x.name() for x in OUT.Gen]), '(wp%s)'%(str(tuple(OUT.degvec)))))
    else:
        OUT._makeOrderMatrix_()
        singular.eval('ring tmp = %d,(%s),M(%sM)'%(_prime, ','.join([x.name() for x in OUT.Gen]), OUT.prefix))
    if _prime!=2 and OUT.firstOdd<len(OUT.Gen):   # non-commutative case
        singular.eval('degBound = 0')
        singular.eval('def %sr(%d) = superCommutative(%d,%d)'%(OUT.prefix,lastRelevantDeg,OUT.firstOdd+1, len(OUT.Gen)))
    else:
        singular.eval('def %sr(%d) = tmp'%(OUT.prefix,lastRelevantDeg))
    OUT.set_ring()
    if RelG:
        singular.eval(('ideal %sI = '%OUT.prefix)+','.join(RelG))
    else:
        singular.eval('ideal %sI'%OUT.prefix)
    if DG:
        singular.eval(('ideal %sDG = '%OUT.prefix)+','.join(DG))
    else:
        singular.eval('ideal %sDG'%OUT.prefix)
    OUT.StdMon = {}
    for nkey,StdMonN in StdMon:
        OUT.StdMon[nkey]={}
        for monkey,STD in StdMonN:
            if monkey!='1':
                OUT.StdMon[nkey][monkey] = singular.ideal(STD)
            else:
                OUT.StdMon[nkey][monkey] = singular('1')
    OUT._PtoPcapCPdirect = []
    OUT._PtoPcapCPtwist = []
    OUT._PtoPcapCPdirectSing = []
    OUT._PtoPcapCPtwistSing = []
    from pGroupCohomology.cochain import chmap_unpickle
    from sage.interfaces.singular import SingularElement
    OUT_S = singular(OUT._HP)
    for i in range(len(SubgroupList)):
        HX = COHO_from_key(SubgroupList[i])
        OUT._PtoPcapCPdirect.append(chmap_unpickle(OUT._HP,HX,*PtoPcapCPdirect[i]))
        OUT._PtoPcapCPtwist.append(chmap_unpickle(OUT._HP,HX,*PtoPcapCPtwist[i]))
        singular(HX).set_ring()
        OUT._PtoPcapCPtwistSing.append(SingularElement(singular, 'map', OUT_S.name()+','+PtoPcapCPtwistSing[i]))
        OUT._PtoPcapCPdirectSing.append(SingularElement(singular, 'map', OUT_S.name()+','+PtoPcapCPdirectSing[i]))

    OUT.InitSubgroups() # reconstructs many attributes via HP
    OUT.Dickson = Dickson
    _cache[OUT._key] = OUT
    return OUT

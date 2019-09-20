# -*- coding: utf-8 -*-

#*****************************************************************************
#
#    Explore graded isomorphisms of modular cohomology rings of finite groups
#
#    Copyright (C) 2019 Simon A. King <simon.king@uni-jena.de>
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

from sage.interfaces.singular import SingularElement
from sage.all import singular
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.cachefunc import cached_method
from pGroupCohomology import CohomologyRing
from sage.all import cartesian_product_iterator, Integer, Infinity
from sage.rings.polynomial.hilbert import first_hilbert_series
from pGroupCohomology.auxiliaries import coho_logger
import sys

########################################################################
##
##  THE TEST ENGINE

class IsomorphismTest:
    """
    An engine to detect graded isomorphisms between cohomology rings by enumeration.

    NOTE:

    Usually, the isomorphism test engine is only called via
    :meth:`~pGroupCohomology.cohomology.COHO.is_isomorphic`.
    However, the direct use of the test engine allows further
    options.

    EXAMPLES:

    We give an example of two non-isomorphic groups that have isomorphic cohomology
    rings::

        sage: from pGroupCohomology import CohomologyRing
        sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
        sage: CohomologyRing.doctest_setup()
        sage: H173 = CohomologyRing(64, 173)
        sage: H176 = CohomologyRing(64, 176)
        sage: H173.make()
        sage: H176.make()
        sage: CohomologyRing.global_options('info')

    We choose a test engine with a cutoff that is too small to detect isomorphy::

        sage: T = IsomorphismTest(H176, H173, cutoff=60)
        sage: T.explore_isomorphisms()        # long time
        IsomorphismTest(H^*(SmallGroup(64,176); GF(2)), H^*(SmallGroup(64,173); GF(2))):
            Trying to find an isomorphism
        ...
            gen(4) is rigid: b_1_0 --> 1*b_1_0
        H^*(SmallGroup(64,173); GF(2)):
            Determine degree 1 standard monomials
            Determine degree 3 standard monomials
            Determine degree 1 standard monomials
        IsomorphismTest(H^*(SmallGroup(64,176); GF(2)), H^*(SmallGroup(64,173); GF(2))):
            gen(3) is rigid: a_1_1 --> 1*a_1_1
            1 potential assignments for ['gen(4)', 'gen(3)']
            4 potential assignments for ['gen(4)', 'gen(3)', 'gen(5)']
        ...
        H^*(SmallGroup(64,173); GF(2)):
            Determine degree 2 standard monomials
        ...
        IsomorphismTest(H^*(SmallGroup(64,176); GF(2)), H^*(SmallGroup(64,173); GF(2))):
            Verify if we found an isomorphism
            ... Not a homomorphism
            Verify if we found an isomorphism
        ...
            0 potential assignments for ['gen(4)', 'gen(3)', 'gen(5)', 'gen(6)', 'gen(1)', 'gen(2)']
            No conclusion on the existence of an isomorphism.

    The statistic of criteria used in the process is as follows (sorted in order
    to have a reproducible test)::

        sage: sorted(T.statistic.items(), key=repr)
        [('Hilbert series of ideals do not match', 129),
         ('isomorphism test', 43200),
         ('nil-deg', 10),
         ('not homomorphism', 43200),
         (('potential isomorphism', 1), 347),
         (('potential isomorphism', 2), 28),
         (('potential isomorphism', 3), 224),
         (('potential isomorphism', 4), 64),
         (('potential isomorphism', 5), 240),
         (('potential isomorphism', 6), 43200)]

    So, 43200 possibilites to map the 6 generators have been tested, but none of them
    resulted in a homomorphism (so, it wasn't needed to test bijectivity).
    It would be possible to find an isomorphism using a higher cut-off. However,
    we show that using an additional criterion (that in some examples would
    be very difficult to compute) yields the result more easily, as it drastically
    cuts down the number of generator mappings that potentially could extend
    to an isomorphism::

        sage: T = IsomorphismTest(H176, H173, cutoff=60, use_radical=True)
        sage: T.explore_isomorphisms()              # long time
        IsomorphismTest(H^*(SmallGroup(64,176); GF(2)), H^*(SmallGroup(64,173); GF(2))):
            Trying to find an isomorphism
        H^*(SmallGroup(64,173); GF(2)):
            Determine degree 1 standard monomials
        IsomorphismTest(H^*(SmallGroup(64,176); GF(2)), H^*(SmallGroup(64,173); GF(2))):
            gen(4) is rigid: b_1_0 --> 1*b_1_0
        H^*(SmallGroup(64,173); GF(2)):
            Determine degree 1 standard monomials
            Determine degree 3 standard monomials
            Determine degree 1 standard monomials
        IsomorphismTest(H^*(SmallGroup(64,176); GF(2)), H^*(SmallGroup(64,173); GF(2))):
            gen(3) is rigid: a_1_1 --> 1*a_1_1
            1 potential assignments for ['gen(4)', 'gen(3)']
            4 potential assignments for ['gen(4)', 'gen(3)', 'gen(5)']
            64 potential assignments for ['gen(4)', 'gen(3)', 'gen(5)', 'gen(6)']
        ...
            240 potential assignments for ['gen(4)', 'gen(3)', 'gen(5)', 'gen(6)', 'gen(1)']
        H^*(SmallGroup(64,173); GF(2)):
            Determine degree 4 standard monomials
        IsomorphismTest(H^*(SmallGroup(64,176); GF(2)), H^*(SmallGroup(64,173); GF(2))):
            Verify if we found an isomorphism
            ... Not a homomorphism
            Verify if we found an isomorphism
        ...
            ... Not a homomorphism
            Verify if we found an isomorphism
            Isomorphism found!
        ('1*c_2_4',
         '1*b_1_2*b_3_6+1*c_4_9+1*c_2_4*b_1_0*b_1_2',
         '1*a_1_1',
         '1*b_1_0',
         '1*b_1_2',
         '1*b_3_6')
        sage: sorted(T.statistic.items(), key=repr)
        [('Hilbert series of ideals do not match', 171),
         ('Hilbert series of radicals do not match', 286),
         ('isomorphism test', 169),
         ('nil-deg', 10),
         ('not homomorphism', 168),
         (('potential isomorphism', 1), 675),
         (('potential isomorphism', 2), 22),
         (('potential isomorphism', 3), 316),
         (('potential isomorphism', 4), 64),
         (('potential isomorphism', 5), 240),
         (('potential isomorphism', 6), 169)]

    """
    def __init__(self, D, C, use_annihilator = True, use_radical = False, cutoff = 15):
        """
        INPUT:

        - Two cohomology rings `D` (domain) and `C` (codomain)
        - optional: Whether to use annihilators to detect non-isomorphy (default: True)
        - optional: Whether to use radicals to detect non-isomorphy (default: False)
        - optional: when to cut-off lists of candidates of partial isomorphisms (default: 15)

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(64,1)
            sage: H2 = CohomologyRing(64,2)
            sage: T = IsomorphismTest(H1,H2, use_annihilator=False, use_radical=True, cutoff=5)
            sage: T
            IsomorphismTest(H^*(SmallGroup(64,1); GF(2)), H^*(SmallGroup(64,2); GF(2)))
            sage: T.explore_isomorphisms()
            False

        """
        self.use_annihilator = use_annihilator
        self.use_radical = use_radical
        self.cutoff = cutoff
        self.total_candidates = Integer(0)
        self.critical_generators = [] # a generator that can't be mapped
        self.rigid_generators = [] # all generators which have a unique
                                   # candidate for mapping
        self.statistic = {}

        self._domain = D
        assert self._domain.completed, "%r ist not completely computed yet"%D
        self._codomain = C
        assert self._codomain.completed, "%r ist not completely computed yet"%C
        self.prefix = self._domain.prefix+self._codomain.prefix
        self.singular = singular
        self.singular.LIB('primdec')
        #
        self._SD = self.singular(self._domain)
        self._SD.set_ring()
        self.singular.eval('if(defined(%srelation_ideal)>0){kill %srelation_ideal;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %srelation_ideal = ringlist(basering)[4]'%self.prefix)
        self.singular.eval('if(defined(%smapI)>0){kill %smapI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %smapI'%self.prefix)
        #
        self._SC = self.singular(self._codomain)
        self._SC.set_ring()
        self.singular.eval('if(defined(%smapI)>0){kill %smapI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %smapI'%self.prefix)
        L = self._SC.ringlist()
        tmpIC = L[4]
        self._codomain_comm = self.singular('ring(list(%s[1..3],ideal(0)))'%(L.name()))
        i = self.singular._next_var_name()
        self.singular.eval('for (int %s=1; %s<=size(%s[2]); %s++){%s[2][%s]="@"+%s[2][%s];} kill %s;'%(i,i,L.name(),i,L.name(), i,L.name(),i,i))
        if self._domain.base_ring().characteristic()%2:
            self.singular.LIB("poly.lib")
            self._dim_command = 'GKdim'
            #self._R_elim = self.singular('gcRingSum(ring(%s))+%s'%(L.name(),self._SD.name()))
        else:
            self._dim_command = 'dim'
        self._R_elim = self.singular('ring(%s)+%s'%(L.name(),self._SD.name()))
        self._SC.set_ring()
        self.singular.eval('kill '+L.name())
        #self._R_elim.set_ring()
        #
        # First, we create a NON-COMMUTATIVE UNQUOTIENTED version of the domain ring.
        # We only want to see the trivial relations.
        self._domain.set_ring()
        R = self.singular('basering')
        L = self.singular.ringlist('basering')
        tmpID = L[4]
        # Now, we create COMMUTATIVE UNQUOTIENTED versions of the ring
        self._domain_comm = self.singular('ring(list(%s[1..3],ideal(0)))'%(L.name()))
        self.singular.eval('kill '+L.name())
        self._domain_comm.set_ring()
        # "qrels" are *only* the trivial relations in a supercommutative ring!
        self.singular.eval('if(defined(qrels)>0){kill qrels;}')
        self.singular.eval('ideal qrels = imap(%s, %s)'%(R.name(), tmpID.name()))
        self.singular.eval('if(defined(%sfetchI)>0){kill %sfetchI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %sfetchI'%self.prefix)
        R.set_ring()
        self.singular.eval('kill '+tmpID.name())

        #
        self._codomain_comm.set_ring()
        # This time, the quotient relations include the non-trivial relations too.
        self.singular.eval('if(defined(qrels)>0){kill qrels;}')
        self.singular.eval('ideal qrels = imap(%s, %s)'%(self._SC.name(), tmpIC.name()))
        self.singular.eval('if(defined(%sfetchI)>0){kill %sfetchI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %sfetchI'%self.prefix)
        self._SC.set_ring()
        self.singular.eval('kill '+tmpIC.name())

    def __repr__(self):
        """
        TEST::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(64,1)
            sage: H2 = CohomologyRing(64,2)
            sage: IsomorphismTest(H1,H2)
            IsomorphismTest(H^*(SmallGroup(64,1); GF(2)), H^*(SmallGroup(64,2); GF(2)))

        """
        return "IsomorphismTest(%r, %r)"%(self._domain, self._codomain)

    def elements(self, d):
        """
        Iterate over non-zero indecomposable degree-`d` elements of the codomain.

        INPUT:

        `d` -- the degree

        OUTPUT:

        Iterator over strings determining indecomposable elements of degree `d`
        of the codomain.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(64,1)
            sage: H2 = CohomologyRing(64,2)
            sage: T = IsomorphismTest(H1,H2)
            sage: list(T.elements(1))
            ['1*c_1_0', '1*c_1_1', '1*c_1_1+1*c_1_0']
            sage: list(T.elements(2))
            ['1*c_2_1',
             '1*c_2_1+1*c_1_0*c_1_1',
             '1*c_2_2',
             '1*c_2_2+1*c_1_0*c_1_1',
             '1*c_2_2+1*c_2_1',
             '1*c_2_2+1*c_2_1+1*c_1_0*c_1_1']
            sage: list(T.elements(3))
            []

        """
        S = self._codomain.standard_monomials(d)
        ch = self._codomain.base_ring().characteristic()
        coho_logger.debug("test up to {}^{} = {} elements".format(ch,len(S),ch**len(S)), self)
        counter = 0
        for C in cartesian_product_iterator([range(ch)]*len(S)):
            counter += 1
            if any(C):
                sys.stdout.flush()
                indecomposable = False
                for c,s in zip(C,S):
                    if c and not ('*' in s):
                        indecomposable = True
                        break
                if indecomposable:
                    yield '+'.join([repr(c)+'*'+s for c,s in zip(C,S) if c])

    def explore_isomorphisms(self):
        """
        Enumerate and test potential isomophims.

        OUTPUT:

        - A list of generator images (given as strings) of an isomorphism,
          if an isomorphism was found.
        - None, if no isomorphism was found, but non-isomorphy couldn't be asserted.
        - False, if the cohomology rings are not isomorphic.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H156 = CohomologyRing(64,156)
            sage: H156.make()
            sage: H158 = CohomologyRing(64,158)
            sage: H158.make()
            sage: T = IsomorphismTest(H156, H158, cutoff = 2)
            sage: T.explore_isomorphisms()
            ('1*a_1_1*a_3_2+1*c_4_4',
             '1*c_4_5+1*c_4_4',
             '1*a_1_0',
             '1*a_1_1',
             '1*a_1_2',
             '1*a_3_2',
             '1*a_3_3')
            sage: T = IsomorphismTest(H156, H158, cutoff = 1)
            sage: T.explore_isomorphisms()
            sage: H85 = CohomologyRing(64, 85)
            sage: H173 = CohomologyRing(64, 173)
            sage: H85.make()
            sage: H173.make()
            sage: H85.degvec == H173.degvec
            True
            sage: H85.poincare_series() == H173.poincare_series()
            True
            sage: T = IsomorphismTest(H85, H173, cutoff = 10, use_radical = True)
            sage: T.explore_isomorphisms()
            False

        """
        coho_logger.info("Trying to find an isomorphism", self)
        self._clear_candidates()
        self.exhaustive = True
        self.not_exhausted_generators = set([])
        orig_gens = [(x.rdeg(), x.ydeg(), x.deg(), i+1) for i,x in enumerate(self._domain.Gen) if not x.rdeg()]
        orig_gens.sort() # heuristic: those which come first are more likely to be rigid.
        while True:
            n_rigids = len(self.rigid_generators)
            raw_Sizes = []
            for rdeg,ydeg,deg,nb in orig_gens:
                raw_Sizes.append((len(self.candidates_of_gens((nb,),len(self.rigid_generators))), rdeg, ydeg, deg, nb))
            if len(self.rigid_generators)==n_rigids:
                break
        raw_Sizes.sort()
        Rigids = []
        Sizes = []
        CutBranches = []
        coho_logger.debug("iterating over %d raw sizes", self, len(raw_Sizes))
        for (l,r,y,d,g) in raw_Sizes:
            if l==1:
                Rigids.append((r,y,d,l,g))
            elif g in self.not_exhausted_generators:
                CutBranches.append((r,y,d,l,g))
            else:
                Sizes.append((r,y,d,l,g))
        Sizes = Rigids+Sizes+CutBranches
        Regs = []
        Knowns = [p[4] for p in Sizes]
        for i,x in enumerate(self._domain.Gen):
            if x.rdeg():
                if i+1 not in Knowns:
                    Regs.append((x.deg(),0,0,0, i+1))
        Regs.sort()
        Sizes.extend(Regs)
        coho_logger.debug("now determining candidates for %d elements", self, len(Sizes))
        Cands = self.candidates_of_gens(tuple([p[4] for p in Sizes]),len(self.rigid_generators))
        if Cands:
            coho_logger.info("Isomorphism found!", self)
            return Cands[0]
        if self.exhaustive or self.critical_generators:
            coho_logger.info("There is definitely no isomorphism", self)
            return False
        coho_logger.info("No conclusion on the existence of an isomorphism.", self)

    def _clear_candidates(self):
        """
        Clear image candidates from cache that has **not** been exhaustively tested.

        Used internally, not explicitly tested (but implicitly tested elsewhere).
        """
        clear_list = [k for k in self.candidates_of_gens.cache.keys() if k[0][-1] and any([e in self.not_exhausted_generators for e in k[0][0]])]
        for k in clear_list:
            del self.candidates_of_gens.cache[k]

    @cached_method
    def candidates_of_gens(self, Gens, number_of_rigids, allow_cutoff = True):
        """
        Return a list of partial mappings of generators of the domain that could
        potentially extend to an isomorphism.

        NOTE:

        This method is merely of internal use in :meth:`explore_isomorphisms`.

        INPUT:

        - A tuple of numbers, denoting the generators being mapped. Below, we refer
          to them as "active" generators.
        - The number of generators with a unnique image that have been found so far
        - optional: Whether to allow the list of potential images being cut.

        OUTPUT:

        A list of tuples defining mappings of the active generators possibly
        extending to an isomorphism. The length of each tuple coincide with the
        total number of generators, where in the position of the active generators
        the possible image is given as string; all other tuple entries are zero.

        NOTE:

        The number of generators with a unique image is only used for caching.
        If later more generators with a unique image have been found, it makes sense
        to revisit the lists of partial assignments, because their length might
        be drastically reduced when knowing the the unique images of more generators.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H85 = CohomologyRing(64, 85)
            sage: H173 = CohomologyRing(64, 173)
            sage: H85.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H85, H173, cutoff = 10)
            sage: T.exhaustive = True
            sage: T.not_exhausted_generators = set([])
            sage: T.candidates_of_gens((1,),0)
            [('1*c_2_4', 0, 0, 0, 0, 0),
             ('1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*a_1_1*b_1_2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*a_1_1*b_1_2+1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0^2+1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0^2+1*a_1_1*b_1_2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0^2+1*a_1_1*b_1_2+1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*a_1_1*b_1_2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*a_1_1*b_1_2+1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*b_1_0^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*b_1_0^2+1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*b_1_0^2+1*a_1_1*b_1_2+1*c_2_4', 0, 0, 0, 0, 0),
             ('1*b_1_0*b_1_2+1*b_1_0^2+1*a_1_1*b_1_2+1*a_1_1^2+1*c_2_4', 0, 0, 0, 0, 0)]

        If too many potential candidates of generator images arise, the list will be cut::

            sage: CohomologyRing.global_options('debug')
            sage: T.candidates_of_gens((1,2),0)
            ...
            IsomorphismTest(H^*(SmallGroup(64,85); GF(2)), H^*(SmallGroup(64,173); GF(2))):
                      cutting list of nonzero elements
                      cutting list of candidates
                      20 potential assignments for ['gen(1)', 'gen(2)']
            [('1*c_2_4', '1*c_4_9', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*a_1_1^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*a_1_1^2+1*c_2_4^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*a_1_1*b_1_2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*a_1_1*b_1_2+1*c_2_4^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*a_1_1*b_1_2+1*c_2_4*a_1_1^2', 0, 0, 0, 0),
             ('1*c_2_4',
              '1*c_4_9+1*c_2_4*a_1_1*b_1_2+1*c_2_4*a_1_1^2+1*c_2_4^2',
              0,
              0,
              0,
              0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0^2+1*c_2_4^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0^2+1*c_2_4*a_1_1^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0^2+1*c_2_4*a_1_1^2+1*c_2_4^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0^2+1*c_2_4*a_1_1*b_1_2', 0, 0, 0, 0),
             ('1*c_2_4',
              '1*c_4_9+1*c_2_4*b_1_0^2+1*c_2_4*a_1_1*b_1_2+1*c_2_4^2',
              0,
              0,
              0,
              0),
             ('1*c_2_4',
              '1*c_4_9+1*c_2_4*b_1_0^2+1*c_2_4*a_1_1*b_1_2+1*c_2_4*a_1_1^2',
              0,
              0,
              0,
              0),
             ('1*c_2_4',
              '1*c_4_9+1*c_2_4*b_1_0^2+1*c_2_4*a_1_1*b_1_2+1*c_2_4*a_1_1^2+1*c_2_4^2',
              0,
              0,
              0,
              0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0*b_1_2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0*b_1_2+1*c_2_4^2', 0, 0, 0, 0),
             ('1*c_2_4', '1*c_4_9+1*c_2_4*b_1_0*b_1_2+1*c_2_4*a_1_1^2', 0, 0, 0, 0),
             ('1*c_2_4',
              '1*c_4_9+1*c_2_4*b_1_0*b_1_2+1*c_2_4*a_1_1^2+1*c_2_4^2',
              0,
              0,
              0,
              0)]

        It can happen that one generator (or a list of generators) cannot be
        mapped in a way that extends to an isomorphism. This happens, for example,
        if a generator of the domain in degree `d` has a nilpotency degree that
        doesn't match the nilpotency degree of any degree-`d` element of to codomain.
        In that case, there cannot be an isomorphism::

            sage: T.candidates_of_gens((3,),0)
            ...
            IsomorphismTest(H^*(SmallGroup(64,85); GF(2)), H^*(SmallGroup(64,173); GF(2))):
                      test up to 2^3 = 8 elements
                      nilpotency degree of '1*a_1_1' doesn't match generator 3
                      nilpotency degree of '1*b_1_0' doesn't match generator 3
                      nilpotency degree of '1*b_1_0+1*a_1_1' doesn't match generator 3
                      nilpotency degree of '1*b_1_2' doesn't match generator 3
                      nilpotency degree of '1*b_1_2+1*a_1_1' doesn't match generator 3
                      nilpotency degree of '1*b_1_2+1*b_1_0' doesn't match generator 3
                      nilpotency degree of '1*b_1_2+1*b_1_0+1*a_1_1' doesn't match generator 3
            []

        If one now tries to map another generator, we already know that there
        cannot be an isomorphism, thus, the answer is immediate::

            sage: T.candidates_of_gens((4,),0)
                      There cannot be a homomorphism, (gen(3)) cannot be mapped
            []

        """
        C = []
        counter = 0
        if self.candidates_of_gens.is_in_cache(Gens, number_of_rigids, False):
            return self.candidates_of_gens(Gens, number_of_rigids, False)
        Rigids = []
        try:
            if self.critical_generators:
                coho_logger.info("There cannot be a homomorphism, (%s) cannot be mapped"%', '.join(['gen(%d)'%k for k in self.critical_generators]), self)
                return []
            if len(Gens)==1:
                i = Gens[0]
                old_candidates = None
                for nb_rig in range(number_of_rigids):
                    if self.candidates_of_gens.is_in_cache(Gens, nb_rig):
                        old_candidates = self.candidates_of_gens(Gens, nb_rig)
                        break
                if old_candidates is not None:
                    if not old_candidates:
                        return old_candidates
                else:
                    nil_deg = self._domain.gen(i).nilpotency_degree()
                Ims = [0]*len(self._domain.Gen)
                for g in self.rigid_generators:
                    if i==g[0]:
                        Ims[i-1] = g[1]
                        return [tuple(Ims)]
                    Ims[g[0]-1] = g[1]
                    if g[0] not in Gens:
                        Rigids.append(g[0])
                # Heuristic: Generally, "regular" generators (that form a
                # regular sequence) will have many possible images---here is
                # where the size of the ring's automorphism group may become
                # problematic. So, we may cut the candidate list short.
                for y in old_candidates or self.elements(self._domain.gen(i).deg()):
                    if (not old_candidates):
                        if self._codomain(y).nilpotency_degree()!=nil_deg:
                            coho_logger.debug("nilpotency degree of %r doesn't match generator %d", self,y,i)
                            self.statistic['nil-deg'] = self.statistic.get('nil-deg',0) + 1
                            continue
                        if self.rigid_generators:
                            # Could be that computing annihilator is easier
                            # with just a single element...
                            ShortIms = [0]*len(self._domain.Gen)
                            ShortIms[i-1] = y
                            if not self.potential_partial_isomorphism(ShortIms):
                                continue
                        Ims[i-1] = y
                    else:
                        Ims[i-1] = y[i-1]
                    if self.potential_partial_isomorphism(Ims):
                        counter += 1
                        C.append(tuple(Ims))
                        if allow_cutoff and (counter >= (6 if not self.rigid_generators else 3)*self.cutoff):
                            coho_logger.debug("cutting list of nonzero elements", self)
                            self.not_exhausted_generators.add(i)
                            self.exhaustive = False
                            break
                if not C and not any([k in self.not_exhausted_generators for k in Gens]):
                    if not self.critical_generators:
                        self.critical_generators = list(Gens)
                    else:
                        self.critical_generators.append(i)
                if len(C)==1:
                    if Gens[0] not in [r[0] for r in self.rigid_generators]:
                        coho_logger.info("gen(%d) is rigid: %s --> %s"%(Gens[0],self._domain.gen(Gens[0]).name(),C[0][Gens[0]-1]), self)
                        self.rigid_generators.append((Gens[0],C[0][Gens[0]-1]))
                if not i in self.not_exhausted_generators:
                    self.candidates_of_gens.set_cache(C, Gens, number_of_rigids, False)
                return C
            h1 = -1 #len(Gens)//2
            h2 = h1 #-1 if len(Gens)<=2 else (-2 if len(Gens)==3 else -3)
            FirstHalf = self.candidates_of_gens(Gens[:h1],len(self.rigid_generators))
            if FirstHalf:
                SecondHalf = self.candidates_of_gens(Gens[h1:],len(self.rigid_generators))
                #~ coho_logger.info("Testing up to %d*%d = %d assignments"%(len(FirstHalf),len(SecondHalf), len(FirstHalf)*len(SecondHalf)), self)
            else:
                SecondHalf = []
                coho_logger.info("No candidates remain", self)
            self._remove_partial_relations_from_cache(len(Gens))
            self._remove_candidates_from_cache(len(Gens))
            if FirstHalf:
                for Ims1,Ims2 in cartesian_product_iterator([FirstHalf, SecondHalf]):
                    Ims = [None if (0!=a!=b!=0) else (a if a else b) for a,b in zip(Ims1,Ims2)]
                    for g in self.rigid_generators:
                        if 0!=Ims[g[0]-1]!=g[1]:
                            raise RuntimeError("Value of rigid generator is not assumed")
                        else:
                            Ims[g[0]-1] = g[1]
                            if g[0] not in Gens:
                                Rigids.append(g[0])
                    if None in Ims:
                        continue
                    if (0 in Ims and len(set(Ims))-1<len(Ims)-Ims.count(0)) or (0 not in Ims and len(set(Ims))<len(Ims)-Ims.count(0)):
                        self.statistic['triviality'] = self.statistic.get('triviality',0) + 1
                        continue
                    if self.potential_partial_isomorphism(Ims):
                        counter += 1
                        C.append(tuple(Ims))
                        if len(Gens)==len(self._domain.Gen):
                            return C
                        if allow_cutoff and (counter >= self.cutoff*(2**(len(Ims)-Ims.count(0)-len(self.rigid_generators)-1))):
                            coho_logger.debug("cutting list of candidates", self)
                            for k in Gens:
                                self.not_exhausted_generators.add(k)
                            self.exhaustive = False
                            break
            if len(C)==1:
                old_rigids = [x[0] for x in self.rigid_generators]
                for g in Gens:
                    if g not in old_rigids:
                        self.rigid_generators.append((g,C[0][g-1]))
                        coho_logger.info("further rigid generator gen(%d) --> %s"%(g,C[0][g-1]), self)
            if not C and not any([k in self.not_exhausted_generators for k in Gens]):
                if not self.critical_generators:
                    self.critical_generators = list(Gens)
                else:
                    self.critical_generators.extend(Gens)
            coho_logger.info("%d potential assignments for %r",self, len(C), ["gen(%d)"%g for g in Gens])
            if all(k not in self.not_exhausted_generators for k in Gens):
                self.candidates_of_gens.set_cache(C, Gens, number_of_rigids, False)
                if Rigids:
                    self.candidates_of_gens.set_cache(C, tuple(Rigids)+Gens, number_of_rigids, False)
            if allow_cutoff and Rigids:
                self.candidates_of_gens.set_cache(C, tuple(Rigids)+Gens, number_of_rigids, True)
            return C
        finally:
            pass

    @lazy_attribute
    def unquotiented_domain(self):
        """
        A representation of the domain in Singular, without its quotient relations.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H85 = CohomologyRing(64, 85)
            sage: H173 = CohomologyRing(64, 173)
            sage: H85.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H85, H173)
            sage: T.unquotiented_domain
            polynomial ring, over a field, global ordering
            // coefficients: ZZ/2
            // number of vars : 6
            //        block   1 : ordering M
            //                  : names    c_2_4 c_4_9 a_1_0 a_1_1 b_1_2 a_3_6
            //                  : weights      2     4     1     1     1     3
            //                  : weights     -1    -1     0     0     0     0
            //                  : weights      0     0    -1    -1     0    -1
            //                  : weights     -1     0     0     0     0     0
            //                  : weights      0     0    -1     0     0     0
            //                  : weights      0     0     0    -1     0     0
            //        block   2 : ordering C

        """
        self._domain.set_ring()
        L = self.singular('ringlist(basering)')
        self.singular.eval('%s[4]=ideal(0)'%L.name())
        R = L.ring()
        singular.eval('kill %s'%L.name())
        R.set_ring()
        self.singular.eval('if(defined(%selimI)>0){kill %selimI;}'%(self.prefix,self.prefix))
        self.singular.eval('ideal %selimI'%self.prefix)
        return R

    def _remove_partial_relations_from_cache(self, n):
        """
        Remove cached partial relations for all subrings of less than n generators.

        Used internally, not explicitly tested (but implicitly tested elsewhere).
        """
        keys = [k for k in self.partial_relations.cache.keys() if k[0][0].count(True)<n]
        for k in keys:
            del self.partial_relations.cache[k]

    def _remove_candidates_from_cache(self, n):
        """
        Remove image candidates for all sets of less than or equal n and more
        than 1 generators. This also removes cached Hilbert data.

        Compare ._clear_candidates(), which removes everything that has been cut!

        Used internally, not explicitly tested (but implicitly tested elsewhere).
        """
        keys = [k for k in self.candidates_of_gens.cache.keys() if 1<len(k[0][0])<=n]
        for k in keys:
            del self.candidates_of_gens.cache[k]
        keys = [k for k in self.hilbert_of_preimage.cache.keys() if len(k[0][0])<=n]
        for k in keys:
            del self.hilbert_of_preimage.cache[k]
        keys = [k for k in self.hilbert_of_preimage_annihilator.cache.keys() if len(k[0][0])<=n]
        for k in keys:
            del self.hilbert_of_preimage_annihilator.cache[k]
        keys = [k for k in self.hilbert_of_preimage_radical.cache.keys() if len(k[0][0])<=n]
        for k in keys:
            del self.hilbert_of_preimage_radical.cache[k]

    @cached_method
    def partial_relations(self,T):
        """
        Algebraic relations for a subset of the generators of the domain.

        INPUT:

        A tuple whose length is the number of generators in positive degree
        of the domain. The entries are either true or false.

        OUTPUT:

        An ideal that defines the subring spanned by the denoted generators
        as a quotient ring.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H85 = CohomologyRing(64, 85)
            sage: H173 = CohomologyRing(64, 173)
            sage: H85.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H85, H173)
            sage: T.partial_relations((True,False,True,False,True,False))
            a_1_0^2,
            a_1_0*b_1_2^2
            sage: T._domain.rels()
            ['a_1_0^2', 'a_1_1^2', 'a_1_0*b_1_2^2', 'a_1_0*a_3_6', 'a_3_6^2']

        Note that the computation can be costly, as elimination is involved.

        """
        self.unquotiented_domain.set_ring()
        H1 = self._domain
        self.singular.eval('%selimI=eliminate(imap(%sr(%d), %sI),%s)'%(self.prefix,H1.prefix,H1.knownDeg,H1.prefix, '*'.join([H1.gen(i+1).name() for i,x in enumerate(T) if not x])))
        self._SD.set_ring()
        return self.singular('imap(%s,%selimI)'%(self.unquotiented_domain.name(),self.prefix))

    def set_images(self, im_gens):
        """
        Map some generators, aiming to test whether that may extend to an isomorphism.

        INPUT:

        A list of strings or 0, such that the `i`-th entry defines the image
        in the codomain of the `i`-th generator of the domain.

        OUTPUT:

        There is no output, but various attributes of the test engine are redefined.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(27,3)
            sage: H1.make()
            sage: H2 = CohomologyRing(81,9)
            sage: H2.make()
            sage: X = IsomorphismTest(H1,H2)
            sage: X.set_images(("2*b_2_3+1*b_2_1",0,0,0,0,0,0,0,0))
            sage: X.hilbert_of_image()
            t^20 - 2*t^19 - 2*t^18 + 2*t^17 + 6*t^16 + 4*t^15 - 10*t^14 - 10*t^13 - t^12 + 12*t^11 + 14*t^10 - 2*t^9 - 11*t^8 - 12*t^7 + 2*t^6 + 10*t^5 + 4*t^4 - 2*t^3 - 4*t^2 + 1
            sage: X.set_images(("2*b_2_1+1*b_2_0",0,0,0,0,0,0,0,0))
            sage: X.hilbert_of_image()
            -t^18 + 4*t^16 + 2*t^15 - 5*t^14 - 8*t^13 - t^12 + 10*t^11 + 9*t^10 - 9*t^8 - 10*t^7 + t^6 + 8*t^5 + 5*t^4 - 2*t^3 - 4*t^2 + 1

        """
        self.total_candidates += 1
        if len(im_gens)!=len(self._domain.Gen):
            raise ValueError("%d generators, but %d images are given"%(len(self._domain.Gen),len(im_gens)))
        self._im_gens = im_gens
        self._SC.set_ring()
        if hasattr(self,'_Smap'):
            self.singular.eval('kill %s'%self._Smap.name())
            self.singular.eval('map %s = %s, ideal(%s)'%(self._Smap.name(), self._SD.name(), ','.join([str(x) for x in im_gens])))
        else:
            self._Smap = SingularElement(self.singular,'map','%s, ideal(%s)'%(self._SD.name(), ','.join([str(x) for x in im_gens])))
        self._codomain_comm.set_ring()
        self._R_elim.set_ring()
        try:
            if 'urbild_GB' in self.__dict__:
                self.singular.eval('kill %s'%(self.urbild_GB.name()))
                del self.__dict__['urbild_GB']
        except BaseException:
            pass
        if 'hilbert_of_image' in self.__dict__:
            del self.__dict__['hilbert_of_image']
        if 'hilbert_of_image_radical' in self.__dict__:
            del self.__dict__['hilbert_of_image_radical']
        if 'hilbert_of_image_annihilator' in self.__dict__:
            del self.__dict__['hilbert_of_image_annihilator']
        if hasattr(self, '_J_elim'):
            self.singular.eval('%s = ideal(matrix(ideal(fetch(%s,%s)))-matrix(ideal(%s)))'%(self._J_elim.name(), self._SC.name(),self._Smap.name(),self.singular.eval('varstr(%s)'%self._SD.name())))
        else:
            self._J_elim = self.singular('ideal(matrix(ideal(fetch(%s,%s)))-matrix(ideal(%s)))'%(self._SC.name(),self._Smap.name(),self.singular.eval('varstr(%s)'%self._SD.name())))
        self._SC.set_ring()

########
##
##   Hilbert functions of the ideal generated by some generators resp. their images must coincide.

    @lazy_attribute
    def hilbert_of_image(self):
        """
        Hilbert series of the ideal generated by the candidate images.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(27,3)
            sage: H1.make()
            sage: H2 = CohomologyRing(81,9)
            sage: H2.make()
            sage: X = IsomorphismTest(H1,H2)
            sage: X.set_images(("2*b_2_1+1*b_2_0","2*b_2_3+1*b_2_1",0,0,0,0,0,0,0))
            sage: X.hilbert_of_image()
            t^20 - 5*t^18 - 2*t^17 + 9*t^16 + 10*t^15 - 4*t^14 - 18*t^13 - 10*t^12 + 10*t^11 + 18*t^10 + 10*t^9 - 10*t^8 - 18*t^7 - 4*t^6 + 10*t^5 + 9*t^4 - 2*t^3 - 5*t^2 + 1

        """
        self._SC.set_ring()
        #--tmpI = self._Smap.ideal().std()
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,self._Smap.name()))
        self._codomain_comm.set_ring()
        # qrels contains *all* quotient relations, including the nontrivials.
        #--tmpI2 = self.singular('fetch(%s,%s)+qrels'%(self._SC.name(),tmpI.name()))
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels'%(self.prefix,self._SC.name(),self.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._codomain.degvec)

    @lazy_attribute
    def hilbert_of_image_annihilator(self):
        """
        Hilbert series of the annihilator of the ideal generated by the candidate images.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(27,3)
            sage: H1.make()
            sage: H2 = CohomologyRing(81,9)
            sage: H2.make()
            sage: X = IsomorphismTest(H1,H2)
            sage: X.set_images(("2*b_2_1+1*b_2_0","2*b_2_3+1*b_2_1",0,0,0,0,0,0,0))
            sage: X.hilbert_of_image_annihilator()
            -t^20 + 3*t^18 + 2*t^17 - t^16 - 6*t^15 - 6*t^14 + 2*t^13 + 8*t^12 + 10*t^11 - 10*t^9 - 8*t^8 - 2*t^7 + 6*t^6 + 6*t^5 + t^4 - 2*t^3 - 3*t^2 + 1

        """
        self._SC.set_ring()
        #--tmpI = self._Smap.ideal().std()
        ActiveGens = [i for i,x in enumerate(self._im_gens) if x]
        #~ if ActiveGens:
            #~ d = [self._codomain.Gen[i].deg() for i in ActiveGens]
            #~ SmallerGens = ','.join([x.name() for x in self._codomain.Gen if x.deg()<d])
            #~ if not SmallerGens:
                #~ SmallerGens = 0
        #~ else:
            #~ SmallerGens = 0
        #~ self.singular.eval('%smapI = std(ideal(%s)+ideal(%s))'%(self.prefix,SmallerGens,self._Smap.name()))
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix, self._Smap.name()))
        self.singular.eval('%smapI = std(quotient(std(0),%smapI))'%(self.prefix,self.prefix))
        self._codomain_comm.set_ring()
        # qrels contains *all* quotient relations, including the nontrivials.
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels'%(self.prefix,self._SC.name(),self.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._codomain.degvec)

    @lazy_attribute
    def hilbert_of_image_radical(self):
        """
        Hilbert series of the radical of the ideal generated by the candidate images.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(27,3)
            sage: H1.make()
            sage: H2 = CohomologyRing(81,9)
            sage: H2.make()
            sage: X = IsomorphismTest(H1,H2)
            sage: X.set_images(("2*b_2_1+1*b_2_0","2*b_2_3+1*b_2_1",0,0,0,0,0,0,0))
            sage: X.hilbert_of_image_radical()
            t^16 - 2*t^15 - 3*t^14 + 6*t^13 + 6*t^12 - 6*t^11 - 13*t^10 + 2*t^9 + 18*t^8 + 2*t^7 - 13*t^6 - 6*t^5 + 6*t^4 + 6*t^3 - 3*t^2 - 2*t + 1

        """
        #~ self._SC.set_ring()
        #--tmpI = self._Smap.ideal().std()
        #~ self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,self._Smap.name()))
        #~ self.singular.eval('%smapI = std(radical(%smapI))'%(self.prefix,self.prefix))
        self._codomain_comm.set_ring()
        # qrels contains *all* quotient relations, including the nontrivials.
        self.singular.eval('%sfetchI = std(radical(ideal(imap(%s,%s))+qrels))'%(self.prefix, self._SC.name(), self._Smap.name()))
        #~ self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels'%(self.prefix,self._SC.name(),self.prefix))
        #~ self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._codomain.degvec)

    @cached_method
    def hilbert_of_preimage(self, Gens):
        """
        Hilbert series of the ideal generated by a subset of the ring generators.

        INPUT:

        A tumple of numbers denoting the generators being chosen.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H1 = CohomologyRing(27,3)
            sage: H1.make()
            sage: H2 = CohomologyRing(81,9)
            sage: H2.make()
            sage: X = IsomorphismTest(H1,H2)
            sage: X.hilbert_of_preimage((1,2))
            t^19 - 2*t^18 - 3*t^17 + 5*t^16 + 6*t^15 - t^14 - 11*t^13 - 8*t^12 + 8*t^11 + 11*t^10 + 7*t^9 - 6*t^8 - 14*t^7 - 3*t^6 + 7*t^5 + 8*t^4 - t^3 - 5*t^2 + 1

        Note that using the Hilbert series of the ideal generated by the second
        ring generator, one can prove that the two cohomology rings are not isomorphic,
        although their Poincaré series and generator degrees are equal::

            sage: H1.poincare_series() == H2.poincare_series()
            True
            sage: H1.degvec == H2.degvec
            True
            sage: for c in X.elements(2):
            ....:     T = (0,c)+(0,)*7
            ....:     X.set_images(T)
            ....:     if X.hilbert_of_preimage((2,)) == X.hilbert_of_image():
            ....:         print(c)

        The point is that no degree-`2` element of the codomain generates an
        ideal with the same Hilbert series as the sedond generator (which also
        is in degree `2`) of the domain.

        """
        self._SD.set_ring()
        #--tmpI = self.singular('std(ideal(%s))'%(','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,','.join(['var(%d)'%i for i in Gens])))
        self._domain_comm.set_ring()
        # qrels only contains the "trivial" relations a^2=0. That's why we now add the nontrivials...
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels+imap(%sr(%d),%sI)'%(self.prefix,self._SD.name(),self.prefix,self._domain.prefix,self._domain.knownDeg,self._domain.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._domain.degvec)

    @cached_method
    def hilbert_of_preimage_annihilator(self, Gens):
        """
        Hilbert series of the annihilator of the ideal generated by some ring
        generators of the domain.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H176 = CohomologyRing(64, 176)
            sage: H173 = CohomologyRing(64, 173)
            sage: H176.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H176, H173)
            sage: T.set_images((0,0,'a_1_1','b_1_0',0,0))
            sage: T.hilbert_of_image_annihilator() == T.hilbert_of_preimage_annihilator((3,4))
            True
            sage: T.hilbert_of_preimage_annihilator((3,4))
            -t^9 + 2*t^8 - t^7 - t^6 + t^5 + t^4 + t^3 - 3*t^2 + 1

        """
        self._SD.set_ring()
        #~ d = [self._domain.Gen[i-1].deg() for i in Gens]
        #~ SmallerGens = ','.join([x.name() for x in self._domain.Gen if x.deg()<d])
        #~ if not SmallerGens:
            #~ SmallerGens = 0
        #--tmpI = self.singular('std(ideal(%s))'%(','.join(['var(%d)'%i for i in Gens])))
        #~ self.singular.eval('%smapI = std(ideal(%s)+ideal(%s))'%(self.prefix, SmallerGens,','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix, ','.join(['var(%d)'%i for i in Gens])))
        self.singular.eval('%smapI = std(quotient(std(0),%smapI))'%(self.prefix,self.prefix))
        self._domain_comm.set_ring()
        # qrels only contains the "trivial" relations a^2=0. That's why we now add the nontrivials...
        self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels+imap(%sr(%d),%sI)'%(self.prefix,self._SD.name(),self.prefix,self._domain.prefix,self._domain.knownDeg,self._domain.prefix))
        self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._domain.degvec)

    @cached_method
    def hilbert_of_preimage_radical(self, Gens):
        """
        Hilbert series of the radical of the ideal generated by some ring
        generators of the domain.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H176 = CohomologyRing(64, 176)
            sage: H173 = CohomologyRing(64, 173)
            sage: H176.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H176, H173)
            sage: T.set_images((0,0,'a_1_1','b_1_0',0,0))
            sage: T.hilbert_of_image_radical() == T.hilbert_of_preimage_radical((3,4))
            True
            sage: T.set_images(('a_1_1*b_1_2','c_2_4**2','a_1_1','b_1_0',0,0))
            sage: T.hilbert_of_image_radical() == T.hilbert_of_preimage_radical((1,2,3,4))
            False

        """
        #~ self._SD.set_ring()
        #--tmpI = self.singular('std(ideal(%s))'%(','.join(['var(%d)'%i for i in Gens])))
        #~ self.singular.eval('%smapI = std(ideal(%s))'%(self.prefix,','.join(['var(%d)'%i for i in Gens])))
        #~ self.singular.eval('%smapI = std(radical(%smapI))'%(self.prefix,self.prefix))
        self._domain_comm.set_ring()
        # qrels only contains the "trivial" relations a^2=0. That's why we now add the nontrivials...
        self.singular.eval('%sfetchI = std(radical(ideal(%s)+qrels+imap(%sr(%d),%sI)))'%(self.prefix,
                ','.join(['var(%d)'%i for i in Gens]),
                self._domain.prefix,self._domain.knownDeg,self._domain.prefix))
        #~ self.singular.eval('%sfetchI = fetch(%s,%smapI)+qrels+imap(%sr(%d),%sI)'%(self.prefix,self._SD.name(),self.prefix,self._domain.prefix,self._domain.knownDeg,self._domain.prefix))
        #~ self.singular.eval('attrib(%sfetchI,"isSB",1)'%self.prefix)
        return first_hilbert_series(self.singular('%sfetchI'%(self.prefix)), self._domain.degvec)

    @lazy_attribute
    def urbild_GB(self):
        r"""
        An ideal that allows the computation of preimages of a ring homomorphism.

        NOTE:

        It requires elimination, thus, can be costly.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H176 = CohomologyRing(64, 176)
            sage: H173 = CohomologyRing(64, 173)
            sage: H176.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H176, H173)
            sage: T.set_images(('c_2_4', 'b_1_2*b_3_6+1*c_4_9+1*c_2_4*b_1_0*b_1_2',
            ....:     'a_1_1', 'b_1_0', 'b_1_2', 'b_3_6'))
            sage: T.urbild_GB
            @a_1_1+a_1_1,
            @b_1_0+b_1_0,
            @b_1_2+b_1_2,
            @c_2_4+c_2_4,
            @b_3_6+b_3_6,
            @c_4_9+b_1_2*b_3_6+c_4_9+c_2_4*b_1_0*b_1_2

        Since all generators of the codomain occur as leading monomials (with
        name prepended by "@"), the result shows that we have a surjection.

        """
        coho_logger.debug(">>> need elimination...", self)
        self._R_elim.set_ring()
        return self._J_elim.groebner()

    def is_homomorphism(self):
        r"""
        Test if the given generator images define a homomorphism.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H176 = CohomologyRing(64, 176)
            sage: H173 = CohomologyRing(64, 173)
            sage: H176.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H176, H173)
            sage: T.set_images(('c_2_4', 'b_1_2*b_3_6+1*c_4_9+1*c_2_4*b_1_0*b_1_2', 'a_1_1', 'b_1_0', 'b_1_2', 'b_3_6'))
            sage: T.is_homomorphism()
            True
            sage: T.set_images(('c_2_4', 'b_1_2*b_3_6+1*c_4_9+1*c_2_4*b_1_0*b_1_2', 'a_1_1', 'b_1_2', 'b_1_0', 'b_3_6'))
            sage: T.is_homomorphism()
            False

        """
        self._SD.set_ring()
        self._SC.set_ring()
        return self.singular.eval('size(NF(%s(%srelation_ideal),std(0)))'%(self._Smap.name(),self.prefix))=='0'

    def potential_partial_isomorphism(self, im_gens):
        """
        Test if a partial assignment of generator images may extend to an isomorphism.

        INPUT:

        A list or tuple of generator images, some of them may be zero.

        OUTPUT:

        The result of some tests telling whether it seems possible to replace
        the zero assignments to something that yields a ring isomorphism.
        The specific tests depend on the parameters used to create the test
        engine.

        EXAMPLES::

            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H176 = CohomologyRing(64, 176)
            sage: H173 = CohomologyRing(64, 173)
            sage: H176.make()
            sage: H173.make()
            sage: T = IsomorphismTest(H176, H173)
            sage: T.potential_partial_isomorphism(('c_2_4', 'b_1_2*b_3_6+1*c_4_9+1*c_2_4*b_1_0*b_1_2',0,0,0,0))
            True
            sage: T.potential_partial_isomorphism(('b_1_2*b_1_0', 'b_1_2*b_3_6+1*c_4_9+1*c_2_4*b_1_0*b_1_2',0,0,0,0))
            False

        The test engine keeps a statistic on the usage of the method. We see
        that the method was called twice with potential images of two generators,
        and see that in one case the Hilbert series of the ideals generated by
        the generators respectively their images do not match::

            sage: sorted(T.statistic.items(), key=repr)
            [('Hilbert series of ideals do not match', 1),
             (('potential isomorphism', 2), 2)]

        """
        new_im_gens = list(im_gens)
        self.set_images(new_im_gens)
        counter = self.statistic.get(('potential isomorphism',len(im_gens)-im_gens.count(0)),0) + 1
        self.statistic['potential isomorphism',len(im_gens)-im_gens.count(0)] = counter
        sys.stdout.flush()
        if all(im_gens):
            return self.is_isomorphism()

        # Do the Hilbert functions match? If they don't, it can't
        # become an isomorphism.
        HIm = self.hilbert_of_image
        HPrim = self.hilbert_of_preimage(tuple([i+1 for i,x in enumerate(new_im_gens) if x]))
        if HIm!=HPrim:
            self.statistic["Hilbert series of ideals do not match"] = self.statistic.get("Hilbert series of ideals do not match", 0) + 1
            return False

        if len(im_gens)-im_gens.count(0)>1:
            # For single generators, we would just test the nilpotency degree,
            # but this has already been considered.
            QD = self.partial_relations(tuple(bool(x) for x in new_im_gens))
            self._SC.set_ring()
            if self.singular.eval('size(NF(%s(%s),std(0)))'%(self._Smap.name(),QD.name()))!='0':
                self.statistic["Subalgebras do not match"] = self.statistic.get("Subalgebras do not match",0) + 1
                return False

        if self.use_annihilator:
            HIm = self.hilbert_of_image_annihilator
            HPrim = self.hilbert_of_preimage_annihilator(tuple([i+1 for i,x in enumerate(new_im_gens) if x]))
            if HIm!=HPrim:
                self.statistic["Hilbert series of annihilators do not match"] = self.statistic.get("Hilbert series of annihilators do not match", 0) + 1
                return False

        if self.use_radical:
            HIm = self.hilbert_of_image_radical
            HPrim = self.hilbert_of_preimage_radical(tuple([i+1 for i,x in enumerate(new_im_gens) if x]))
            if HIm!=HPrim:
                self.statistic["Hilbert series of radicals do not match"] = self.statistic.get("Hilbert series of radicals do not match", 0) + 1
                return False
        return True

    def is_isomorphism(self):
        """
        Test if the current assignment of generator images gives rise to an isomorphism.

        NOTE:

        The method uses elimination and may thus be costly. When :meth:`explore_isomorphisms`
        is called, it is tried to recognise non-isomorphisms without elimination.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.isomorphism_test import IsomorphismTest
            sage: CohomologyRing.doctest_setup()
            sage: H156 = CohomologyRing(64,156)
            sage: H156.make()
            sage: H158 = CohomologyRing(64,158)
            sage: H158.make()
            sage: T = IsomorphismTest(H156, H158)
            sage: T.set_images(('a_1_1*a_3_2+c_4_4', 'c_4_5+c_4_4', 'a_1_0', 'a_1_1', 'a_1_2', 'a_3_2', 'a_3_3'))
            sage: CohomologyRing.global_options('debug')
            sage: T.is_isomorphism()
            ...
            IsomorphismTest(H^*(SmallGroup(64,156); GF(2)), H^*(SmallGroup(64,158); GF(2))):
                      Verify if we found an isomorphism
                      ... need elimination...
            True
            sage: T.set_images(('c_4_4', 'c_4_5+c_4_4', 'a_1_0', 'a_1_1', 'a_1_2', 'a_3_2', 'a_3_3'))
            sage: T.is_isomorphism()
                      Verify if we found an isomorphism
                      ... Not a homomorphism
            False

        """
        self.statistic['isomorphism test'] = self.statistic.get('isomorphism test',0)+1
        if self._domain.poincare_series()!=self._codomain.poincare_series():
            coho_logger.info(">>> Hilbert series do not match", self)
            return False
        coho_logger.info("Verify if we found an isomorphism", self)
        if not self.is_homomorphism():
            coho_logger.info(">>> Not a homomorphism", self)
            self.statistic["not homomorphism"] = self.statistic.get("not homomorphism",0)+1
            return False
        self._R_elim.set_ring()
        GL = [repr(m) for m in self.urbild_GB.lead()]
        # Since the Hilbert series are equal,
        # we do not need to test both surjectivity
        # *and* injectivity---one of them is enough.
        ##
        # Contract: No generator name of the domain starts with
        # an '@'. Hence, if '@'+x.name() is in G for all generators
        # x of the codomain, we are gold.
        for x in self._codomain.Gen:
            if '@'+x.name() not in GL:
                coho_logger.info(">>> Homomorphism is not surjective", self)
                coho_logger.debug(">>> %s is not in the image", self, x.name())
                self.statistic["not surjective"] = self.statistic.get("not surjective",0) + 1
                return False
        return True

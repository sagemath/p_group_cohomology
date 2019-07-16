# -*- coding: utf-8 -*-

#*****************************************************************************
#
#    Cohomology Ring Elements, Yoneda Cochains, and Induced Maps
#
#    Copyright (C) 2009, 2015 Simon A. King <simon.king@uni-jena.de>
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

"""
Elements of Modular Cohomology Rings and their Induced Homomorphisms.

AUTHORS:

- Simon King <simon.king@uni-jena.de>

This module provides elements of modular cohomology rings of
groups of prime power order (:class:`COCH`), of finite groups
that are not of prime power order (:class:`MODCOCH`), induced
maps between cohomology rings (:class:`ChMap`), and Yoneda
cochains for prime power groups (:class:`YCOCH`). While Yoneda
cochains are just a tool for our implementation of Massey
products and Kraines' restricted Massey powers, the other
three classes are vital for cohomology computations.

The class :class:`COCH` provides elements of the mod-`p` cohomology of
a finite `p`-group `P`. It is based on a minimal free resolutions of
`F_pP` provided by the class :class:`~pGroupCohomology.resolution.RESL`.
The cup product is computed by standard constructions from homological
algebra.

In contrast, :class:`MODCOCH` provides elements of the mod-`p`
cohomology of any finite group `G`. The underlying data are stable
elements of the mod-`p` cohomology ring of a subgroup `U` of `G` whose
index is coprime to `p`. This ring is represented in the Singular
interface. For instance, `P` may be a Sylow `p`-subgroup of `G`. It is
allowed that `G=U` is a finite `p`-group, but in this case, the
cohomology ring of `G` must first be computed using :class:`COCH`.

Group homomorphisms induce maps in cohomology, and this is provided by
:class:`ChMap`. Induced homomorphisms are essential for the
computation of cohomology rings of finite groups that are not of prime
power order: The conditions defining stable elements are expressed in
terms of pairs of induced maps.

:class:`COCH`, :class:`MODCOCH` and :class:`ChMap` can quite easily be
combined, which can be seen in the following examples.

EXAMPLES:

We define two groups (one of them is of prime power order) and
compute their cohomology rings.
::

    sage: from pGroupCohomology import CohomologyRing
    sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
    sage: S = libgap.SymmetricGroup(6)
    sage: D = libgap.DihedralGroup(8)
    sage: HS = CohomologyRing(S, prime=2, GroupName='Sym6', from_scratch=True)
    sage: HS.make()
    sage: HD = CohomologyRing(D, GroupName='D_8', from_scratch=True)
    sage: HD.make()

We do some computations with cohomology elements, testing relations in
``HS`` and ``HD``::

    sage: cD1 = HD.1+HD.2*HD.3; cD1
    c_2_2+(b_1_0)*(b_1_1): 2-Cocycle in H^*(D_8; GF(2))
    sage: cD2 = HD.1+HD.3^2; cD2
    c_2_2+(b_1_1)**2: 2-Cocycle in H^*(D_8; GF(2))
    sage: cD1 == cD2
    True
    sage: HD.rels()
    ['b_1_1^2+b_1_0*b_1_1']

::

    sage: cS1 = HS.1*HS.2+HS.3; cS1
    (c_2_1)*(c_1_0)+(b_3_2): 3-Cocycle in H^*(Sym6; GF(2))
    sage: cS2 = HS.1*HS.2+HS.4; cS2
    (c_2_1)*(c_1_0)+(b_3_3): 3-Cocycle in H^*(Sym6; GF(2))
    sage: cS1*cS2 == HS.3*HS.4 + HS.1*HS.2*(HS.1*HS.2+HS.3+HS.4)
    True
    sage: HS.rels()
    ['b_3_2*b_3_3']

We define an embedding of ``D`` in ``S`` and compute the induced
map from ``HS`` to ``HD``::

    sage: emb = D.GroupHomomorphismByImages(S,D.GeneratorsOfGroup(),libgap.eval('[ (2,4), (1,2,3,4), (1,3)(2,4) ]'))
    sage: resS_D = HS.hom(emb,HD)
    sage: [resS_D(g).as_polynomial() for g in HS.gens()[1:]]
    ['b_1_0*b_1_1+b_1_0^2+c_2_2',
     'b_1_1+b_1_0',
     'c_2_2*b_1_1+c_2_2*b_1_0',
     'b_1_0^2*b_1_1+c_2_2*b_1_1']

Note that the generators of ``HD`` are :class:`COCH`, while those of
``HS`` are :class:`MODCOCH`. But the image of the induced map is
formed by :class:`MODCOCH`::

    sage: type(HD.1)
    <type 'pGroupCohomology.cochain.COCH'>
    sage: type(HS.1)
    <class 'pGroupCohomology.cochain.MODCOCH'>
    sage: type(resS_D(HS.1))
    <class 'pGroupCohomology.cochain.MODCOCH'>

It is possible to mix both classes in arithmetic expressions::

    sage: resS_D(HS.2) == HD.2+HD.3
    True
    sage: resS_D(HS.1)*resS_D(HS.2) == resS_D(HS.1)*HD.2+resS_D(HS.1)*HD.3
    True

"""

from __future__ import print_function, absolute_import
import sys
import os

## Sage generalities
import sage
import sage.all
from sage.all import cputime
from sage.all import walltime
from sage.all import copy
from sage.all import deepcopy
from sage.all import load
from sage.all import tmp_filename
from sage.all import Infinity
from sage.misc.cachefunc import cached_method

## Sage Rings etc.
from sage.all import Integer
from sage.all import FiniteField as GF
from sage.all import Matrix
from sage.all import MatrixSpace
from sage.structure.element cimport RingElement
from sage.rings.homset import RingHomset_generic

from sage.matrix.matrix_gfpn_dense cimport new_mtx

# auxiliary class from pGroupCohomology (the Cython classes are imported in cochain.pxd
from pGroupCohomology.auxiliaries import coho_options, coho_logger, safe_save, _gap_reset_random_seed

from libc.string cimport memcpy
from cysignals.signals cimport sig_check, sig_on, sig_off

#####################################################################
#####################################################################
## Cochain extension type
#####################################################################
#####################################################################

class COCH_unpickle_class:
    r"""
    Unpickling a cochain.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(8,3, from_scratch=True)
        sage: H.make()
        sage: C=H.2
        sage: type(C)
        <type 'pGroupCohomology.cochain.COCH'>
        sage: D=loads(dumps(C))   #indirect doctest
        sage: print(C)
        1-Cocycle in H^*(D8; GF(2)),
        represented by
        [1 0]
        rdeg = 0
        ydeg = 0
        sage: print(D)
        1-Cocycle in H^*(D8; GF(2)),
        represented by
        [1 0]
        rdeg = 0
        ydeg = 0

    ``C`` and ``D`` are different objects, but of course their parents
    are the same, and the cochains are equal::

        sage: D is C
        False
        sage: D.parent() is C.parent()
        True
        sage: D == C
        True

    """
    def __init__(self):
        """
        TESTS::

            sage: from pGroupCohomology.cochain import COCH_unpickle_class
            sage: CU = COCH_unpickle_class()
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,2, from_scratch=True)
            sage: C = CU(H,2,'foo',[0,1,1],0,1)      # indirect doctest
            sage: C
            foo: 2-Cocycle in H^*(SmallGroup(8,2); GF(2))
            sage: print(C)
            2-Cocycle in H^*(SmallGroup(8,2); GF(2)),
            represented by
            [0 1 1]
            rdeg = 1
            ydeg = 0

        """
        self.__safe_for_unpickling__ = True

    def __call__(self, H, n, Nick, L, ydeg, rdeg, polyrep=False):
        """
        TESTS::

            sage: from pGroupCohomology.cochain import COCH_unpickle_class
            sage: CU = COCH_unpickle_class()
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: C = CU(H,2,'foo',[0,1,1],0,1)   # indirect doctest
            sage: C
            foo: 2-Cocycle in H^*(D8; GF(2))
            sage: print(C)
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 1 1]
            rdeg = 1
            ydeg = 0
        """
        return COCH(H, n, Nick, L, ydeg, rdeg, polyrep)

coch_unpickle=COCH_unpickle_class()

################################################################
## Elements of modular cohomology rings of finite groups
################################################################

cdef class COCH(RingElement):
    r"""
    COCH extension class representing elements of cohomology rings.

    INPUT:

    - ``H`` -- a cohomology ring (:class:`~pGroupCohomology.cohomology.COHO`)
    - ``n`` -- the degree of the cochain (integer)
    - ``s`` -- name of the `n`-cochain (string)
    - ``M`` -- data describing the cochain. Either
       1. a `(1 \times d)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix, or
       2. a `d`-tuple of integers

      where `d` is the projective rank of the `n`-th term of the resolution
      that underlies ``H``
    - ``ydeg`` (optional, default ``None``) -- y-degree of the cochain
    - ``rdeg`` (optional, default ``None``) -- r-degree of the cochain

    OUTPUT:

    A degree `n` element of ``H`` of name s.

    NOTE:

    - Usually, a cochain will be created by doing algebra with the generators
      of a cohomology ring.
    - In our application (see :mod:`pGroupCohomology`), ``rdeg==1`` if and only if
      the cochain is a Duflot regular generator of a cohomology
      ring; ``ydeg==1`` if and only if the cochain is a generator
      of a cohomology ring that is neither nilpotent nor Duflot
      regular.
    - Every cochain is provided with a name. When a cochain is the result of a
      computation then its name will by default describe its construction.
      We think that this is a very useful feature.


    EXAMPLES:

    First, we show how one would usually create a cochain::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: C = H.2
        sage: D = H.3
        sage: C
        b_1_0: 1-Cocycle in H^*(D8; GF(2))
        sage: D
        b_1_1: 1-Cocycle in H^*(D8; GF(2))
        sage: C+D
        b_1_0+b_1_1: 1-Cocycle in H^*(D8; GF(2))
        sage: C*D
        (b_1_0)*(b_1_1): 2-Cocycle in H^*(D8; GF(2))
        sage: print(C^3)
        3-Cocycle in H^*(D8; GF(2)),
        represented by
        [1 0 0 0]
        sage: print(D^3)
        3-Cocycle in H^*(D8; GF(2)),
        represented by
        [0 1 0 0]

    Next, we show a non-commutative example. Just for documentation,
    we create the cochains more directly::

        sage: H = CohomologyRing(27,3, from_scratch=True)
        sage: print(H.resolution())
        Resolution:
        0 <- GF(3) <- GF(3)[E27]

    Incidentally, we know that the projective rank of the second term
    of the resolution is four. So, we can define::

        sage: from pGroupCohomology.cochain import COCH
        sage: C = COCH(H,2,'first',(1,0,1,2))

    Now, the resolution is computed out to the second term, and the
    cochain ``C`` has the name 'first'::

        sage: print(H.resolution())
        Resolution:
        0 <- GF(3) <- GF(3)[E27] <- rank 2 <- rank 4
        sage: C
        first: 2-Cocycle  in H^*(E27; GF(3))
        sage: print(C)
        2-Cocycle in  H^*(E27; GF(3)),
        represented by
        [1 0 1 2]

    Using :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrices, we provide
    a slightly different way to create a cochain. The matrix must
    be immutable::

        sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
        sage: D = COCH(H,2,'second', MTX(MatrixSpace(GF(3),1,4, implementation=MTX), [[0,1,0,1]], mutable=False))

    Now, we can add or subtract the cochains::

        sage: C+D
        first+second: 2-Cocycle in H^*(E27; GF(3))
        sage: print(C+D)
        2-Cocycle in H^*(E27; GF(3)),
        represented by
        [1 1 1 0]
        sage: print(C-D)
        2-Cocycle in H^*(E27; GF(3)),
        represented by
        [1 2 1 1]

    Scalar multiplication works as well::

        sage: 2*C
        2*(first): 2-Cocycle in H^*(E27; GF(3))
        sage: print(C*2)
        2-Cocycle in H^*(E27; GF(3)),
        represented by
        [2 0 2 1]

    But certainly, in cohomology computations the cup-product
    is the most interesting::

        sage: C*D
        (first)*(second): 4-Cocycle in H^*(E27; GF(3))
        sage: print(H.resolution())
        Resolution:
        0 <- GF(3) <- GF(3)[E27] <- rank 2 <- rank 4 <- rank 6 <- rank 7
        sage: E = C^2
        sage: E = C^2+D*C*2
        sage: E
        (first)**2+((second)*(first))*2: 4-Cocycle in H^*(E27; GF(3))
        sage: print(E)
        4-Cocycle in H^*(E27; GF(3)),
        represented by
        [2 2 0 1 0 0 2]

    Since `p>2` in this example, the cohomology ring is non-commutative::

        sage: X = COCH(H,3,'X',(1,1,1,0,0,0))
        sage: Y = COCH(H,3,'Y',(0,0,0,1,1,1))
        sage: print(X*Y)
        6-Cocycle in H^*(E27; GF(3)),
        represented by
        [2 1 1 0 0 0 0 0 0]
        sage: print(Y*X)
        6-Cocycle in H^*(E27; GF(3)),
        represented by
        [1 2 2 0 0 0 0 0 0]

    The name (which by default describes the construction of the cochain)
    can be overwritten::

        sage: E.name()
        '(first)**2+((second)*(first))*2'
        sage: E.setname('foo')
        sage: E
        foo: 4-Cocycle in H^*(E27; GF(3))

    """
#################
# init, dealloc(automatic in this case), repr
    def __init__(self, PARENT, int n, char *Nick, L, ydeg=None, rdeg=None, is_polyrep=False):
        """
        INPUT:

        - ``PARENT`` -- a cohomology ring (:class:`~pGroupCohomology.cohomology.COHO`)
        - ``n`` -- integer, the degree of this cohomology ring element
        - ``Nick`` -- string, the name used to display this element
        - ``L`` -- list of ``r`` marks (integers), where ``r`` is the
          projective rank of the resolution of ``PARENT``.
        - ``ydeg`` -- optional integer, should be 1 for nilpotent elements.
        - ``rdeg`` -- optional integer, should be 1 if the restriction to
          the greatest central elementary abelian subgroup does not vanish.
        - ``is_polyrep`` -- optional boolean; if ``True``, it is assumed
          that the given name defines a representation of this element
          as a polynomial in the generators of ``PARENT``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: from pGroupCohomology.cochain import COCH
            sage: H = CohomologyRing(8,3)
            sage: H.make()

        We create an element of ``H``, and, for test purposes, make the
        system believe that its name is a polynomial.

            sage: C = COCH(H, 5, "foo", [0,1,0,1,0,1], is_polyrep=True)  # indirect doctest
            sage: C
            foo: 5-Cocycle in H^*(D8; GF(2))

        Since we incorrectly asserted that the name provides a polynomial
        representation, we get the following result::

            sage: C.as_polynomial()
            'foo'

        However, when we overwrite the name and do not indicate that
        it is a polynomial, the result now makes more sense::

            sage: C.setname('bar')
            sage: C
            bar: 5-Cocycle in H^*(D8; GF(2))
            sage: C.as_polynomial()
            'b_1_1^5+c_2_2*b_1_1^3+c_2_2^2*b_1_1'

        """
        from pGroupCohomology.cohomology import COHO
        if not isinstance(PARENT, COHO):
            raise TypeError("The parent of a cochain must be a cohomology ring (type %s)"%repr(COHO))
        cdef RESL R = PARENT.Resl
        self._sing_val = None
        if (n<0):
            raise IndexError("Degree out of range")
        while n>R.deg():
            R.nextDiff()
        cdef MTX LMTX
        if isinstance(L, tuple):
            L = list(L)
        if isinstance(L,list):
            if (len(L)!=R.Data.projrank[n]):
                raise IndexError("Last parameter must be of length %d"%(R.Data.projrank[n]))
            self.Resl = R
            self.Deg = n
            self.Name = str(Nick)
            self.Data = new_mtx(rawMatrix(R.G_Alg.Data.p, [L]), None)
            self.Data.set_immutable()
        elif isinstance(L,MTX):
            LMTX = L
            if (LMTX.Data.Field != R.G_Alg.Data.p):
                raise TypeError("MTX matrix must be defined over GF(%d)"%(R.G_Alg.Data.p))
            LMTX.set_immutable()
            if (LMTX._nrows != 1) or (LMTX._ncols != R.Data.projrank[n]):
                raise TypeError("(1 x %d) MTX matrix expected"%(R.Data.projrank[n]))
            self.Resl = R
            self.Deg = n
            self.Name = Nick
            self.Data = LMTX
        else:
            raise TypeError("Last parameter must be a list/tuple of integers or an MTX matrix")
        self.Ydeg = ydeg
        self.Rdeg = rdeg
        RingElement.__init__(self,PARENT)
        self._latex = None
        self._polyrep = is_polyrep

    def __copy__(self):
        """
        Return a copy of self, defined over *the same* resolution.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: C = H.2+H.3
            sage: C == copy(C)      # indirect doctest
            True
            sage: C is copy(C)
            False

        """
        return COCH(self._parent, self.Deg, self.Name, copy(self.Data), self.ydeg, self.rdeg, self._polyrep)

    def __reduce__(self):
        """
        Return data used for pickling/unpickling ``self``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: C = H.2+H.3
            sage: C == loads(dumps(C))     # indirect doctest
            True
            sage: C is loads(dumps(C))
            False

        """
        return coch_unpickle, (self._parent, self.Deg, self.Name, self.Data, self.Ydeg, self.Rdeg, self._polyrep)

    def _repr_(self):
        """
        Return a brief description of the cochain.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: C = H.2+H.3
            sage: C         # indirect doctest
            b_1_0+b_1_1: 1-Cocycle in H^*(D8; GF(2))

        """
        return self.name()+': %d-Cocycle in %s'%(self.Deg,self.parent().__repr__())

    def __str__(self):
        """
        Return a more detailed description of the cochain.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: C = H.2+H.3
            sage: print(C) # indirect doctest
            1-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1]

        """
        s = ("%d-Cocycle in %s"%(self.Deg,self.parent().__repr__()))+',\nrepresented by\n'+self.Data.__str__()
        if (self.rdeg()!=None):
            s=s+'\nrdeg = %d'%(self.rdeg())
        if (self.ydeg()!=None):
            s=s+'\nydeg = %d'%(self.ydeg())
        return s

    def _singular_(self, S):
        """
        Represent self as an element of the Singular interface version of the parent cohomology ring.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: singular(H.1)   # indirect doctest
            c_2_2
            sage: singular(H.2*H.1)
            c_2_2*b_1_0

        """
        if (self._sing_val is not None) and (self._sing_val.parent() is S):
            try:
                self._sing_val._check_valid()
                return self._sing_val
            except ValueError:
                pass
        self.parent()._singular_(S).set_ring()
        self._sing_val = S(self.as_polynomial())
        return self._sing_val

    def _MODCOCH_(self,S=None):
        """
        Transform self into an instance of MODCOCH, using a specific singular instance.

        INPUT:

        ``S`` (optional): A specific Singular instance

        OUTPUT:

        A :class:`MODCOCH` instance equal to self.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(32,4)
            sage: H.make()
            sage: c = H.1+H.3*H.4; c
            c_2_1+(a_1_0)*(a_1_1): 2-Cocycle in H^*(SmallGroup(32,4); GF(2))
            sage: type(c)
            <type 'pGroupCohomology.cochain.COCH'>
            sage: C = c._MODCOCH_()
            sage: type(C)
            <class 'pGroupCohomology.cochain.MODCOCH'>
            sage: c == C
            True
            sage: c*H.2 == C*H.2
            True

        """
        if S is None:
            from pGroupCohomology.auxiliaries import singular
            S = singular
        try:
            br = S('basering')
        except:
            br = None
        S(self.parent()).set_ring()
        s = S(self)
        # parent, value, deg=None, name=None, S=None, rdeg=None, ydeg=None, is_polyrep=False, is_NF=None
        out = MODCOCH(self.parent(), s, deg=self.deg(), name=repr(s), S=S, rdeg=self.rdeg(), ydeg=self.ydeg(), is_polyrep=True)
        if br is not None:
            br.set_ring()
        return out

    def set_latex_name(COCH self, s):
        r"""
        Declare how self should be typeset in \LaTeX.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: latex(H.2)
            b_{1,0}
            sage: (H.2).set_latex_name('H_2')
            sage: latex(H.2)
            H_2

        """
        if not isinstance(s, basestring):
            raise TypeError("String expected")
        self._latex = s

    def _latex_(COCH self):
        """
        Return a latex typeset.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: latex(H.2*H.1+H.2*H.3^2) # indirect doctest
            (b_{1,0}) (c_{2,2})+(b_{1,0}) ((b_{1,1})^{2})

        """
        if self._latex is not None:
            return self._latex
        from pGroupCohomology.factory import _name2latex
        self._latex = _name2latex(self.name())
        return self._latex


################
# structural parts
    def resolution(self):
        """
        Return the underlying resolution.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: from pGroupCohomology.cochain import COCH
            sage: C=COCH(H,2,'foo',(1,1,0))

        Note that the needed terms of the resolution are automatically
        computed::

            sage: print(C.resolution())
            Resolution:
            0 <- GF(2) <- GF(2)[D8] <- rank 2 <- rank 3
            sage: C.resolution() is H.resolution()
            True

        """
        return self.Resl

    def deg(self):
        """
        Return the degree of ``self``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: C=H.2*H.1
            sage: C.deg()
            3

        """
        return self.Deg

    cpdef MTX MTX(self):
        """
        Return the :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix by which ``self`` is defined.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: C = H.2*H.1
            sage: print(C.MTX())
            [0 0 1 0]

        """
        return self.Data

    def yoneda_cocycle(COCH self):
        """
        Express ``self`` as a Yoneda cocycle.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: Y21 = H.2.yoneda_cocycle()*H.1.yoneda_cocycle()
            sage: X21 = (H.2*H.1).yoneda_cocycle()
            sage: Y21[0] == X21[0]
            True
            sage: Y21[1] == X21[1]
            True
            sage: Y21[2] == X21[2]
            True

        """
        # If YCOCH only gets the first term and does not get an explicit construction
        # description, then the result is a cocycle.
        return YCOCH(self.Resl, self.Deg, self.Resl.CochainToChainmap(self.Deg,self.Data)[2])

    def name(self):
        """
        Return the name of ``self``.

        NOTE:

        When a :class:`~pGroupCohomology.cochain.COCH` instance is created by invoking
        the init method, a name must be given. When further :class:`~pGroupCohomology.cochain.COCH`
        instances are created by arithmetic operations, the name of the result describes its
        construction.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: C=H.2*H.1
            sage: print(C.name())
            (b_1_0)*(c_2_2)
            sage: H(C.name()) == C
            True

        Note that there is no automatic simplification when the result
        represents the trivial cochain::

            sage: (C*2).name()
            '((b_1_0)*(c_2_2))*0'
            sage: print(C*2)
            3-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 0 0 0]

        """
        return self.Name

    label = name

    def setname(self, s, is_polyrep=False):
        """
        Set the name of ``self``.

        INPUT:

        s -- a string providing the new name

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: C=H.2*H.1
            sage: C
            (b_1_0)*(c_2_2): 3-Cocycle in H^*(D8; GF(2))
            sage: C.setname('foo')
            sage: C
            foo: 3-Cocycle in H^*(D8; GF(2))

        """
        if not isinstance(s, basestring):
            raise TypeError("String expected")
        self.Name = s
        self._latex = None
        self._polyrep = is_polyrep

    def as_polynomial(self):
        """
        Return a string that represents ``self`` as a polynomial in its parent.

        NOTE:

        The name of ``self`` will be modified inplace

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: c = H.1*H.2+H.3^3
            sage: c
            (c_2_2)*(b_1_0)+(b_1_1)**3: 3-Cocycle in H^*(D8; GF(2))
            sage: c.setname('foo')
            sage: c
            foo: 3-Cocycle in H^*(D8; GF(2))
            sage: c.as_polynomial()
            'b_1_1^3+c_2_2*b_1_0'
            sage: c
            b_1_1^3+c_2_2*b_1_0: 3-Cocycle in H^*(D8; GF(2))

        """
        if not self._polyrep:
            self.parent().element_as_polynomial(self)
        return self.name()

    def rdeg(self):
        """
        Return the `r`-degree of ``self``.

        NOTE:

        The r-degree plays an important role in the computation
        of cohomology rings. A generator of a cohomology ring
        has ``rdeg==1`` if and only if it is a Duflot regular
        generator, which means that its restriction to the
        greatest central elementary abelian subgroup is not
        nilpotent.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.1.rdeg()
            1
            sage: H.2.rdeg()
            0
            sage: H.3.rdeg()
            0

        """
        return self.Rdeg

    def ydeg(self):
        """
        Return the `y`-degree of ``self``.

        NOTE:

        The y-degree plays an important role in the computation
        of cohomology rings. A generator of a cohomology ring
        has ``ydeg==1`` if and only if it is nilpotent.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,3)
            sage: H.make()
            sage: print(H)
            Cohomology ring of Small Group number 3 of order 16 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [b_2_1: 2-Cocycle in H^*(SmallGroup(16,3); GF(2)),
             c_2_2: 2-Cocycle in H^*(SmallGroup(16,3); GF(2)),
             c_2_3: 2-Cocycle in H^*(SmallGroup(16,3); GF(2)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(16,3); GF(2)),
             b_1_1: 1-Cocycle in H^*(SmallGroup(16,3); GF(2))]
            Minimal list of algebraic relations:
            [a_1_0^2,
             a_1_0*b_1_1,
             b_2_1*a_1_0,
             b_2_1^2+c_2_2*b_1_1^2]
            sage: H.1.rdeg(),H.1.ydeg()
            (0, 0)
            sage: H.2.rdeg(),H.2.ydeg()
            (1, 0)
            sage: H.4.rdeg(),H.4.ydeg()
            (0, 1)

        """
        return self.Ydeg

    def is_nilpotent(self):
        """
        Tells whether this cocycle is nilpotent.

        An elemenet of a mod-`p` cohomology ring of a finite group is
        nilpotent if and only if the restrictions to all maximal
        `p`-elementary abelian subgroups are.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace

        An example in even characteristic::

            sage: H = CohomologyRing(64,242)
            sage: H.make()
            sage: H.nil_radical()
            b_1_0*b_1_2+b_1_0^2,
            b_1_0*b_1_3+b_1_0*b_1_1+b_1_0^2
            sage: H('b_1_0*b_1_2+b_1_0^2').is_nilpotent()
            True
            sage: H('b_1_0*b_1_3+b_1_0*b_1_2').is_nilpotent()
            False
            sage: H('b_1_0*b_1_3+b_1_0*b_1_1+b_1_0^2').is_nilpotent()
            True

        An example in odd characteristic::

            sage: H = CohomologyRing(81,13)
            sage: H.make()
            sage: H.nil_radical()
            a_1_0,
            a_1_1,
            a_1_2,
            a_3_6,
            a_5_10
            sage: c = H('a_1_2*a_5_10')
            sage: bool(c)
            True
            sage: c.is_nilpotent()
            True
            sage: c.nilpotency_degree()
            2

        Two abelian examples, that gave a wrong answer with previous versions
        of the spkg::

            sage: H = CohomologyRing(3^4,gap.NumberSmallGroups(3^4))
            sage: H.make()
            sage: (H.5*H.6+H.7*H.8).is_nilpotent()
            True
            sage: (H.5*H.6+H.7*H.8).nilpotency_degree()
            3
            sage: H = CohomologyRing(16,2)
            sage: H.make()
            sage: H.3.is_nilpotent()
            True
            sage: H.3.nilpotency_degree()
            2

        """
        H = self.parent()
        ch = H.base_ring().characteristic()
        singular = H.GenS.parent()
        if not self:
            return True
        if ch!=2 and self.deg()%2:
            return True
        if not H.MaxelPos:
            s = singular(self)
            singular(H).set_ring()
            return singular.eval('NF({}, {})'.format(s.name(), H.nil_radical().name()))=='0'
        for p in H.MaxelPos:
            phi = H.RestrMaps[p][1]
            self_res = phi(self)
            if ch==2:
                if self_res:
                    return False
            else:
                if singular(self_res).NF(self_res.parent().nil_radical()):
                    return False
        return True

    def nilpotency_degree(self):
        """
        The smallest exponent by which this cocycle becomes zero.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,18)
            sage: H.make()
            sage: H.nil_radical()
            a_1_0,
            a_1_1,
            a_2_0,
            a_2_1,
            a_5_5,
            a_5_8,
            a_6_7,
            a_6_10
            sage: c = H('a_5_5')
            sage: c.nilpotency_degree()
            4

        The following takes quite long, as it is needed to compute the
        resolution of this cohomology ring out to degree 20. However, it
        confirms the stated nilpotency degree::

            sage: bool(c^2), bool(c^3), bool(c^4)
            (True, True, False)

        If the cocycle is not nilpotent, infinity is returned::

            sage: c = H('b_2_3')
            sage: c.is_nilpotent()
            False
            sage: c.nilpotency_degree()
            +Infinity

        Of course, a zero cochain has nilpotency degree one::

            sage: (c*0).nilpotency_degree()
            1

        """
        if not self:
            return 1
        if not self.is_nilpotent():
            return Infinity
        singular = self.parent().GenS.parent()
        s = singular(self)
        singular(self.parent()).set_ring()
        d = 1
        while True:
            d += 1
            if singular.eval('NF(%s**%d, std(0))'%(s.name(),d))=='0':
                return d


################
# !=,==, dictionary etc.
    cpdef _richcmp_(self, C, int x):
        """
        Compare cochains.

        NOTE:

        By Sage's coercion model, both arguments are elements of the same
        parent. But it is possible that they are of different type.
        If both are of type :class:`~pGroupCohomology.cochain.COCH`,
        the degree and the underlying matrices are compared. If the second
        argument is of type :class:`~pGroupCohomology.cochain.MODCOCH`,
        the elements are compared in Singular.

        TESTS:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.1.deg()
            2
            sage: H.2.deg()
            1
            sage: H.1>H.2         # indirect doctest
            True
            sage: print(H.2*H.3)
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 0 0]
            sage: H.2*H.3 == H.1*0
            True
            sage: print(H.2*H.2)
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 0 0]
            sage: print(H.3*H.3)
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 1 0]
            sage: H.2*H.2 > H.3*H.3
            True
            sage: H.2*H.2 < H.3*H.3
            False

        """
        assert isinstance(C,COCH) or isinstance(C,MODCOCH)
        cdef COCH C2
        # < 0, <= 1, == 2, != 3, > 4, >= 5
        if (x==0):
            if isinstance(C,COCH):
                C2 = C
                return (self.Deg < C2.Deg) or ((self.Deg == C2.Deg) and (self.Data < C2.Data))
            return self._MODCOCH_() < C
        if (x==1):
            if isinstance(C,COCH):
                C2 = C
                return (self.Deg < C2.Deg) or ((self.Deg == C2.Deg) and (self.Data <= C2.Data))
            return self._MODCOCH_() <= C
        if (x==2):
            if isinstance(C,COCH):
                C2 = C
                return (self.Deg == C2.Deg) and (self.Data == C2.Data)
            return self._MODCOCH_() == C
        if (x==3):
            if isinstance(C,COCH):
                C2 = C
                return (self.Deg != C2.Deg) or (self.Data != C2.Data)
            return self._MODCOCH_() != C
        if (x==4):
            if isinstance(C,COCH):
                C2 = C
                return (self.Deg > C2.Deg) or ((self.Deg == C2.Deg) and (self.Data > C2.Data))
            return self._MODCOCH_() > C
        if (x==5):
            if isinstance(C,COCH):
                C2 = C
                return (self.Deg > C2.Deg) or ((self.Deg == C2.Deg) and (self.Data >= C2.Data))
            return self._MODCOCH_() >= C
        return NotImplemented

    def __hash__(COCH self):
        r"""
        Return a hash value of ``self``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: C = H.2
            sage: hash(C) == hash(copy(C))   # indirect doctest
            True
            sage: hash(C) == hash(loads(dumps(C)))
            True
            sage: D = {C:1, C^2:2}
            sage: D[copy(C)]
            1
            sage: D[copy(C)*C]
            2

        """
        return (self.Deg, self.Data).__hash__()


################
# Arithmetic
    def __nonzero__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(32,4)
            sage: H.make()
            sage: H.1.is_zero() #indirect doctest
            False
            sage: (2*H.1).is_zero() #indirect doctest
            True

        """
        cdef FEL f
        FfSetField((<COCH>self).Data.Data.Field)
        FfSetNoc((<COCH>self).Data.Data.Noc)
        return FfFindPivot((<COCH>self).Data.Data.Data, &f)!=-1

    cpdef _add_(self, other):
        r"""
        Sum of cochains of the same degree.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.1+H.2
            Traceback (most recent call last):
            ...
            IndexError: cochains must be of the same degree
            sage: H.2+H.3        # indirect doctest
            b_1_0+b_1_1: 1-Cocycle in H^*(D8; GF(2))
            sage: print(H.3+H.2)
            1-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1]

        It is possible to mixedly add :class:`COCH` and :class:`MODCOCH`::

            sage: X = CohomologyRing(720,763,prime=2)
            sage: X.make()
            sage: type(X.sylow_cohomology()('c_2_5*b_1_0'))
            <type 'pGroupCohomology.cochain.COCH'>
            sage: type(X.3.as_cocycle_in_sylow())
            <class 'pGroupCohomology.cochain.MODCOCH'>
            sage: print(X.sylow_cohomology()('c_2_5*b_1_0')+X.3.as_cocycle_in_sylow())
            c_2_5*b_1_0+(c_2_5*b_1_0): 3-Cocycle in H^*(D8xC2; GF(2))
            defined by
            0
            sage: type(X.sylow_cohomology()('c_2_5*b_1_0')+X.3.as_cocycle_in_sylow())
            <class 'pGroupCohomology.cochain.MODCOCH'>

        """
        if isinstance(other,MODCOCH):
            return self._MODCOCH_(other._Svalue.parent())+other
        cdef COCH C
        try:
            C = other
        except:
            C = self.parent()(other)
        if (self.Resl is C.Resl):
            if self.Deg!=C.Deg:
                raise IndexError("cochains must be of the same degree")
            else:
                return COCH(self._parent, self.Deg, self.Name+'+'+C.Name, self.Data+C.Data, is_polyrep=self._polyrep and C._polyrep)
        else:
            raise ValueError("Cochains must be defined over a common resolution")

    cpdef _sub_(self, other):
        """
        Difference of two cochains of the same degree.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.1-H.2   # indirect doctest
            Traceback (most recent call last):
            ...
            IndexError: cochains must be of the same degree
            sage: H.2-H.3   # indirect doctest
            b_1_0-(b_1_1): 1-Cocycle in H^*(D8; GF(2))
            sage: print(H.3+H.2)
            1-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1]

        """
        if isinstance(other,MODCOCH):
            return self._MODCOCH_(other._Svalue.parent())-other
        cdef COCH C
        try:
            C = other
        except:
            C = self.parent()(other)
        if (self.Resl is C.Resl):
            if self.Deg!=C.Deg:
                raise IndexError("cochains must be of the same degree")
            else:
                return COCH(self._parent, self.Deg, self.Name+'-('+C.Name+')', self.Data-C.Data, is_polyrep=self._polyrep and C._polyrep)
        else:
            raise ValueError("Cochains must be defined over a common resolution")
    cpdef ModuleElement _neg_(self):
        r"""
        Additive inverse of a cochain.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: - H.1    # indirect doctest
            (-(b_2_0)): 2-Cocycle in H^*(E27; GF(3))
            sage: print(H.1)
            2-Cocycle in H^*(E27; GF(3)),
            represented by
            [1 0 0 0]
            rdeg = 0
            ydeg = 0
            sage: print(-H.1)
            2-Cocycle in H^*(E27; GF(3)),
            represented by
            [2 0 0 0]

        """
        return COCH(self._parent, self.Deg, '(-('+self.Name+'))', -self.Data, is_polyrep=self._polyrep)

    cdef inline void set_mtx_globals(self):
        "Define MeatAxe's global variables compatible with self's data"
        FfSetField(self.Data.Data.Field)
        FfSetNoc(self.Data.Data.Noc)

    cdef void isubmul(self, COCH other, FEL c):
        """
        self -> self - other*c

        ASSUMPTIONS:

        It is assumed that self and other have the same rank, and that
        MeatAxe's FfField and FfCurrentRowSize are compatible with the
        data of the cochains.
        """
        if c == FF_ZERO:
            return
        elif c != FF_ONE:
            FfAddMulRow(self.Data.Data.Data, other.Data.Data.Data, <FEL>mtx_taddinv[<int><unsigned char>c])
            self.Name = self.Name + '-({})*('.format(<int><unsigned char>c) + other.Name +')'
            self._polyrep = self._polyrep and other._polyrep
        else:
            FfSubRow(self.Data.Data.Data, other.Data.Data.Data)
            self.Name = self.Name + '-('+ other.Name +')'
            self._polyrep = self._polyrep and other._polyrep

    cpdef _lmul_(self, Element right):
        """
        Scalar multiplication from the right side.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: H.1*2   # indirect doctest
            (b_2_0)*2: 2-Cocycle in H^*(E27; GF(3))

        """
        Right = int(right)
        if Right==1:
            return self
        else:
            return COCH(self._parent, self.Deg, '('+self.Name+')*'+str(Right%self.Data.Data.Field), self.Data._mul_long(Right), is_polyrep=self._polyrep)

    cpdef _rmul_(self, Element left):
        """
        Scalar multiplication from the left side.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: 2*H.1   # indirect doctest
            2*(b_2_0): 2-Cocycle in H^*(E27; GF(3))

        """
        Right = int(left)
        if Right==1:
            return self
        else:
            return COCH(self._parent, self.Deg, str(Right%self.Data.Data.Field) + '*('+self.Name+')', self.Data._mul_long(Right), is_polyrep=self._polyrep)

    cdef _mul_long(self, long n):
        """
        Multiplication with a Python int or long.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: H.1*int(0)      # indirect doctest
            0: 2-Cocycle in H^*(E27; GF(3))
            sage: H.1*int(1)
            b_2_0: 2-Cocycle in H^*(E27; GF(3))
            sage: H.1*int(-1)
            -(b_2_0): 2-Cocycle in H^*(E27; GF(3))
            sage: H.1*int(2)
            (b_2_0)*2: 2-Cocycle in H^*(E27; GF(3))

        """
        if n==1:
            return self
        if n==0:
            return COCH(self._parent, self.Deg,
                    '0',
                    self.Data._mul_long(0), is_polyrep=True)
        if n==-1:
            return COCH(self._parent, self.Deg,
                    '-('+self.Name+')',
                    self.Data._mul_long(n), is_polyrep=self._polyrep)
        return COCH(self._parent, self.Deg,
                    '('+self.Name+')*'+str(n%self.Data.Data.Field),
                    self.Data._mul_long(n), is_polyrep=self._polyrep)

    cpdef _mul_(self, right):
        """
        Cup product of two cochains, or scalar multiplication.

        NOTE:

        Some data needed for the construction of the cup product are
        cached. This yields to a massive improvement of performance
        in cohomology computations.

        NOTE:

        Let ``D1,D2`` be two cochains in a cohomology ring, of
        degrees ``d1,d2``. In general, the computation of ``D1*D2``
        is faster than the computation of ``D2*D1``, if ``d1<d2``.
        Hence, for computing ``D2*D1``, we recommend to compute
        ``D1*D2`` first.

        The cup product is graded commutative. Hence,
        ``D2*D1 = D1*D2*(-1)^(d1*d2)``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: H.gens()
            [1,
             b_2_0: 2-Cocycle in H^*(E27; GF(3)),
             b_2_1: 2-Cocycle in H^*(E27; GF(3)),
             b_2_2: 2-Cocycle in H^*(E27; GF(3)),
             b_2_3: 2-Cocycle in H^*(E27; GF(3)),
             c_6_8: 6-Cocycle in H^*(E27; GF(3)),
             a_1_0: 1-Cocycle in H^*(E27; GF(3)),
             a_1_1: 1-Cocycle in H^*(E27; GF(3)),
             a_3_4: 3-Cocycle in H^*(E27; GF(3)),
             a_3_5: 3-Cocycle in H^*(E27; GF(3))]
            sage: H.2*H.3       # indirect doctest
            (b_2_1)*(b_2_2): 4-Cocycle in H^*(E27; GF(3))
            sage: H.2*H.3 == H.3*H.2
            True
            sage: print(H.7*H.9)
            4-Cocycle in H^*(E27; GF(3)),
            represented by
            [1 2 1 0 0 0 0]
            sage: print(H.9*H.7)
            4-Cocycle in H^*(E27; GF(3)),
            represented by
            [2 1 2 0 0 0 0]
            sage: 2*H.3 == (-1)*H.3 == H.3*2 == -H.3
            True
            sage: (-1)*H.3
            2*(b_2_2): 2-Cocycle in H^*(E27; GF(3))

        """
        cdef COCH C
        if isinstance(right,MODCOCH):
            return self._MODCOCH_(right._Svalue.parent())*right
        C = right  # now, right is supposed to be a cochain
        coho_logger.debug("Compute %s*%s",self.Resl, self.Name, C.Name)
        if C.Deg == 0:
            right = C.Data[0,0]
            if right==1:
                return self
            else:
                return COCH(self._parent, self.Deg, '('+self.Name+')*'+str(right%self.Data.Data.Field), self.Data._mul_long(right), is_polyrep=self._polyrep and C._polyrep)
        if self.Deg == 0:
            left = self.Data[0,0]
            if left==1:
                return C
            else:
                return COCH(C._parent, C.Deg, '('+C.Name+')*'+str(left%C.Data.Data.Field), C.Data._mul_long(left), is_polyrep=self._polyrep and C._polyrep)
        cdef RESL R
        cdef MTX CM, CM1,CM2,OUT
        cdef int n,n_old,n_oldmax,Cdeg,nontips
        cdef int i,j, rk, RK, n_orig
        cdef FEL self_f
        # cdef PTR src,dest
        if isinstance(C,COCH):
            if not (self.Resl is C.resolution()):
                raise ValueError("Cochains must be defined over a common resolution")
            CM = C.MTX()
            n_orig = C.deg()
            while (self.deg()+C.deg())>len(self.Resl.Diff):
                self.Resl.nextDiff()
            R = self.Resl
            nontips = R.G_Alg.Data.nontips
            Cdeg = C.deg()
            n = self.deg()+Cdeg
            # lift to chain maps -> kG=P_0:
            (n1,d1,CM1) = R.CochainToChainmap(self.Deg,self.Data)

            ###########
            # the lift of the second chain map
            # is likely to be known; otherwise it is computed now.
            TryLift = R.Lifts[(n,n_orig,CM)]
            if TryLift is None:
                for n_oldmax from n > n_oldmax >= Cdeg:
                    TryLift = R.Lifts[(n_oldmax,n_orig,CM)]
                    if TryLift != None:
                        break
                if TryLift is None:
                    ((n2,d2,CM2),n_max) = (R.CochainToChainmap(Cdeg,CM), 2*Cdeg)
                    R.setLift(C,2*Cdeg)
                else:
                    ((n2,d2,CM2),n_max) = TryLift
                while (n2<n):
                    (n2,d2,CM2) = R.liftChainMap((n2,d2,CM2))
                    self.Resl.Lifts[(n2,n_orig,CM)] = ((n2,d2,CM2),n_max)
            else:
                ((n2,d2,CM2),n_max) = TryLift
            # compose self with the lift of C
            # OUT = R.composeChainMaps(CM2,CM1,self.deg()+C.deg(),self.deg(),0)
            # the following should be MUCH faster:
            OUT = new_mtx(MatAlloc(self.Data.Data.Field, R.Data.projrank[self.deg()+Cdeg], nontips), self.Data)
            rk = R.Data.projrank[self.deg()]
            RK = R.Data.projrank[self.deg()+Cdeg]
            # CM2 should have rk*RK rows
            # print('Compose Chainmaps')
            for i in range(rk): # loop through the rows of OUT
                self_f = FfExtract(self.Data.Data.Data, i)
                if self_f != FF_ZERO:
                    for j in range(RK): # loop through the entries of the lift of C
                        FfAddMulRow(MatGetPtr(OUT.Data, j), MatGetPtr(CM2.Data, i+rk*j), self_f)
            OUT.set_immutable()
            return COCH(self._parent, self.Deg+Cdeg, '('+self.Name+')*('+C.name()+')', \
                R.ChainmapToCochain((self.Deg+Cdeg,0,OUT)), is_polyrep=self._polyrep and C._polyrep)
        else:
            raise TypeError("Multiplication COCH*%s not defined"%(type(C)))

    def __div__(COCH self, long c):
        """
        Quotient of a cochain by a field element.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: print(H.2)
            2-Cocycle in H^*(E27; GF(3)),
            represented by
            [0 1 0 0]
            rdeg = 0
            ydeg = 0
            sage: print(H.2/2)      # indirect doctest
            2-Cocycle in H^*(E27; GF(3)),
            represented by
            [0 2 0 0]

        """
        if c == 1:
            return self
        else:
            return COCH(self._parent, self.Deg, '('+self.Name+')/'+str(c%self.Data.Data.Field), self.Data/c, is_polyrep=self._polyrep)

    def __pow__(COCH self, int n, x):
        """
        Raise a cochain to some non-negative integer power (cup product with itself).

        NOTE:

        Some data needed for the construction of the cup product
        are cached. This yields to a massive improvement of
        performance in cohomology computations.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.3^4     # indirect doctest
            (b_1_1)**4: 4-Cocycle in H^*(D8; GF(2))
            sage: print(H.3^4)
            4-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 1 0 0 0]

        """
        if n<0:
            raise ValueError("Exponent must be non-negative integer")
        if n==0:
            return int(1)
        while (self.Deg*n>len(self.Resl.Diff)):
            self.Resl.nextDiff()
        s=self.Name
        cdef COCH OUT
        OUT = self
        for i from 1 <= i < n:
            OUT = self*OUT
        if n>1:
            OUT.Name='('+s+')**'+str(n)
        else:
            OUT.Name=s
        return OUT

    def right_multiplication(COCH self):
        """
        Return the cohomology ring endomorphism given by right-multiplication with ``self``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: print(H)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]
            sage: x,a,b,c = H.gens()
            sage: B = b.right_multiplication()
            sage: C = c.right_multiplication()
            sage: B(a) == a*b
            True
            sage: A = a.right_multiplication()
            sage: BA = A(B)
            sage: BA(a) == a*a*b
            True
            sage: r = H.restriction_maps()[2][1]
            sage: rB = r(B)
            sage: r(a)*r(b) == rB(a)
            True

        """
        cdef RESL R = self.Resl
        nt = R.G_Alg.Data.nontips
        fd = R.G_Alg.Data.p
        I = new_mtx(MatId(fd,nt), None)
        I.set_immutable()
        M = R.CochainToChainmap(self.Deg,self.Data)[2]
        name = '(.*%s)'%(self.Name)
        f = self.parent().hom(I,self.parent(),M,-self.Deg)
        f.set_name(name)
        return f

    def normalize(COCH self):
        """
        Scale ``self`` inplace so that its leading coefficient is 1 (if non-zero).

        OUTPUT:

        ``True`` if self is a null-cochain, and ``None`` otherwise

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: C=2*H.1+H.2
            sage: print(C)
            2-Cocycle in H^*(E27; GF(3)),
            represented by
            [2 1 0 0]
            sage: C.normalize()
            sage: print(C)
            2-Cocycle in H^*(E27; GF(3)),
            represented by
            [1 2 0 0]
            sage: C
            (2*(b_2_0)+b_2_1)/2: 2-Cocycle in H^*(E27; GF(3))
            sage: D = 0*H.2
            sage: D.normalize()
            True
            sage: D
            0*(b_2_1): 2-Cocycle in H^*(E27; GF(3))

        """
        cdef FEL f
        FfSetField(self.Data.Data.Field)
        FfSetNoc(self.Data.Data.Noc)
        cdef int i = FfFindPivot(self.Data.Data.Data, &f)
        if i>=0:
            if f!=FF_ONE:
                FfMulRow(self.Data.Data.Data, mtx_tmultinv[f])
                if self.Data._is_immutable:
                    self.Data._cache.clear()
                self.Name = '('+self.Name+')/%d'%(f)
            return None
        else:
            return True

    #######################################################################
    ## Higher structures
    #######################################################################

    def massey_power(COCH self, i=1):
        r"""
        Return the `p^i`-fold restricted Massey product of ``self``, or ``None`` if it does not exist.

        INPUT:

        ``i`` (optional integer, default 1)

        OUTPUT:

        A cochain with the same parent as ``self``, named ``"<%s; %d>"%(self.name(),i)``.

        NOTE:

        We refer to the `p^i`-fold restricted Massey product as the `i`-th restricted
        Massey power.

        According to [Kraines]_, for `p > 2`, the 1st restricted Massey power
        of a cocycle `C` of odd degree in a cohomology ring with coefficients in
        `\mathbb F_p` is minus the Bockstein of the Steenrod `p`-th power, `-\beta P^1(C)`.

        EXAMPLES:

        First, we study an example in the cohomology ring of an elementary abelian
        `p`-group. The cohomology ring is simple enough to allow for an explicit computation
        of Bockstein and Steenrod powers.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(9,2)
            sage: H.make()
            sage: H.gens()
            [1,
             c_2_1: 2-Cocycle in H^*(SmallGroup(9,2); GF(3)),
             c_2_2: 2-Cocycle in H^*(SmallGroup(9,2); GF(3)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(9,2); GF(3)),
             a_1_1: 1-Cocycle in H^*(SmallGroup(9,2); GF(3))]

        We compute the 1st restricted Massey powers of the degree one
        generators. Of course, the degree two generators have no Massey
        power, as they are not nilpotent.
        ::

            sage: print(H.1.massey_power())
            None
            sage: H.element_as_polynomial(H.3.massey_power())
            -c_2_1: 2-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: H.element_as_polynomial(H.4.massey_power())
            -c_2_2: 2-Cocycle in H^*(SmallGroup(9,2); GF(3))

        Since indeed `c_{2,1}` and `c_{2,2}` are the Bocksteins of `a_{1,0}`
        and `a_{1,1}`, Kraines' formula is verified in degree one. But it
        also holds in degree three, as we are now going to show.

        We consider `C = a_{1,0}c_{2,1}`. By Cartan formula and since `P^0`
        is the identity, we have `P^1(C) = P^1(a_{1,0})c_{2,1} + a_{1,0}P(c_{2,1})`.
        Since `P^1` vanishes in degree one and acts as the `p`-th power in
        degree two, we get `P^1(C) = a_{1,0}c_{2,1}^3`. Applying the Bockstein
        operator `\beta`, we get `\beta P^1(C) = c_{2,1}^4`, since
        `\beta(c_{2,1}) = \beta^2(c_{1,0}) = 0` and since
        `\beta(xy)=\beta(x)y + (-1)^{\deg x}x\beta(y)`. Hence, according to
        Kraines, we should get `\langle a_{1,0}c_{2,1}; 1\rangle = - c_{2,1}^4`.
        And indeed::

            sage: (H.1*H.3).massey_power()
            <(c_2_1)*(a_1_0); 1>: 8-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: H.element_as_polynomial(_)
            -c_2_1^4: 8-Cocycle in H^*(SmallGroup(9,2); GF(3))

        We now consider a more advanced example, namely the extraspecial 3-group
        of order 27 and exponent 3::

            sage: H = CohomologyRing(27,3)
            sage: H.make()

        We compute generators for the nil radical of ``H`` and compute the 3-fold Massey
        product for each generator that is of degree not more than 5::

            sage: singular(H).set_ring()
            sage: N = [H(str(X)) for X in H.nil_radical()]
            sage: MP = [X.massey_power() for X in N]
            sage: MP
            [<a_1_0; 1>: 2-Cocycle in H^*(E27; GF(3)),
             <a_1_1; 1>: 2-Cocycle in H^*(E27; GF(3)),
             <a_3_4; 1>: 8-Cocycle in H^*(E27; GF(3)),
             <a_3_5; 1>: 8-Cocycle in H^*(E27; GF(3))]

        After expressing them as polynomials in the cohomology generators, we obtain
        ::

            sage: [H.element_as_polynomial(X) for X in MP]
            [-b_2_0: 2-Cocycle in H^*(E27; GF(3)),
             -b_2_3: 2-Cocycle in H^*(E27; GF(3)),
             b_2_0^2*a_1_1*a_3_5+b_2_0^2*a_1_0*a_3_4+b_2_0*c_6_8: 8-Cocycle in H^*(E27; GF(3)),
             -b_2_0^3*b_2_2-b_2_0^2*a_1_1*a_3_5-b_2_0^2*a_1_0*a_3_5+b_2_3*c_6_8+b_2_0*c_6_8: 8-Cocycle in H^*(E27; GF(3))]

        Hence, particularly interesting seems to be the first restricted Massey power
        of the degree three generators of ``H``. We take the restriction maps to
        the four classes of maximal elementary abelian subgroups, which are all
        of order 9::

            sage: r1 = H.restriction_maps()[2][1]
            sage: r1
            Induced homomorphism of degree 0 from H^*(E27; GF(3)) to H^*(SmallGroup(9,2); GF(3))
            sage: r2 = H.restriction_maps()[3][1]
            sage: r3 = H.restriction_maps()[4][1]
            sage: r4 = H.restriction_maps()[5][1]
            sage: C = H.8
            sage: C
            a_3_4: 3-Cocycle in H^*(E27; GF(3))
            sage: U = r1.codomain()
            sage: U.element_as_polynomial(r1(C))
            0: 3-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: U.element_as_polynomial(r2(C))
            -c_2_2*a_1_0+c_2_1*a_1_1: 3-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: U.element_as_polynomial(r3(C))
            -c_2_2*a_1_0+c_2_1*a_1_1: 3-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: U.element_as_polynomial(r4(C))
            c_2_2*a_1_1-c_2_2*a_1_0+c_2_1*a_1_1: 3-Cocycle in H^*(SmallGroup(9,2); GF(3))

        Hence, after computing Bockstein and Steenrod power in ``U`` as above, and since
        Steenrod power and Bockstein commute with restriction maps, the theorem of Kraines
        tells us that `\langle C; 1\rangle` should restrict to
        `0`, `c_{2,1}c_{2,2}^3 - c_{2,1}^3c_{2,2}`, `c_{2,1}c_{2,2}^3 - c_{2,1}^3c_{2,2}`,
        and `-c_{2,2}^4 - c_{2,1}c_{2,2}^3 + c_{2,1}^3c_{2,2}`. It does::

            sage: CP = C.massey_power()
            sage: U.element_as_polynomial(r1(CP))
            0: 8-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: U.element_as_polynomial(r2(CP))
            c_2_1*c_2_2^3-c_2_1^3*c_2_2: 8-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: U.element_as_polynomial(r3(CP))
            c_2_1*c_2_2^3-c_2_1^3*c_2_2: 8-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: U.element_as_polynomial(r4(CP))
            -c_2_2^4+c_2_1*c_2_2^3-c_2_1^3*c_2_2: 8-Cocycle in H^*(SmallGroup(9,2); GF(3))

        It is known that for this group, a cocycle is uniquely determined by its restrictions
        to the maximal elementary abelian subgroups. Hence, we have verified the computation
        of the first restricted Massey power of ``C``.

        We don't know of general results in the case of even characteristic. However, even
        in this case, we find that cocycles of higher degree can be produced by restricted
        Massey powers, for example for the cohomology ring of `C_4\times C_4`::

            sage: H = CohomologyRing(16,2)
            sage: H.make()
            sage: x,a,b,c,d = H.gens()
            sage: c
            c_1_0: 1-Cocycle in H^*(SmallGroup(16,2); GF(2))
            sage: d
            c_1_1: 1-Cocycle in H^*(SmallGroup(16,2); GF(2))
            sage: H.element_as_polynomial(c.massey_power())
            0: 2-Cocycle in H^*(SmallGroup(16,2); GF(2))
            sage: H.element_as_polynomial(d.massey_power())
            0: 2-Cocycle in H^*(SmallGroup(16,2); GF(2))
            sage: H.element_as_polynomial(c.massey_power(2))
            c_2_1: 2-Cocycle in H^*(SmallGroup(16,2); GF(2))
            sage: H.element_as_polynomial(d.massey_power(2))
            c_2_2: 2-Cocycle in H^*(SmallGroup(16,2); GF(2))

        We verify that the result is consistent with the set-valued non-restricted Massey products::

            sage: sorted(list(H.massey_products(c,c,c,c)))
            [c_2_1: 2-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_2_1+c_1_0*c_1_1: 2-Cocycle in H^*(SmallGroup(16,2); GF(2))]
            sage: sorted(list(H.massey_products(d,d,d,d)))
            [c_2_2: 2-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_2_2+c_1_0*c_1_1: 2-Cocycle in H^*(SmallGroup(16,2); GF(2))]

        """
        if i==0:
            return self
        cdef RESL R = self.resolution()
        # The following Yoneda cochains are self-lifting,
        # i.e., lifting produces a (anti)commutative ladder
        cdef list L = [YCOCH(R,self.Deg,R.CochainToChainmap(self.Deg, self.Data)[2])]
        cdef int j,l
        cdef YCOCH Value
        cdef int fl = R.G_Alg.Data.p
        l = 1
        while l < fl**i:
            if L[0].deg()%2:
                Value = - L[0]*L[-1]
            else:
                Value = L[0]*L[-1]
            for j from 0 < j < l:
                if L[j].deg()%2:
                    Value = Value - L[j]*L[-j-1]
                else:
                    Value = Value + L[j]*L[-j-1]
            l += 1
            if l == fl**i:
                return COCH(self.parent(), Value.deg(), '<%s; %d>'%(self.name(),i), R.ChainmapToCochain((Value.deg(),0,Value[0])))
            S = Value.find_cobounding_yoneda_cochains(all=False)
            if not S:
                return None
            L.append(S[0])

################################################################
## Elements of modular cohomology rings of finite groups
################################################################

def MODCOCH_unpickle(L0,L1,L2,L3,L4,L5,L6=False,L7=None):
    """
    Auxiliary function for unpickling :class:`MODCOCH`.

    TESTS::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(720,763,prime=2)
        sage: H.make()
        sage: H.1 == loads(dumps(H.1)) #indirect doctest
        True
        sage: H.1 is loads(dumps(H.1)) #indirect doctest
        False

    """
    return MODCOCH(L0,L1,deg=L2,name=L3,rdeg=L4,ydeg=L5, is_polyrep=L6, is_NF=L7)

class MODCOCH(RingElement):
    """
    Elements of modular cohomology rings of finite groups.

    See :mod:`pGroupCohomology` or :class:`~pGroupCohomology.modular_cohomology.MODCOHO`
    for examples of cohomology computations.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(720,763,prime=2)
        sage: H.make()
        sage: H.2
        c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))
        sage: print(H('b_3_3*c_3_2+c_2_1^2*c_1_0^2'))   #indirect doctest
        (b_3_3)*(c_3_2)+(((c_2_1)^2)*((c_1_0)^2)): 6-Cocycle in H^*(SmallGroup(720,763); GF(2))
        defined by
        b_1_1^4*c_1_2^2+b_1_0^4*c_1_2^2+c_2_5*b_1_0^3*c_1_2+c_2_5^2*b_1_1^2+c_2_5^2*b_1_0*c_1_2+b_1_1^2*c_1_2^4+c_2_5^2*c_1_2^2

    """
    def __init__(self, parent, value, deg=None, name=None, S=None, rdeg=None, ydeg=None, is_polyrep=False, is_NF=None):
        """
        INPUT:

        - ``parent``: a cohomology ring
          (:class:`~pGroupCohomology.cohomology.COHO` or
          :class:`~pGroupCohomology.modular_cohomology.MODCOHO`).
        - ``value``: a string, or a singular element. This is a
          polynomial representation of an element of ``parent._HP``
          if ``parent`` is the cohomology ring of a non prime power group,
          and of ``parent`` otherwise.
        - ``deg`` (optional int): degree; if not provided, the degree will
          be computed from the given ``value``. The degree should be provided
          if ``value==0``.
        - ``name`` (optional string): Representation in ``parent`` (in general,
          this is *different* from ``value``!). If not given, it will be
          identified with ``repr(value)``.
        - ``S`` (optional): A Singular instance. Must be provided if ``value``
          is a string.
        - ``rdeg`` (optional int): `r`-degree. The `r`-degree should be 1
          for Duflot elements (i.e., the restriction to the centre of a
          Sylow subgroup is not zero), and 0 or None otherwise.
        - ``ydeg`` (optional int): `y`-degree. The `y`-degree should be 1
          for nilpotent elements, and 0 or None otherwise.
        - ``is_polyrep`` (optional boolean): If ``True``, the user asserts
          that ``name`` provides a polynomial representation of self as an
          element of ``parent``. Note that a polynomial representation can
          always be computed using :meth:`~pGroupCohomology.modular_cohomology.MODCOHO.element_as_polynomial`.
        - ``is_NF`` (optional boolean): If ``True``, the user asserts that
          ``value`` is a normal form in ``parent._HP`` respectively ``parent``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.1
            c_2_2: 2-Cocycle in H^*(D8; GF(2))
            sage: type(H.1)
            <type 'pGroupCohomology.cochain.COCH'>
            sage: from pGroupCohomology.cochain import MODCOCH
            sage: c = MODCOCH(H, singular(H.1), name='foo')   # indirect doctest
            sage: c
            foo: 2-Cocycle in H^*(D8; GF(2))
            sage: c == H.1
            True
            sage: loads(dumps(c)) == c
            True

        """
        from pGroupCohomology.auxiliaries import singular
        if S is None:
            if hasattr(value,'parent'):
                singular = value.parent()
        else:
            singular = S
        self._COCH = None
        self._NF = None
        self._str_value = None
        self._lm = None
        self._lmstr = None
        self._lc = None
        self._lt = None
        self._rdeg=rdeg
        self._ydeg=ydeg
        self._sing_val = None
        self._latex = None
        RingElement.__init__(self,parent)
        # self.Resl = parent.Resl
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self._SPparent = singular(parent._HP or parent)
        self._SPparent.set_ring()
        if isinstance(value,basestring):
            self._Svalue = singular.poly(value)
            #self._str_value = value
        else:
            if value.parent() is not singular:
                raise ValueError("parent of %s is not singular"%value)
            # We want a copy anyway, an the following line tests whether
            # value is defined.
            self._Svalue = singular.poly(value.name())
        if deg is None:
            self.Deg = int(self._Svalue.parent().eval('deg(%s)'%(self._Svalue.name())))
        else:
            self.Deg = deg
        if name is None:
            self._name = str(value)
        else:
            self._name = name
        self._polyrep = is_polyrep
        self._NF = is_NF
        if br is not None:
            br.set_ring()

    def __reduce__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: c = H('c_3_2^2+c_3_2*b_3_3+c_2_1*c_1_0*c_3_2')
            sage: c == loads(dumps(c))   # indirect doctest
            True

        """
        return MODCOCH_unpickle, (self.parent(), self.val_str(), self.Deg, self._name, self._rdeg, self._ydeg, self._polyrep,self._NF)

    def _richcmp_(self, C, int x):
        """
        Comparison of cohomology elements.

        The comparison of two elements (both type <MODCOCH> of the same
        cohomology ring ``H`` is done first by degree, then by comparison
        in the monomial ordering of ``H._HP`` (if ``H`` is an instance of
        :class:`~pGroupCohomolgy.modular_cohomology.MODCOHO`) respectively
        of ``H`` (otherwise).

        NOTE:

        The comparison is by taking normal forms, since
        ``singular(H.subgroup_cohomology())`` respectively
        ``singular(H.sylow_cohomology())`` are quotient rings.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: print(H)
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
            <BLANKLINE>

        Apparently, adding the relation must not change the value
        of a cohomology element::

            sage: H.1^2*H.2^2+H(H.rel(0))==H.1^2*H.2^2
            True

        A zero-valued element of degree 6 is greater than a non-zero
        element of degree four::

            sage: H(H.rel(0)).is_zero()
            True
            sage: H.1*H.2**2 < H(H.rel(0))
            True

        Before comparing, the two elements are turned into normal form.
        Thus, it is possible that before comparison the two elements,
        represented as polynomials in the cohomology ring of the underlying
        subgroup, look different::

            sage: c = H.1^3+H.4^2
            sage: singular(c.parent()._HP).set_ring()
            sage: c.value() == (H.1^3+H.4^2)._NF_().value()
            False
            sage: c == (H.1^3+H.4^2)._NF_()
            True
            sage: c.value() == (H.1^3+H.4^2)._NF_().value()
            True

        """
        assert isinstance(C,COCH) or isinstance(C,MODCOCH)
        if isinstance(C, MODCOCH):
            other = C
        else:
            other = C._MODCOCH_()
        cdef bint out
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        dgb = singular.eval('degBound')
        # < 0, <= 1, == 2, != 3, > 4, >= 5
        try:
            if x==0:
                if self.deg() < other.deg():
                    return True
                self._NF_()
                other._NF_()
                singular(self.parent()._HP or self.parent()).set_ring()
                out = (self.deg()==other.deg()) and (self.value()<other.value())
                return out
            if x==1:
                if self.deg() < other.deg():
                    return True
                self._NF_()
                other._NF_()
                singular(self.parent()._HP or self.parent()).set_ring()
                out = (self.deg()==other.deg()) and (self.value()<=other.value())
                return out
            if x==2:
                if self.deg() != other.deg():
                    return False
                self._NF_()
                other._NF_()
                singular(self.parent()._HP or self.parent()).set_ring()
                out = (self.value()==other.value())
                return out
            if x==3:
                if self.deg() != other.deg():
                    return True
                self._NF_()
                other._NF_()
                singular(self.parent()._HP or self.parent()).set_ring()
                out = (self.value()!=other.value())
                return out
            if x==4:
                if self.deg() > other.deg():
                    return True
                self._NF_()
                other._NF_()
                singular(self.parent()._HP or self.parent()).set_ring()
                out = (self.deg()==other.deg()) and (self.value()>other.value())
                return out
            if x==5:
                if self.deg() > other.deg():
                    return True
                self._NF_()
                other._NF_()
                singular(self.parent()._HP or self.parent()).set_ring()
                out = (self.deg()==other.deg()) and (self.value()>=other.value())
                return out
            return NotImplemented
        finally:
            if br is not None:
                br.set_ring()
            singular.eval('degBound='+dgb)

    def _repr_(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: H.2      # indirect doctest
            c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: H('c_3_2^2+c_3_2*b_3_3+c_2_1*c_1_0*c_3_2')
            (c_3_2)^2+((c_3_2)*(b_3_3))+(((c_2_1)*(c_1_0))*(c_3_2)): 6-Cocycle in H^*(SmallGroup(720,763); GF(2))

        """
        return self._name+": %d-Cocycle in %s"%(self.Deg, repr(self.parent()))

    def __str__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: print(H.2)     # indirect doctest
            c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))
            defined by
            b_1_1+c_1_2
            sage: print(H('c_3_2^2+c_3_2*b_3_3+c_2_1*c_1_0*c_3_2'))
            (c_3_2)^2+((c_3_2)*(b_3_3))+(((c_2_1)*(c_1_0))*(c_3_2)): 6-Cocycle in H^*(SmallGroup(720,763); GF(2))
            defined by
            c_2_5*b_1_0^3*c_1_2+c_2_5*b_1_1^2*c_1_2^2+c_2_5^2*b_1_1*c_1_2+c_2_5^2*b_1_0*c_1_2+c_2_5*b_1_1*c_1_2^3

        Note that, when printing the value that the element takes in a subgroup,
        it is not necessarily in normal form.

        """
        return repr(self)+'\ndefined by\n'+self.val_str()

    def set_latex_name(self, s):
        r"""
        Declare how self should be typeset in \LaTeX.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: latex(H.2)
            b_{1,0}
            sage: (H.2).set_latex_name('H_2')
            sage: latex(H.2)
            H_2

        """
        if not isinstance(s, basestring):
            raise TypeError("String expected")
        self._latex = s

    def _latex_(self):
        r"""
        Return a \LaTeX typeset.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: latex((H.1*H.2*H.3+H.3*H.4)) # indirect doctest
            b_{3,3} c_{3,2}+c_{2,1} c_{1,0} b_{3,3}

        """
        if self._latex is not None:
            return self._latex
        from pGroupCohomology.auxiliaries import singular
        try:
            br = singular('basering')
        except TypeError:
            br = None
        from pGroupCohomology.factory import _name2latex
        singular(self.parent()).set_ring()
        self._latex = _name2latex(repr(singular(self)))
        if br is not None:
            br.set_ring()
        return self._latex

    def __copy__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: H.2 is copy(H.2)   # indirect doctest
            False
            sage: H.2 == copy(H.2)
            True

        """
        out = MODCOCH(self.parent(), self.value(), deg=self.Deg, name=self._name, rdeg=self._rdeg, ydeg=self._ydeg, is_polyrep=self._polyrep, is_NF=self._NF)
        out._str_value = self._str_value
        return out

    #########
    # Dealing with standard attributes (name, deg etc)

    def deg(self):
        """
        Degree of a cohomology element.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: H('c_3_2^2+b_3_3*c_3_2+c_2_1*c_1_0*c_3_2').deg()
            6

        The degree may be explicitly provided in the definition of the
        cohomology ring element, even if it is not clear from its given
        value::

            sage: from pGroupCohomology.cochain import MODCOCH
            sage: c = MODCOCH(H, '0', deg=15)
            sage: c.deg()
            15

        """
        return self.Deg

    def rdeg(self):
        """
        `r`-degree.

        This is supposed to be 1 for Duflot elements, i.e., for those
        elements that have a non-zero restrictions to the centre of
        a Sylow subgroup.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: [t.rdeg() for t in H.Gen]
            [1, 1, 0, 1]

        So, the restriction of all but the third generator to the centre
        of a Sylow subgroup should be non-zero::

            sage: r = H.restriction_maps()[1][1]
            sage: r
            Induced homomorphism of degree 0 from H^*(SmallGroup(720,763); GF(2)) to H^*(SmallGroup(4,2); GF(2))
            sage: print(r(H.1)._NF_())
            c_1_1^2: 2-Cocycle in H^*(SmallGroup(4,2); GF(2))
            defined by
            c_1_1^2
            sage: print(r(H.2)._NF_())
            c_1_0: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))
            defined by
            c_1_0
            sage: print(r(H.3)._NF_())
            0: 3-Cocycle in H^*(SmallGroup(4,2); GF(2))
            defined by
            0
            sage: print(r(H.4)._NF_())
            c_1_0*c_1_1^2: 3-Cocycle in H^*(SmallGroup(4,2); GF(2))
            defined by
            c_1_0*c_1_1^2

        """
        return self._rdeg

    def ydeg(self):
        """
        `y`-degree.

        This is supposed to be 1 for nilpotent elements.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=3)
            sage: H.make()
            sage: [t.ydeg() for t in H.Gen]
            [0, 0, 1, 1]

        Indeed, the last two generators are nilpotent::

            sage: print(H.3**2)
            (a_3_0)^2: 6-Cocycle in H^*(SmallGroup(720,763); GF(3))
            defined by
            0
            sage: print(H.4**2)
            (a_7_1)^2: 14-Cocycle in H^*(SmallGroup(720,763); GF(3))
            defined by
            0

        """
        return self._ydeg

    def setname(self, s, is_polyrep=False):
        """
        Set the name of a cohomology ring element.

        INPUT:

        - ``s`` (string), new namme of the element
        - ``is_polyrep`` (optional boolean, default ``False``):
          If ``True``, the user asserts that the new name provides
          a polynomial representation of the element, expressed
          in the given generator names of the cohomology ring

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: c = H.2
            sage: c.setname('charly')
            sage: c
            charly: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: c.name()
            'charly'
            sage: c.as_polynomial()
            'c_1_0'
            sage: c
            c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))

        """
        if isinstance(s,basestring):
            self._name = s
        else:
            raise TypeError("string expected")
        self._latex = None
        self._polyrep = is_polyrep

    def as_polynomial(self):
        """
        Find a polynomial representation of ``self``.

        OUTPUT:
        A string that defines a polynomial, expressed in the
        given generator names of the cohomology ring

        NOTE:
        The name of the cohomology ring element will be
        changed into the polynomial expression.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: c = H.2
            sage: c.setname('charly')
            sage: c
            charly: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: c.name()
            'charly'
            sage: c.as_polynomial()
            'c_1_0'
            sage: c
            c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))

        """
        if not self._polyrep:
            self.parent().element_as_polynomial(self)
        return self.name()

    def name(self):
        """
        Return the name of the cohomology ring element.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: c = H.2
            sage: c.name()
            'c_1_0'
            sage: c.setname('charly')
            sage: c
            charly: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: c.name()
            'charly'
            sage: c.as_polynomial()
            'c_1_0'
            sage: c
            c_1_0: 1-Cocycle in H^*(SmallGroup(720,763); GF(2))

        """
        return self._name

    ##############
    ## Different representations
    def value(self):
        """
        The value of self in the Singular interface.

        NOTE:

        By "value", we mean its representation in the Singular
        interface as a stable element in the cohomology ring of
        the chosen subgroup.

        This value is not unique, as the cohomology ring of
        the subgroup is a quotient ring. Thus, the value is a
        coset representative, and it is not necessarily in normal
        form.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: singular(H.subgroup_cohomology()).set_ring()
            sage: (H.1*H.2+H.3)._NF_().value()
            b_1_1^2*c_1_2+b_1_0^2*c_1_2+c_2_5*b_1_1+c_2_5*b_1_0+b_1_1*c_1_2^2+c_2_5*c_1_2

        Note that if Singular crashed, it is attempted to reconstructed the value.
        However, this is only possible if :meth:`val_str` was called before.
        ::

            sage: c = (H.1*H.2+H.3)._NF_()
            sage: c.val_str()
            'b_1_1^2*c_1_2+b_1_0^2*c_1_2+c_2_5*b_1_1+c_2_5*b_1_0+b_1_1*c_1_2^2+c_2_5*c_1_2'
            sage: singular.quit()
            sage: CohomologyRing.global_options('info')
            sage: c.value()
            H^*(D8xC2; GF(2)):
                      Reconstructing data in the Singular interface
            b_1_1^2*c_1_2+b_1_0^2*c_1_2+c_2_5*b_1_1+c_2_5*b_1_0+b_1_1*c_1_2^2+c_2_5*c_1_2
            sage: CohomologyRing.global_options('warn')

        """
        singular = self._Svalue.parent()
        try:
            self._Svalue._check_valid()
        except:
            self._reconstruct_singular_(singular)
        return self._Svalue

    def val_str(self):
        """
        A polynomial representation as stable element.

        OUTPUT:

        A string that provides a polynomial representation for
        the cohomology ring element, expressed as a (stable)
        cocycle of the underlying subgroup.

        NOTE:

        In general, the normal form is not computed before
        returning the result.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: (H.1*H.2)._NF_().val_str()
            'b_1_1^2*c_1_2+b_1_0^2*c_1_2+c_2_5*b_1_1+b_1_1*c_1_2^2+c_2_5*c_1_2'
            sage: H.one().val_str()
            '1'

        """
        if self._str_value is not None:
            return self._str_value
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        singular(self.parent()._HP or self.parent()).set_ring()
        if singular.eval('typeof(%s)'%self.value().name())=='int':
            return singular.eval(self.value().name())
        if not self._NF:
            singular.eval('%s=NF(%s,std(0))'%(self.value().name(),self.value().name()))
        self._NF = True
        cdef int SizePieces = coho_options.get('SingularCutoff',50)
        cdef list L = []
        cdef int j
        cdef int a = int(singular.eval('size(%s)'%self.value().name()))
        cdef int nr = a//SizePieces
        for j from 0<=j<nr:
            L.append(singular.eval('print(%s[%d..%d])'%(self.value().name(),j*SizePieces+1,(j+1)*SizePieces)))
            if len(L)>1 and (L[-1][0] not in ['-','+']):
                L.insert(-1,'+')
        if nr*SizePieces<a:
            L.append(singular.eval('print(%s[%d..%d])'%(self.value().name(),nr*SizePieces+1,a)))
            if len(L)>1 and (L[-1][0] not in ['-','+']):
                L.insert(-1,'+')
        self._str_value = ''.join(L) if L else '0'
        if br is not None:
            br.set_ring()
        return self._str_value

    def _singular_(self, S):
        """
        Represent ``self`` as an element of the Singular interface version of the parent cohomology ring.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: singular(H).set_ring()
            sage: singular(H.1*H.2+H.3)    # indirect doctest
            b_3_3+c_2_1*c_1_0
            sage: parent(_)
            Singular

        """
        if (self._sing_val is not None) and (self._sing_val.parent() is S):
            try:
                self._sing_val._check_valid()
                return self._sing_val
            except ValueError:
                pass
        self.parent()._singular_(S).set_ring()
        self._sing_val = S(self.as_polynomial())
        return self._sing_val

    def _reconstruct_singular_(self,S=None):
        """
        Automatic reconstruction of data in the Singular interface when it crashed.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: print(H.6*H.8)
            (a_7_1)*(a_15_3): 22-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            2*c_2_1^5*c_2_2^5*a_1_0*a_1_1

        After quitting singular, the data are reconstructed (which is
        visible in the log), so that the computation can be recovered::

            sage: singular.quit()
            sage: CohomologyRing.global_options('info')
            sage: print(H.6*H.8)   # indirect doctest
            H^*(SmallGroup(25,2); GF(5)):
                      Reconstructing data in the Singular interface
            (a_7_1)*(a_15_3): 22-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            2*c_2_1^5*c_2_2^5*a_1_0*a_1_1
            sage: CohomologyRing.global_options('warn')

        """
        if S is None:
            from pGroupCohomology.auxiliaries import singular
            S = singular
        try:
            br = S('basering')
        except:
            br = None
        self._SPparent = S(self.parent()._HP or self.parent())
        self._SPparent.set_ring()
        self._sing_val = None
        try:
            self._Svalue = S.poly(self._str_value)
        except:
            try:
                if not self._polyrep:
                    raise RuntimeError(repr(self)+' is not known to be defined by a polynomial')
                tmp = self.parent()(self.name())
                self._str_value = tmp.val_str()
                self._Svalue = S.poly(tmp.value())
            except BaseException, msg:
                if br is not None:
                    br.set_ring()
                raise RuntimeError(msg.args[0]+"\nSorry, couldn't reconstruct %s after singular crashed"%repr(self))
        if br is not None:
            br.set_ring()

    def as_cocycle_in_subgroup(self):
        """
        Represent ``self`` as stable cocycle of the chosen subgroup.

        OUTPUT:

        The element (:class:`~MODCOCH`) of
        ``self.parent().subgroup_cohomology()`` by which ``self`` is
        defined.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.AlternatingGroup(8)
            sage: H = CohomologyRing(G,prime=2,GroupName='A8') # long time
            sage: H.make()              # long time
            sage: H.subgroup_cohomology()
            H^*(SmallGroup(192,1493); GF(2))
            sage: H.1.as_cocycle_in_subgroup()
            (b_1_0)^2+(b_2_2)+(b_2_1): 2-Cocycle in H^*(SmallGroup(192,1493); GF(2))
            sage: H.subgroup_cohomology()('b_1_0^2+b_2_2+b_2_1')*H.2.as_cocycle_in_subgroup() == (H.1*H.2).as_cocycle_in_subgroup()
            True

        """
        P = self.parent()
        if P._HP is None:
            return self
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self._NF_()
        singular(P._HP).set_ring()
        S = self.value()
        if S.parent().eval('%s==0'%S.name())=='1':
            if br is not None:
                br.set_ring()
            return MODCOCH(P._HP,0,S=singular,deg=self.deg())
        s = self.val_str()
        if br is not None:
            br.set_ring()
        if P._HP is P._HSyl: # we want MODCOCH
            return MODCOCH(P._HP,self.value(),name=s,deg=self.deg())
        return P._HP(s)


    def as_cocycle_in_sylow(self):
        """
        Represent ``self`` as stable cocycle of the Sylow subgroup.

        OUTPUT:

        The element (:class:`~pGroupCohomology.cochain.MODCOCH`)
        of ``self.parent().sylow_cohomology()`` that corresponds
        to ``self``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.AlternatingGroup(8)
            sage: H = CohomologyRing(G,prime=2,GroupName='A8')  # long time
            sage: H.make()                          # long time
            sage: H.1.as_cocycle_in_sylow()
            b_1_1*b_1_2+b_1_1^2+b_1_0^2+b_2_5+b_2_4: 2-Cocycle in H^*(SmallGroup(64,138); GF(2))
            sage: H.sylow_cohomology()('b_1_1*b_1_2+b_1_1^2+b_1_0^2+b_2_5+b_2_4')*H.2.as_cocycle_in_sylow() == (H.1*H.2).as_cocycle_in_sylow()
            True

        """
        if self.parent()._HP is None:
            return self
        OUT = self.as_cocycle_in_subgroup()
        while OUT.parent() is not self.parent()._HSyl:
            OUT = OUT.as_cocycle_in_subgroup()
        return OUT

    #############
    ## Basic and not so basic arithmetic

    def _neg_(self):
        """
        Additive inverse.

        TESTS:

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: print(H.2)
            c_8_0: 8-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_2^4+c_2_1^4
            sage: print(-H.2) #indirect doctest
            -(c_8_0): 8-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            -c_2_2^4-c_2_1^4

        """
        try:
            return MODCOCH(self.parent(), -self._Svalue, self.Deg, '-('+self._name+')', is_polyrep=self._polyrep)
        except TypeError:
            try:
                br = self._Svalue.parent()('basering')
            except:
                br = None
            try:
                self._SPparent.set_ring()
            except: # singular crashed
                self._reconstruct_singular_()
            OUT = -self
            if br is not None:
                br.set_ring()
            return OUT

    def __pow__(self,int n):
        """
        Exponentiation.

        TESTS:

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: print(H.2)
            c_8_0: 8-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_2^4+c_2_1^4
            sage: print(H.2^3)   # indirect doctest
            (c_8_0)^3: 24-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_2^12-2*c_2_1^4*c_2_2^8-2*c_2_1^8*c_2_2^4+c_2_1^12

        """
        if n<0:
            raise ValueError("negative exponents are not allowed")
        try:
            return MODCOCH(self.parent(), self._Svalue.parent()('%s^%d'%(self._Svalue.name(),n)), self.Deg*n, '('+self._name+')^%d'%n, is_polyrep=self._polyrep)
        except TypeError:
            try:
                br = self._Svalue.parent()('basering')
            except:
                br = None
            try:
                self._SPparent.set_ring()
            except: # singular crashed
                self._reconstruct_singular_()
            OUT = self**n
            if br is not None:
                br.set_ring()
            return OUT

    def __nonzero__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(252,10,prime=2)
            sage: H.make()
            sage: H.1.is_zero() #indirect doctest
            False
            sage: (2*H.1).is_zero() #indirect doctest
            True
            sage: (H.3^2+H.2*H.3+H.2^2+H.1^3).is_zero() #indirect doctest
            True

        """
        return self.lc()!=0

    def _add_(self, other):
        """
        Sum of two elements (same degree) of a cohomology ring.

        TESTS:

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(720,763,prime=2)
            sage: X.make()
            sage: print(X.3+X.4) #indirect doctest
            b_3_3+(c_3_2): 3-Cocycle in H^*(SmallGroup(720,763); GF(2))
            defined by
            b_1_0^2*c_1_2+c_2_5*b_1_0+c_2_5*c_1_2

        It is possible to add :class:`MODCOCH` with :class:`COCH`::

            sage: print(X.3.as_cocycle_in_sylow()+X.sylow_cohomology()('c_2_5*b_1_0'))
            c_2_5*b_1_0+(c_2_5*b_1_0): 3-Cocycle in H^*(D8xC2; GF(2))
            defined by
            0

        """
        if not isinstance(other, MODCOCH):
            if hasattr(other,'_MODCOCH_'):
                return self+other._MODCOCH_(self._Svalue.parent())
            if other!=0:
                raise TypeError("Second summand must not be of type %s"%type(other))
            return self
        if self.Deg != other.deg():
            raise ValueError("The summands must be in the same degree")
        try:
            return MODCOCH(self.parent(), self._Svalue+other._Svalue,self.Deg, self._name+'+('+other.name()+')', is_polyrep=self._polyrep and other._polyrep)
        except TypeError:
            try:
                br = self._Svalue.parent()('basering')
            except:
                br = None
            try:
                self._SPparent.set_ring()
            except: # singular crashed
                self._reconstruct_singular_()
                other._reconstruct_singular_()
            OUT = self+other
            if br is not None:
                br.set_ring()
            return OUT

    def _sub_(self, other):
        """
        Difference.

        TESTS:

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: print(H.5)
            a_7_0: 7-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_2^3*a_1_1+c_2_1^3*a_1_0
            sage: print(H.6)
            a_7_1: 7-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_1*c_2_2^2*a_1_0-c_2_1^2*c_2_2*a_1_1
            sage: print(H.5-H.6) #indirect doctest
            a_7_0-(a_7_1): 7-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_2^3*a_1_1-c_2_1*c_2_2^2*a_1_0+c_2_1^2*c_2_2*a_1_1+c_2_1^3*a_1_0

        """
        if not isinstance(other, MODCOCH):
            if hasattr(other,'_MODCOCH_'):
                return self-other._MODCOCH_(self._Svalue.parent())
            if other!=0:
                raise TypeError("Second summand must not be of type %s"%type(other))
            return self
        if self.Deg != other.deg():
            raise ValueError("The summands must be in the same degree")
        try:
            return MODCOCH(self.parent(), self._Svalue-other._Svalue, self.Deg, self._name+'-('+other.name()+')', is_polyrep=self._polyrep and other._polyrep)
        except TypeError:
            try:
                br = self._Svalue.parent()('basering')
            except:
                br = None
            try:
                self._SPparent.set_ring()
            except: # singular crashed
                self._reconstruct_singular_()
                other._reconstruct_singular_()
            OUT = self-other
            if br is not None:
                br.set_ring()
            return OUT

    def _lmul_(self, other):
        """
        Scalar multiplication.

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: H.1*2   # indirect doctest
            (a_6_0)*(2): 6-Cocycle in H^*(SmallGroup(400,206); GF(5))

        """
        if other==1:
            return self
        try:
            return MODCOCH(self.parent(), '('+self.val_str()+')*('+repr(other)+')', deg=self.Deg, name='('+self._name+')*('+repr(other)+')', is_polyrep=self._polyrep)
        except TypeError: # this happens, for instance, if singular crashes
            try:
                br = self._Svalue.parent()('basering')
            except:
                br = None
            try:
                self._SPparent.set_ring()
            except: # singular crashed
                self._reconstruct_singular_()
                other._reconstruct_singular_()
            OUT = self*other
            if br is not None:
                br.set_ring()
            return OUT

    _rmul_ = _lmul_

    def _mul_(self, other):
        """
        Cup product.

        TESTS:

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: print(H.5)
            a_7_0: 7-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_2^3*a_1_1+c_2_1^3*a_1_0
            sage: print(H.6)
            a_7_1: 7-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_1*c_2_2^2*a_1_0-c_2_1^2*c_2_2*a_1_1
            sage: print(H.5*H.6) #indirect doctest
            (a_7_0)*(a_7_1): 14-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            -c_2_1*c_2_2^5*a_1_0*a_1_1-c_2_1^5*c_2_2*a_1_0*a_1_1
            sage: print(3*H.5) #indirect doctest
            (a_7_0)*(3): 7-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            -2*c_2_2^3*a_1_1-2*c_2_1^3*a_1_0
            sage: print(H.6*3) #indirect doctest
            (a_7_1)*(3): 7-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            -2*c_2_1*c_2_2^2*a_1_0+2*c_2_1^2*c_2_2*a_1_1

        """
        try:
            self._SPparent.set_ring()
        except: # singular crashed
            self._reconstruct_singular_()
            other._reconstruct_singular_()
        from pGroupCohomology.cochain import COCH
        if isinstance(other,COCH):
            return self*other._MODCOCH_(self._Svalue.parent())
        try:
            return MODCOCH(self.parent(), self._Svalue*other._Svalue, deg=self.Deg+other.deg(),name='('+self._name+')*('+other.name()+')', is_polyrep=self._polyrep and other._polyrep)
        except TypeError:
            try:
                br = self._Svalue.parent()('basering')
            except:
                br = None
            try:
                self._SPparent.set_ring()
            except: # singular crashed
                self._reconstruct_singular_()
                other._reconstruct_singular_()
            OUT = self*other
            if br is not None:
                br.set_ring()
            return OUT

    def __div__(self, other):
        """
        Division by an invertible element of the base ring.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: print(H.1)
            a_6_0: 6-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_1*c_2_2*a_1_0*a_1_1
            sage: print(H.1/3) #indirect doctest
            (a_6_0)/(3): 6-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            2*c_2_1*c_2_2*a_1_0*a_1_1

        It is impossible to divide by :class:`MODCOCH`, and of
        course division by zero is not possible either::

            sage: H.2/H.1
            Traceback (most recent call last):
            ...
            TypeError: Can not divide by <class 'pGroupCohomology.cochain.MODCOCH'>

        """
        try:
            self._SPparent.set_ring()
        except: # singular crashed
            self._reconstruct_singular_()
            other._reconstruct_singular_()
        if not isinstance(other, MODCOCH):
            if other==1:
                return self
            try:
                return MODCOCH(self.parent(), self._Svalue/other, name='('+self._name+')/('+repr(other)+')', is_polyrep=self._polyrep)
            except:
                raise ZeroDivisionError
        raise TypeError('Can not divide by %s'%repr(MODCOCH))

    def is_nilpotent(self):
        """
        Tells whether this cocycle is nilpotent.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(60,3,prime=2)
            sage: H.make()
            sage: singular(H).set_ring()
            sage: H.nil_radical()
            c_1_0
            sage: H.gens()
            [1,
             c_2_0: 2-Cocycle in H^*(SmallGroup(60,3); GF(2)),
             c_1_0: 1-Cocycle in H^*(SmallGroup(60,3); GF(2))]
            sage: H.gen(1).is_nilpotent()
            False
            sage: H.gen(2).is_nilpotent()
            True
            sage: bool(H.gen(2)^2)
            False

        An example in odd characteristic::

            sage: H = CohomologyRing(1620, 23, prime=3)
            sage: H.make()
            sage: H.1.is_nilpotent()
            True
            sage: bool(H.1^2)
            True
            sage: bool(H.1^3)
            False
            sage: H.2.is_nilpotent()
            False

        """
        H = self.parent()
        ch = H.base_ring().characteristic()
        singular = self._SPparent.parent()
        if not self:
            return True
        if ch!=2 and self.deg()%2:
            return True
        if not H.MaxelPos:
            s = singular(self)
            singular(H).set_ring()
            return singular.eval('NF({}, {})'.format(s.name(), H.nil_radical().name()))=='0'
        for p in H.MaxelPos:
            phi = H.RestrMaps[p][1]
            self_res = phi(self)
            if ch==2:
                if self_res:
                    return False
            else:
                if singular(self_res).NF(self_res.parent().nil_radical()):
                    return False
        return True

    def nilpotency_degree(self):
        """
        The smallest exponent by which this cocycle becomes zero.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(60,3,prime=2)
            sage: H.make()
            sage: singular(H).set_ring()
            sage: H.nil_radical()
            c_1_0
            sage: H.gens()
            [1,
             c_2_0: 2-Cocycle in H^*(SmallGroup(60,3); GF(2)),
             c_1_0: 1-Cocycle in H^*(SmallGroup(60,3); GF(2))]
            sage: H.1.is_nilpotent()
            False
            sage: H.1.nilpotency_degree()
            +Infinity
            sage: (H.1*0).nilpotency_degree()
            1
            sage: H.2.is_nilpotent()
            True
            sage: bool(H.2^2)
            False
            sage: H.2.nilpotency_degree()
            2

        An example in odd characteristic::

            sage: H = CohomologyRing(1620, 23, prime=3)
            sage: H.make()
            sage: for g in H.Gen:
            ....:     if g.nilpotency_degree() == 3:
            ....:         break
            ....:
            sage: bool(g^2)
            True
            sage: bool(g^3)
            False
            sage: H.2.is_nilpotent()
            False
            sage: H.2.nilpotency_degree()
            +Infinity
            sage: (H.2*0).nilpotency_degree()
            1

        """
        if not self:
            return 1
        if not self.is_nilpotent():
            return Infinity
        singular = self._SPparent.parent()
        s = singular(self)
        singular(self.parent()).set_ring()
        d = 1
        while True:
            d += 1
            if singular.eval('NF(%s**%d, std(0))'%(s.name(),d))=='0':
                return d

    def massey_power(self, i=1):
        """
        Experimental: Restricted Massey power.

        ALGORITHM:

        A cocycle ``C`` is expressed as a (stable) element of the
        cohomology of the Sylow subgroup. The Massey power is computed
        there (see
        :meth:`~pGroupCohomology.cochain.COCH.massey_power`).

        NOTE:

        We did not prove that the result always is a stable
        element. But if it is, it yields the restricted Massey power
        of ``C``. Therefore, this method is merely experimental.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(432,234,prime=3)
            sage: H.make()
            sage: c = H.5; c
            a_3_0: 3-Cocycle in H^*(SmallGroup(432,234); GF(3))
            sage: cS = c.as_cocycle_in_sylow(); cS
            b_2_3*a_1_1+b_2_0*a_1_0: 3-Cocycle in H^*(E27; GF(3))
            sage: cM = c.massey_power(); cM
            b_4_0*b_4_1+b_4_0^2: 8-Cocycle in H^*(SmallGroup(432,234); GF(3))
            sage: cSM = cS.massey_power(); cSM
            <(b_2_3)*(a_1_1)+(b_2_0)*(a_1_0); 1>: 8-Cocycle in H^*(E27; GF(3))
            sage: cM.as_cocycle_in_sylow() == cSM
            True

        """
        # this is experimental
        HSyl = self.parent()._HSyl or self.parent()
        selfCOCH = HSyl(self.as_cocycle_in_sylow().name())
        COCHpower = selfCOCH.massey_power(i)
        if COCHpower is None:
            return None
        if HSyl is self.parent():
            return COCHpower
        out = self.parent().stable_to_polynomial(COCHpower)
        if out is None:
            raise RuntimeError("This implementation is experimental. Your example is not covered. Please inform the author.")
        return out

    def _NF_(self, id=None):
        """
        Replace the underlying value in the cohomology of a subgroup by its normal form.

        INPUT:

        ``id`` (optional list of strings): Compute the normal form
        subject an ideal in the Singular version of the cohomology
        ring of the underlying subgroup, given by a list of strings.

        OUTPUT:

        ``self``. The underlying value is changed internally.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2)
            sage: H.make()
            sage: c = H.1*H.2
            sage: singular(H.subgroup_cohomology()).set_ring()
            sage: c.value()
            b_1_0^2*b_1_1+b_1_1^2*c_1_2+b_1_0^2*c_1_2+c_2_5*b_1_1+b_1_1*c_1_2^2+c_2_5*c_1_2

        The value (i.e., the restriction to the subgroup used in the computation of ``H``)
        is not in normal form. We will change this now::

            sage: c._NF_()
            (c_2_1)*(c_1_0): 3-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: c.value()
            b_1_1^2*c_1_2+b_1_0^2*c_1_2+c_2_5*b_1_1+b_1_1*c_1_2^2+c_2_5*c_1_2

        We can also reduce it modulo one of the generators::

            sage: c._NF_(['c_1_2'])
            (c_2_1)*(c_1_0): 3-Cocycle in H^*(SmallGroup(720,763); GF(2))
            sage: c._Svalue
            c_2_5*b_1_1

        Note that this changes the value of ``c`` internally. Computing the
        normal form with respect to a non-trivial ideal should thus be used
        with extreme care.
        ::

            sage: c == H.1*H.2
            False

        """
        try:
            self._Svalue._check_valid()
        except:
            self._reconstruct_singular_()
        if (id is None) and (self._NF is not None):
            return self
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        singular(self.parent()._HP or self.parent()).set_ring()
        if id is None:
            singular.eval('%s=NF(%s,std(0))'%(self._Svalue.name(),self._Svalue.name()))
            self._NF = True
        else:
            self._lc = self._lm = self._lt = None
            self._Svalue = self._Svalue.parent()('NF(%s,std(ideal(%s)))'%(self._Svalue.name(), ','.join(id)))
            self._str_value = None
        if br is not None:
            br.set_ring()
        return self

    def nilreduce(self):
        """
        Inplace reduction of ``self``'s value by the ideal generated by nilpotent generators.

        OUTPUT:

        ``self``. Before, all nilpotent generators of the cohomology
        containing ``self.value()`` are killed in ``self.value()``.

        EXAMPLES:

        Since this test relies on the ring presentation of the
        cohomology of a certain subgroup, we compute it from scratch,
        rather than relying on potentially outdated data in the local
        sources.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(81,8, from_scratch=True)
            sage: X.make()
            sage: H = CohomologyRing(648,132,prime=3, from_scratch=True)
            sage: H.make()
            sage: c = copy(H.5)
            sage: c
            c_6_0: 6-Cocycle in H^*(SmallGroup(648,132); GF(3))

        ``c`` is a regular element (marked by the letter 'c'
        in its name). We took a *copy* of the generator of ``H``
        since ``c`` will be changed inplace. Interpreted as
        an element of the cohomology of the underlying subgroup,
        it has one nilpotent summand::

            sage: c.as_cocycle_in_subgroup()
            b_6_3+a_1_0*a_5_2-c_6_4: 6-Cocycle in H^*(SmallGroup(81,8); GF(3))

        We kill this summand::

            sage: c.nilreduce()
            c_6_0: 6-Cocycle in H^*(SmallGroup(648,132); GF(3))
            sage: c.as_cocycle_in_subgroup()
            b_6_3-c_6_4: 6-Cocycle in H^*(SmallGroup(81,8); GF(3))

        Indeed, the value of ``c`` has changed::

            sage: c == H.5
            False

        """
        # This method usually is called if the parent
        # is a p-group. The implementation is more general:
        P = self.parent()._HP or self.parent()
        cdef list id = [X.name() for X in P.Gen if X.ydeg()]
        if not id:
            return self._NF_()
        return self._NF_(id)

    def lc(self):
        """
        Leading coefficient of ``self`` (type <int>).

        OUTPUT:

        An element of a modular cohomology ring of a finite group
        is given by a stable element in the cohomology ring of a
        suitable subgroup. Expressing the stable element as a
        polynomial, this method returns its leading coefficient,
        as an int.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: singular(H.subgroup_cohomology()).set_ring()
            sage: (H.6*H.8).lc()
            2

        """
        if self._lc is not None:
            return self._lc
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self._NF_()
        self._SPparent.set_ring()
        self._lc = int(singular.eval('leadcoef(%s)'%self._Svalue.name()))
        if br is not None:
            br.set_ring()
        return self._lc

    def lm_string(self):
        """
        Leading monomial (no coefficient) of ``self`` (type <string>).

        OUTPUT:

        An element of a modular cohomology ring of a finite group
        is given by a stable element in the cohomology ring of a
        suitable subgroup. Expressing the stable element as a
        polynomial, this method returns its leading monomial, as
        a string.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(72,40,prime=3)
            sage: H.make()
            sage: H.4.lm_string()
            'c_2_1*c_2_2^2*a_1_0'

        """
        if self._lmstr is not None:
            return self._lmstr
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self._NF_()
        self._SPparent.set_ring()
        self._lmstr = singular.eval('leadmonom(%s)'%self._Svalue.name())
        if br is not None:
            br.set_ring()
        return self._lmstr

    def lm(self):
        """
        Leading monomial (no coefficient) of ``self``.

        OUTPUT:

        An element of a modular cohomology ring of a finite group
        is given by a stable element in the cohomology ring of a
        suitable subgroup. Expressing the stable element as a
        polynomial, this method returns its leading monomial, as
        an element of the Singular interface.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(72,40,prime=3)
            sage: H.make()
            sage: singular(H.subgroup_cohomology()).set_ring()
            sage: H.4.lm()
            c_2_1*c_2_2^2*a_1_0

        """
        if self._lm is not None:
            try:
                self._lm._check_valid()
                return self._lm
            except:
                pass
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self._NF_()
        self._SPparent.set_ring()
        self._lm = singular('leadmonom(%s)'%self.value().name())
        if br is not None:
            br.set_ring()
        return self._lm


    def lt(self):
        """
        Leading term of the underlying cohomology element.

        OUTPUT:

        An element of a modular cohomology ring of a finite group
        is given by a stable element in the cohomology ring of a
        suitable subgroup. Expressing the stable element as a
        polynomial, this method returns its leading term (i.e.,
        the product of coefficient and monomial), as an element
        in the Singular interface.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: singular(H.subgroup_cohomology()).set_ring()
            sage: (H.6*H.8).lt()
            2*c_2_1^5*c_2_2^5*a_1_0*a_1_1

        """
        if self._lt is not None:
            try:
                self._lt._check_valid()
                return self._lt
            except:
                pass
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self._NF_()
        self._SPparent.set_ring()
        self._lt = singular('lead(%s)'%self.value().name())
        if br is not None:
            br.set_ring()
        return self._lt

    def coef(self, m):
        """
        The coefficient of a monomial.

        INPUT:

        ``m``: A monomial of the underlying cohomology ring of a subgroup (String or Singular

        OUTPUT:

        ``self`` can be considered as a stable element of the
        cohomology of a subgroup. Return the coefficient of
        ``m`` in the normal form of that stable element.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: c = H.2*H.3*H.1
            sage: print(c)
            ((c_8_0)*(c_16_1))*(a_6_0): 30-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_1^3*c_2_2^11*a_1_0*a_1_1-c_2_1^11*c_2_2^3*a_1_0*a_1_1

        We can use a monomial in the Singular interface
        ::

            sage: c.coef(c.lm())
            1

        or given by a string::

            sage: c.coef('c_2_1^11*c_2_2^3*a_1_0*a_1_1')
            -1

        """
        singular = self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        try:
            self._SPparent._check_valid()
        except:
            self._reconstruct_singular_()
        self._SPparent.set_ring()
        if hasattr(m,'name'):
            out = int(self._Svalue.parent().eval("%s/%s"%(self.value().name(),m.name())))
            if br is not None:
                br.set_ring()
            return out
        out = int(self._Svalue.parent().eval("%s/(%s)"%(self.value().name(),m)))
        if br is not None:
            br.set_ring()
        return out

    def coef_list(self, list M):
        """
        Return the list of coefficients.

        INPUT:

        A list of standard monomials (represented by strings) of the
        cohomology ring of the underlying subgroup

        OUTPUT:

        A list of integers, providing the coefficients of the given
        monomials in the stable element (normal form) that corresponds
        to ``self``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(400,206,prime=5)
            sage: H.make()
            sage: c = H.2*H.3*H.1
            sage: print(c)
            ((c_8_0)*(c_16_1))*(a_6_0): 30-Cocycle in H^*(SmallGroup(400,206); GF(5))
            defined by
            c_2_1^3*c_2_2^11*a_1_0*a_1_1-c_2_1^11*c_2_2^3*a_1_0*a_1_1

        We wish to get the list of coefficients of ``c`` for all
        standard monomials of the underlying subgroup::

            sage: M = H.subgroup_cohomology().standard_monomials(30); M
            ['c_2_2^14*a_1_0*a_1_1', 'c_2_1*c_2_2^13*a_1_0*a_1_1', 'c_2_1^2*c_2_2^12*a_1_0*a_1_1', 'c_2_1^3*c_2_2^11*a_1_0*a_1_1', 'c_2_1^4*c_2_2^10*a_1_0*a_1_1', 'c_2_1^5*c_2_2^9*a_1_0*a_1_1', 'c_2_1^6*c_2_2^8*a_1_0*a_1_1', 'c_2_1^7*c_2_2^7*a_1_0*a_1_1', 'c_2_1^8*c_2_2^6*a_1_0*a_1_1', 'c_2_1^9*c_2_2^5*a_1_0*a_1_1', 'c_2_1^10*c_2_2^4*a_1_0*a_1_1', 'c_2_1^11*c_2_2^3*a_1_0*a_1_1', 'c_2_1^12*c_2_2^2*a_1_0*a_1_1', 'c_2_1^13*c_2_2*a_1_0*a_1_1', 'c_2_1^14*a_1_0*a_1_1', 'c_2_2^15', 'c_2_1*c_2_2^14', 'c_2_1^2*c_2_2^13', 'c_2_1^3*c_2_2^12', 'c_2_1^4*c_2_2^11', 'c_2_1^5*c_2_2^10', 'c_2_1^6*c_2_2^9', 'c_2_1^7*c_2_2^8', 'c_2_1^8*c_2_2^7', 'c_2_1^9*c_2_2^6', 'c_2_1^10*c_2_2^5', 'c_2_1^11*c_2_2^4', 'c_2_1^12*c_2_2^3', 'c_2_1^13*c_2_2^2', 'c_2_1^14*c_2_2', 'c_2_1^15']
            sage: c.coef_list(M)
            [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

        """
        cdef dict COEFS = {}
        singular=self._Svalue.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        prefix = self.parent().prefix
        name = self.value().name()
        singular(self.parent()._HP or self.parent()).set_ring()
        if self._NF is None:
            singular.eval('%s=NF(%s,std(0))'%(name,name))
            self._NF = True
        if singular.eval(name+'==0')=='1':
            if br is not None:
                br.set_ring()
            return [0]*len(M)
        singular.eval('int %stmpInt'%prefix)
        OUT = [s.strip().split(';') for s in singular.eval('for(%stmpInt=size(%s);%stmpInt>0;%stmpInt--){print(string(leadmonom(%s[%stmpInt]))+";"+string(leadcoef(%s[%stmpInt]))+",");}'%(prefix,name,prefix,prefix,name,prefix,name,prefix)).split(',')][:-1]
        COEFS = dict(OUT)
        singular.eval('kill %stmpInt'%prefix)
        if br is not None:
            br.set_ring()
        return [int(COEFS.get(s,'0')) for s in M]

################################################
## Yoneda cocomplex
################################################

cdef class YCOCH:
    r"""
    Yoneda cochains.

    This is an auxiliary class to facilitate the computation
    of Massey products.

    A Yoneda `i`-cochain is a collection of maps from the `(i+n)`-the term to the `n`-th term
    of a resolution of a group algebra, `n=0,1,2,...`. There is no compatibility condition
    whatsoever (e.g., the maps are not supposed to commute with the boundary maps of the
    resolution).

    Yoneda cochains form a cocomplex, equipped with the coboundary map `\partial` defined by
    `(\partial \phi^i)_n = \phi_n\circ d_{n+i+1} - (-1)^i d_{n-i+1}\circ \phi_{n+1}^i`
    where

    * `P_\ast` is a resolution
    * `\phi^i` is a Yoneda `i`-cochain, `\phi^i_n: P_{i+n}\to P_n` for `n=0,1,2,...`
    * `\phi_n\\circ d_{n+i+1}` means `d_{n+i+1}` followed by `\phi_n`.

    If `Y_1,Y_2` are two Yoneda cochains, then `Y_1*Y_2` is their composition,
    where we use the convention *first* `Y_2` *then* `Y_1`.

    INPUT:

    * ``R``: a resolution (:class:`~pGroupCohomology.resolution.RESL`)
    * ``n``: the degree of the Yoneda cochain (non-negative integer)
    * ``M_0,M_1,...,M_i,...``: a list of :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrices defining maps from the
      `(n+i)`-th to the `i`-th term of ``R``.
    * ``coboundary=None`` (optional): If it is given, it must be a Yoneda cocycle that is the coboundary of self
    * ``construction=None`` (optional): If it is given, it is a list describing its construction. Either:

        - ``['+',Y1,Y2]`` (self is sum of Yoneda cochains ``Y1, Y2``),
        - ``['-',Y1,Y2]`` (self is ``Y1-Y2``),
        - ``['-',Y]`` (self is ``-Y``),
        - ``['*',Y1,Y2]`` (self is the composition of two Yoneda cochains, ``Y2`` followed by ``Y1``), or
        - ``['D',Y]`` (self is the coboundary of the Yoneda cochain ``Y``).

    NOTE:

    The optional parameters are internally used in :meth:`coboundary`, :meth:`find_cobounding_yoneda_cochains`
    and when adding or composing Yoneda cochains. We however document some of the options here.

    We did not implement comparisons between Yoneda cochains, simply since they morally have infinitely many
    terms, and if two Yoneda cochains have a different construction, it would thus hardly be possible to prove
    equality, in general.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: from pGroupCohomology.cochain import YCOCH
        sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: R = H.resolution()
        sage: R
        Resolution of GF(2)[D8]
        sage: Y = YCOCH(R,1, MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,0,1,0,1,0,1,0],[1,0,1,0,1,0,1,0]]))
        sage: len(Y)
        1

    If higher terms of ``Y`` are required, they are automatically computed. Since no
    construction and no coboundary was provided in the definition of ``Y``, it is lifted
    so that its coboundary is zero.
    ::

        sage: Y[1]
        [1 0 0 0 0 0 0 0]
        [0 1 0 0 0 1 0 0]
        [0 0 0 0 0 0 0 0]
        [1 0 0 1 0 0 0 0]
        [0 0 0 0 1 0 0 0]
        [0 0 0 1 0 1 0 0]
        sage: len(Y)
        2
        sage: Y[0]
        [1 0 1 0 1 0 1 0]
        [1 0 1 0 1 0 1 0]
        sage: Y.coboundary()[0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]

    Next, we provide all terms explicitly, yielding a Yoneda cochain that is not a cocycle::

        sage: tmpM1 = MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,0,1,0,1,0,1,0],[1,0,1,0,1,0,1,0]])
        sage: tmpM2 = MTX(MatrixSpace(GF(2),6,8, implementation=MTX), [[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0]])
        sage: Y = YCOCH(R,1,tmpM1,tmpM2)
        sage: Y
        Yoneda 1-cochain on a resolution of GF(2)[D8]
        sage: Y[0]
        [1 0 1 0 1 0 1 0]
        [1 0 1 0 1 0 1 0]
        sage: Y[1]
        [0 1 1 0 0 1 1 0]
        [1 1 0 0 1 1 0 0]
        [1 0 1 0 1 0 1 0]
        [0 1 1 0 0 1 1 0]
        [1 1 0 0 1 1 0 0]
        [1 0 1 0 1 0 1 0]
        sage: Y.coboundary()[0]
        [0 1 1 1 0 0 0 1]
        [0 1 1 1 1 1 1 0]
        [0 1 1 0 0 0 1 1]
        sage: Y.coboundary()[1]
        [0 0 0 0 1 0 0 0]
        [0 1 0 0 0 0 0 0]
        [0 0 1 0 0 0 0 0]
        [0 0 0 1 0 1 0 0]
        [0 0 0 0 0 0 0 0]
        [0 1 0 0 0 0 0 0]
        [0 0 1 0 0 0 0 0]
        [0 0 0 0 0 1 0 0]

    Of course, the coboundary of the coboundary vanishes::

        sage: Y.coboundary().coboundary()[0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        sage: Y.coboundary().coboundary()[1]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]

    Here is what happens internally when defining the composition of ``Y`` with itself::

        sage: YY = YCOCH(R, 2, construction=['*',Y,Y])
        sage: YY[0]
        [1 0 0 0 0 0 1 1]
        [1 1 1 0 1 1 1 1]
        [0 1 1 0 1 1 0 0]
        sage: YY[1]
        [0 1 0 0 0 0 0 0]
        [0 1 0 0 1 0 0 1]
        [1 1 1 1 1 1 1 1]
        [1 0 0 0 1 0 0 0]
        [0 1 1 1 1 1 0 1]
        [1 0 0 0 1 1 1 0]
        [0 1 0 1 0 0 1 0]
        [1 1 0 1 0 0 1 0]

    However, usually one would define the composition like that::

        sage: YY = Y*Y
        sage: YY[0]
        [1 0 0 0 0 0 1 1]
        [1 1 1 0 1 1 1 1]
        [0 1 1 0 1 1 0 0]
        sage: YY[1]
        [0 1 0 0 0 0 0 0]
        [0 1 0 0 1 0 0 1]
        [1 1 1 1 1 1 1 1]
        [1 0 0 0 1 0 0 0]
        [0 1 1 1 1 1 0 1]
        [1 0 0 0 1 1 1 0]
        [0 1 0 1 0 0 1 0]
        [1 1 0 1 0 0 1 0]

    Internally, the coboundary of ``YY`` would be constructed like that::

        sage: DYY = YCOCH(YY.resolution(), YY.deg()+1, construction=['D',YY])
        sage: DYY[0]
        [0 1 0 0 1 0 0 1]
        [0 1 0 0 0 1 1 0]
        [0 0 1 1 1 1 1 1]
        [0 0 1 1 1 1 0 1]
        sage: DYY[1]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 1 1 0 0 1 1]
        [0 0 1 0 0 0 1 0]
        [0 0 0 1 1 0 1 0]
        [0 1 1 0 0 1 1 0]
        [0 1 0 1 0 0 1 0]
        [0 0 1 1 1 0 1 1]
        [0 1 0 1 0 0 1 0]
        [0 0 1 0 1 0 1 1]

    Of course, for the user it is easier to just do
    ::

        sage: DYY = YY.coboundary()
        sage: DYY[0]
        [0 1 0 0 1 0 0 1]
        [0 1 0 0 0 1 1 0]
        [0 0 1 1 1 1 1 1]
        [0 0 1 1 1 1 0 1]

    """
    def __init__(self, RESL R, int n, *L, coboundary=None, construction = None):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import YCOCH, COCH
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.2
            b_1_0: 1-Cocycle in H^*(D8; GF(2))
            sage: Y = YCOCH(H.resolution(),1,H.resolution().CochainToChainmap(1,H.2.MTX())[2])   # indirect doctest
            sage: Y
            Yoneda 1-cochain on a resolution of GF(2)[D8]
            sage: Y2 = Y*Y
            sage: Y2
            Yoneda 2-cochain on a resolution of GF(2)[D8], defined as a product
            sage: C2 = H.element_as_polynomial(COCH(H,2,'Y2',H.resolution().ChainmapToCochain((2,0,Y2[0]))))
            sage: C2
            b_1_0^2: 2-Cocycle in H^*(D8; GF(2))

        """
        self._deg = n
        self._Data = []
        self._R = R
        if (coboundary is not None) and (construction is not None):
            raise ValueError("A Yoneda cochain must not both depend on a construction and on a construction of its coboundary")
        if not ((coboundary is None) or isinstance(coboundary, YCOCH)):
            raise TypeError("If the coboundary is given, it must be a Yoneda cochain")

        # Take care of the construction
        if (construction is None) or isinstance(construction, list):
            self._Constr = construction # this is ['+',Y1,Y2] (self is sum of Y1,Y2)
                                        # or ['-',Y1,Y2] (difference Y1-Y2)
                                        # or ['-',Y] (negative, -Y)
                                        # or ['*',Y1,Y2] (self is Y2 followed by Y1)
                                        # or ['D',Y] (self is the coboundary of Y)
                                        # or None (lifting of self just relies on lifting its coboundary consistently)
        else:
            raise ValueError("'%s' is an improper construction definition for Yoneda cochains"%construction)

        if len(L)==0 and not construction:
            raise ValueError("The input data do not suffice to construct a Yoneda cochain")
        for M in L: # it is not tested whether the data in L are compatible with the given construction (if there is any)
            self.append(M)

        # Take care of the coboundary.
        if construction: # Since self has an external construction, the coboundary depends on self
            if construction[0]=='D':
                self._Cob = None
            else:
                self._Cob = YCOCH(R, n+1, construction=['D',self])
        else: # the coboundary will be lifted on its own.
            if len(L)==1: # This cochain is self-standing, so, we set the coboundary to None, if it is not given explicitly
                self._Cob = None or coboundary
            else: # Unless the coboundary is given explicitly, we compute a self-standing coboundary from the first two terms of L
                self._Cob = coboundary or YCOCH(R, n+1, R.yoneda_coboundary(L[0],L[1],n,n))
                # it is self-standing, since it has only one input datum

    def __repr__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import YCOCH, COCH
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.2
            b_1_0: 1-Cocycle in H^*(D8; GF(2))
            sage: Y = YCOCH(H.resolution(),1,H.resolution().CochainToChainmap(1,H.2.MTX())[2])
            sage: Y      # indirect doctest
            Yoneda 1-cochain on a resolution of GF(2)[D8]
            sage: Y2 = Y*Y
            sage: Y2
            Yoneda 2-cochain on a resolution of GF(2)[D8], defined as a product

        """
        out = "Yoneda %d-cochain on a resolution of %s"%(self._deg,self._R.G_ALG())
        if not self._Constr:
            return out
        if self._Constr[0] == 'D':
            return out+", defined as a coboundary"
        if self._Constr[0] == '+':
            return out+", defined as a sum"
        if self._Constr[0] == '-':
            if len(self._Constr)==2:
                return out+", defined by negation"
            return out+", defined as a difference"
        if self._Constr[0] == '*':
            return out+", defined as a product"
        return out+", definition unknown"

    def __getitem__(self, i):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import YCOCH
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: tmpM1 = MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,0,1,0,1,0,1,0],[1,0,1,0,1,0,1,0]])
            sage: tmpM2 = MTX(MatrixSpace(GF(2),6,8, implementation=MTX), [[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0]])
            sage: Y = YCOCH(H.resolution(), 1, tmpM1, tmpM2)
            sage: print(Y[0])   # indirect doctest
            [1 0 1 0 1 0 1 0]
            [1 0 1 0 1 0 1 0]
            sage: print(Y[1])
            [0 1 1 0 0 1 1 0]
            [1 1 0 0 1 1 0 0]
            [1 0 1 0 1 0 1 0]
            [0 1 1 0 0 1 1 0]
            [1 1 0 0 1 1 0 0]
            [1 0 1 0 1 0 1 0]
            sage: print(Y[2])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 1 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            [0 1 0 1 0 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 1 0 1 0 0 0]
            [1 0 0 1 0 0 0 0]
            [1 0 1 0 0 0 0 0]

        """
        while len(self._Data)<=i:
            self.lift()
        return self._Data[i]

    def deg(self):
        """
        Return the degree of ``self``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import YCOCH
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: Y = YCOCH(H.resolution(),2,H.resolution().CochainToChainmap(2,H.1.MTX())[2])
            sage: Y.deg()
            2

        """
        return self._deg

    def resolution(self):
        """
        Return the resolution over which ``self`` is defined.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import YCOCH
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: Y = YCOCH(H.resolution(),2,H.resolution().CochainToChainmap(2,H.1.MTX())[2])
            sage: print(Y.resolution())
            Resolution:
            0 <- GF(2) <- GF(2)[D8] <- rank 2 <- rank 3 <- rank 4

        """
        return self._R

    def __len__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import YCOCH
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: Y = YCOCH(H.resolution(),2,H.resolution().CochainToChainmap(2,H.1.MTX())[2])
            sage: len(Y)   # indirect doctest
            1
            sage: Y.lift()
            sage: len(Y)
            2

        """
        return len(self._Data)

    def append(self, MTX M):
        """
        append further terms to ``self``.

        INPUT:

        ``M``: :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix defining the next term of self

        NOTE:

        Actually an immutable copy of ``M`` is appended.

        **Warning:** It is strongly recommended to not use this method
        manually, as it is not checked whether the appended term fits
        to the construction of the Yoneda cochain.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: from pGroupCohomology.cochain import YCOCH
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: tmpM1 = MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,0,1,0,1,0,1,0],[1,0,1,0,1,0,1,0]])
            sage: tmpM2 = MTX(MatrixSpace(GF(2),6,8, implementation=MTX), [[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0]])
            sage: Y = YCOCH(H.resolution(), 1, tmpM1, tmpM2)
            sage: M = MTX(MatrixSpace(GF(2),12,8, implementation=MTX), [[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0]])
            sage: Y.append(M)
            sage: Y[2]==M
            True

        """
        if not isinstance(M,MTX):
            raise TypeError("{} expected".format(MTX))
        while self._R.deg()<len(self._Data):
            self._R.nextDiff()
        if M.Data.Field != self._R.coef():
            raise ValueError("Matrix must be defined over GF(%d)"%(self._R.coef()))
        if M.ncols() != self._R.grouporder():
            raise ValueError("Matrix must have %d columns"%(self._R.grouporder()))
        if M.nrows() != self._R.rank(self._deg+len(self._Data)) * self._R.rank(len(self._Data)):
            raise ValueError("First matrix must have %d rows"%(self._R.rank(self._deg+len(self._Data)) * self._R.rank(len(self._Data))))
        M = copy(M)
        M.set_immutable()
        self._Data.append(copy(M))


    ########################
    ##
    ## The Yoneda coboundary map
    ##
    ########################

    def coboundary(YCOCH self):
        r"""
        Return the Yoneda coboundary of ``self``.

        THEORY:

        If `d_\ast: P_\ast \to P_{\ast-1}` denotes the boundary maps of `P_\ast` and `\phi^i` is a Yoneda `i`-cochain
        with `\phi^i_n: P_{i+n}\to P_n` then
        `(\partial \phi^i)_n = \phi_n\circ d_{n+i+1} - (-1)^i d_{n-i+1}\circ \phi_{n+1}^i`, which is a Yoneda `(i+1)`-cocycle.

        NOTE:

        Coboundary and lifting commute, see :meth:`lift`.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: from pGroupCohomology.cochain import YCOCH
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: tmpM1 = MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,0,1,0,1,0,1,0],[1,0,1,0,1,0,1,0]])
            sage: tmpM2 = MTX(MatrixSpace(GF(2),6,8, implementation=MTX), [[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0]])
            sage: Y = YCOCH(H.resolution(),1,tmpM1, tmpM2)
            sage: YC = Y.coboundary()
            sage: YC
            Yoneda 2-cochain on a resolution of GF(2)[D8]
            sage: print(YC[0])
            [0 1 1 1 0 0 0 1]
            [0 1 1 1 1 1 1 0]
            [0 1 1 0 0 0 1 1]
            sage: print(YC[1])
            [0 0 0 0 1 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 1 0 1 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 1 0 0]
            sage: print(YC[2])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 1 0 0 0 0 0]

        The coboundary of the coboundary vanishes::

            sage: YCC = YC.coboundary()
            sage: print(YCC[0])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: print(YCC[1])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]

        """
        if self._Cob is None:
            return YCOCH(self._R,self._deg+1,construction=['D',self])
        return self._Cob

    def find_cobounding_yoneda_cochains (YCOCH self, all=True):
        """
        Construct Yoneda cochains whose coboundary is ``self``.

        ASSUMPTION:

        ``self`` is a Yoneda cocycle. Note that this assumption is not
        verified.

        OUTPUT:

        A list of Yoneda cochains whose coboundary is ``self``.

        If the optional parameter ``all`` is ``True`` (which is default)
        then a list of Yoneda cochains is returned that are pairwise not
        cohomologous (i.e., the pairwise difference is not a coboundary).
        Otherwise, the list will only contain at most one Yoneda cochain.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.gens()
            [1,
             c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            sage: H.rels()
            ['b_1_0*b_1_1']
            sage: Y1 = H.2.yoneda_cocycle()
            sage: Y2 = H.3.yoneda_cocycle()
            sage: Y12 = Y1*Y2
            sage: Y12.find_cobounding_yoneda_cochains()
            [Yoneda 1-cochain on a resolution of GF(2)[D8],
             Yoneda 1-cochain on a resolution of GF(2)[D8],
             Yoneda 1-cochain on a resolution of GF(2)[D8],
             Yoneda 1-cochain on a resolution of GF(2)[D8]]
            sage: C1, C2, C3, C4 = _

        Indeed, the pairwise differences are no coboundaries::

            sage: print(C1[0])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: print(C2[0])
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: print(C3[0])
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            sage: print(C4[0])
            [1 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]

        But the coboundary of ``C1,...,C4`` is ``Y12``::

            sage: print(C1.coboundary()[1])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 1 0 0 0 0]
            sage: Y12[1] == C1.coboundary()[1]
            True
            sage: Y12[0] == C1.coboundary()[0]
            True
            sage: Y12[1] == C1.coboundary()[1]
            True
            sage: Y12[2] == C1.coboundary()[2]
            True
            sage: Y12[0] == C2.coboundary()[0]
            True
            sage: Y12[1] == C2.coboundary()[1]
            True
            sage: Y12[2] == C2.coboundary()[2]
            True
            sage: Y12[0] == C3.coboundary()[0]
            True
            sage: Y12[1] == C3.coboundary()[1]
            True
            sage: Y12[2] == C3.coboundary()[2]
            True
            sage: Y12[0] == C4.coboundary()[0]
            True
            sage: Y12[1] == C4.coboundary()[1]
            True
            sage: Y12[2] == C4.coboundary()[2]
            True

        """
        cdef RESL R = self._R
        cdef int n = self.deg()
        P, K, D = R._get_yoneda_liftdata(n)  # if possible, data are reloaded
        while (n > R.deg()):
            R.nextDiff()
        cdef int RK = R.Data.projrank[n]
        cdef int Rk = R.Data.projrank[n-1]
        cdef int rk = R.Data.projrank[1]
        cdef long fl  = R.G_Alg.Data.p
        cdef long nt  = R.G_Alg.Data.nontips
        cdef MTX X = self[0]
        if X._nrows != RK or X._ncols != nt or X.Data.Field != fl:
            raise RuntimeError("Theoretical error, please inform the author")
        cdef MTX Y = new_mtx(MatAlloc(fl, Rk, nt), X)
        cdef MTX Z = new_mtx(MatAlloc(fl, RK*rk, nt), X)
        cdef int i, m
        coho_logger.info( "Try to find a cobounding Yoneda cochain for %r", self._R, self)
        for i in P: # these are the pivots of the "autolift" data
            m = X[i//nt, i%nt]
            if m:
                if m!=1:
                    Y += (D[i][0]*m)
                    Z += (D[i][1]*m)
                else:
                    Y += D[i][0]
                    Z += D[i][1]

        coho_logger.info("> Verifying the result", self._R)
        if X != R.yoneda_coboundary(Y,Z, n-1,n-1):
            return []
        Y.set_immutable()
        Z.set_immutable()
        cdef YCOCH OUT = YCOCH(R,n-1,Y,Z, coboundary=self)
        if not all:
            return [OUT]
        cdef list L = [OUT]
        cdef list Lnew
        cdef set Known = set([])
        cdef tuple FP
        cdef int k
        cdef MTX Yall,Zall
        cdef YCOCH YC
        coho_logger.info( "Constructing all relevant cobounding Yoneda cochains", self._R)
        for Y0,Z0 in K: # these define Yoneda cocycles, hence, we can add them to our special solution Y,Z
            Lnew = []
            for YC in L:
                Yall = YC[0]
                Zall = YC[1]
                for i from 1<= i < fl: # ... up to fl-1 times.
                    Yall += Y0
                    Zall += Z0
                    FP = (tuple([Yall[k,0] for k in range(Rk)]), tuple([Zall[k,0] for k in range(RK*rk)]))
                    if not (FP in Known):
                        Lnew.append(YCOCH(R,n-1,Yall, Zall, coboundary=self))
                        Known.add(FP)
            L.extend(Lnew)
        return L


    ################
    ## Arithmetic
    ##
    ##  The return values remember how they were constructed,
    ##  which is needed when lifting
    ################

    def __neg__(YCOCH self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(9,2)
            sage: H.make()
            sage: X = H.1.yoneda_cocycle()
            sage: Y = -X # indirect doctest
            sage: Y[0] == - (X[0])
            True
            sage: Y[1] == - (X[1])
            True
            sage: Y[2] == - (X[2])
            True
            sage: Y[3] == - (X[3])
            True
            sage: print(Y[2])
            [2 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [2 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [2 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            sage: print(Y[1])
            [2 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [2 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]

        """
        return YCOCH(self._R, self._deg, construction=['-',self])

    def __sub__(YCOCH self, YCOCH other):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(9,2)
            sage: H.make()
            sage: X = H.3.yoneda_cocycle()
            sage: Y = H.4.yoneda_cocycle()
            sage: D = Y - X # indirect doctest
            sage: D[0] == Y[0]-X[0]
            True
            sage: D[1] == Y[1]-X[1]
            True
            sage: D[2] == Y[2]-X[2]
            True
            sage: print(D[1])
            [1 0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0 0]
            [0 1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 2 0 0 0 0 0 0]

        """
        if not (self._R is other._R):
            raise ValueError("Both summands must be defined over the same resolution")
        if self._deg != other._deg:
            raise ValueError("Both summands must have the same degree")
        return YCOCH(self._R, self._deg, construction=['-',self,other])

    def __add__(YCOCH self, YCOCH other):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(9,2)
            sage: H.make()
            sage: X = H.3.yoneda_cocycle()
            sage: Y = H.4.yoneda_cocycle()
            sage: D = X + Y # indirect doctest
            sage: D[0] == Y[0]+X[0]
            True
            sage: D[1] == Y[1]+X[1]
            True
            sage: D[2] == Y[2]+X[2]
            True
            sage: print(D[1])
            [1 0 0 0 0 0 0 0 0]
            [2 0 0 0 0 0 0 0 0]
            [0 2 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            [0 0 2 0 0 0 0 0 0]

        """
        if not (self._R is other._R):
            raise ValueError("Both summands must be defined over the same resolution")
        if self._deg != other._deg:
            raise ValueError("Both summands must have the same degree")
        return YCOCH(self._R, self._deg, construction=['+',self,other])

    def __mul__(YCOCH self, other):
        """
        Compose two Yoneda cochains, first ``self`` then other.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import YCOCH, COCH
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.2
            b_1_0: 1-Cocycle in H^*(D8; GF(2))
            sage: Y = H.2.yoneda_cocycle()
            sage: Y
            Yoneda 1-cochain on a resolution of GF(2)[D8]
            sage: Y2 = Y*Y   # indirect doctest
            sage: Y2
            Yoneda 2-cochain on a resolution of GF(2)[D8], defined as a product
            sage: print(Y2[0])
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]

        """
        if isinstance(other, YCOCH):
            if self._R is other.resolution():
                d = other.deg()
            else:
                raise ValueError("The two factors must be defined over the same resolution")
        else:
            d = 0
        return YCOCH(self._R, d+self._deg, construction=['*',self,other])

    def lift(self, check=False):
        """
        Compute the next term of ``self``.

        THEORY:

        If the coboundary of self vanishes, then the next term is chosen
        so that the coboundary still vanishes. In the general case, since
        the coboundary of a Yoneda cochain is a cocycle, we can lift the
        coboundary according to the previously stated property. Then, the
        next term is chosen such that the lift and the coboundary map
        commute.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: from pGroupCohomology.cochain import YCOCH
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: tmpM1 = MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,0,1,0,1,0,1,0],[1,0,1,0,1,0,1,0]])
            sage: tmpM2 = MTX(MatrixSpace(GF(2),6,8, implementation=MTX), [[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0],[0,1,1,0,0,1,1,0],[1,1,0,0,1,1,0,0],[1,0,1,0,1,0,1,0]])
            sage: Y = YCOCH(H.resolution(), 1, tmpM1, tmpM2)
            sage: YC = Y.coboundary()
            sage: len(YC)
            1

        We compute the third term of ``YC`` and verify that this is the same as computing the fourth term of ``Y`` and
        then taking the third term of the coboundary of the extended version of ``Y``. Note that when asking for a term
        that has not been computed yet (e.g., ``YC[2]``) then lifting is done automatically.
        ::

            sage: print(YC[2])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 1 0 0 0 0 0]
            sage: Y.lift()
            sage: Y.lift()
            sage: len(Y)
            4

        Now, as four terms of ``Y`` are known, the third term of its coboundary is known even without lifting.
        But it coincides with the third term obtained by lifting ``YC``::

            sage: YC[2] == Y.coboundary()[2]
            True

        """
        cdef RESL R = self._R
        cdef int RK
        cdef int rk
        cdef int i,n,N
        cdef list L
        cdef MTX ToBeLifted
        while R.deg() < len(self)+self.deg():
            R.nextDiff()

        # First case: self is coboundary of something that is defined externally
        if self._Constr and self._Constr[0]=='D':
            Y = self._Constr[1]
            n = len(self)
            N = n + Y.deg()
            # in the following expression, Y is automatically lifted appropriately.
            if Y.deg()%2:
                self.append(self._R.composeChainMaps(self._R[N+1], Y[n], N+1,N,n) + self._R.composeChainMaps(Y[n+1], self._R[n+1], N+1,n+1,n))
            else:
                self.append(self._R.composeChainMaps(self._R[N+1], Y[n], N+1,N,n) - self._R.composeChainMaps(Y[n+1], self._R[n+1], N+1,n+1,n))
            return

        # Second case: it is a sum / difference / negation
        if self._Constr and self._Constr[0]=='+':
            self._Data.append(self._Constr[1][len(self)] + self._Constr[2][len(self)])
            return
        if self._Constr and self._Constr[0]=='-':
            if len(self._Constr)==2:
                self._Data.append(-(self._Constr[1][len(self)]))
            else:
                self._Data.append(self._Constr[1][len(self)] - (self._Constr[2][len(self)]))
            return

        # Third case: it is a product / composition
        if self._Constr and self._Constr[0]=='*':
            if isinstance(self._Constr[2],YCOCH):
                self._Data.append(self._R.composeChainMaps(self._Constr[2][len(self)+self._Constr[1].deg()], self._Constr[1][len(self)], len(self)+self._Constr[2].deg()+self._Constr[1].deg(), len(self)+self._Constr[1].deg(), len(self)))
            else:
                self._Data.append(self._Constr[1][len(self)]*self._Constr[2])
            return

        # Final case: Lifting of self is defined by lifting its coboundary (which might be defined externally!)
        n = len(self)-1 # this is where the last known part of self points to.
        N = n + self._deg + 1 # The lift shall point from N to n+1
        # The lift is done by taking into account term n of the coboundary, which points from N to n
        # and which is assumed to be zero if it is None
        if self._deg%2:
            if self._Cob is None:
                ToBeLifted = -R.composeChainMaps(R[N],self[n],N,N-1,n)
            else:
                ToBeLifted = self._Cob[n] - R.composeChainMaps(R[N],self[n],N,N-1,n)
        else:
            if self._Cob is None:
                ToBeLifted = R.composeChainMaps(R[N],self[n],N,N-1,n)
            else:
                ToBeLifted = R.composeChainMaps(R[N],self[n],N,N-1,n) - self._Cob[n]
        RK = R.Data.projrank[N]
        rk = R.Data.projrank[n]
        n = n+1
        L = [R.find_bounding_chain(n, ToBeLifted.get_slice(i*rk, (i+1)*rk), check=check) for i in range(RK)]
        cdef MTX OUT1 = L[0]
        cdef MTX tmp
        fl = OUT1.Data.Field
        OUT1 = new_mtx(MatAlloc(fl, sum([M.nrows() for M in L]), OUT1._ncols), OUT1)
        cdef Py_ssize_t row = 0
        FfSetField(fl)
        FfSetNoc(OUT1.Data.Noc)
        for tmp in L:
            memcpy(FfGetPtr(OUT1.Data.Data, row), tmp.Data.Data, FfCurrentRowSize*tmp.Data.Nor)
            row += tmp.Data.Nor
        self._Data.append(OUT1)


#####################################################################
#####################################################################
## Chainmap extension type (and homset)
#####################################################################
#####################################################################

class CohomologyHomset(RingHomset_generic):
    """
    Set of Homomorphisms between Modular Cohomology Rings of Finite `p`-Groups.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace

    We consider the dihedral group of order 8 and will study the restriction
    maps to representatives for all conjugacy classes of non-trivial subgroups.
    ::

        sage: G = libgap.DihedralGroup(8)
        sage: H = CohomologyRing(G,GroupName = 'D8', from_scratch=True)
        sage: H.make()
        sage: SubG = [X.RepresentativeSmallest() for X in G.ConjugacyClassesSubgroups()]
        sage: SubG = [X.MinimalGeneratingSet().Group() for X in SubG if X.Order()>1]
        sage: for i in range(len(SubG)):
        ....:     SubG[i].SetName('U%d'%(i+1))
        sage: HSubG = [CohomologyRing(X, from_scratch=True) for X in SubG]
        sage: for X in HSubG:
        ....:     X.make()
        sage: IncG = [X.GroupHomomorphismByImages(G,X.GeneratorsOfGroup(),X.GeneratorsOfGroup()) for X in SubG]
        sage: for i in range(len(IncG)):
        ....:     IncG[i].SetName('i_%d'%(i+1))
        sage: ResG = [H.hom(IncG[i], HSubG[i]) for i in range(len(HSubG))]   # indirect doctest

    Now, we can apply the maps to elements of ``H``::

        sage: ResG[2](H.2+H.3)
        i_3^*(b_1_0+b_1_1): 1-Cocycle in H^*(SmallGroup(2,1); GF(2))

    The image of an element of the base field is mapped to itself, while
    cochains of degree 0 are properly mapped::

        sage: ResG[2](H.0)
        1
        sage: ResG[2](H(1))
        i_3^*(1): 0-Cocycle in H^*(SmallGroup(2,1); GF(2))

    Finally, we show how the images of non-scalar generators of ``H`` under
    the various restrictions maps can be expressed as elements of the cohomology
    rings of the subgroups::

        sage: for f in ResG:
        ....:     print([f.codomain().element_as_polynomial(f(X)).name() for X in H.gens()[1:]])
        ['c_1_0^2', '0', '0']
        ['0', 'c_1_0', '0']
        ['c_1_0^2', 'c_1_0', 'c_1_0']
        ['c_1_1^2+c_1_0*c_1_1', 'c_1_0', '0']
        ['c_2_0', '0', 'c_1_0']
        ['c_1_1^2+c_1_0*c_1_1+c_1_0^2', 'c_1_1', 'c_1_1']
        ['c_2_2', 'b_1_0', 'b_1_1']

    """
    # it inherits _domain and _codomain
    # -- option category is not supported yet
    def __init__(self, X, Y, category=None):
        """
        INPUT:

        - ``X``, ``Y`` -- two cohomology rings (:class:`~pGroupCohomology.cohomology.COHO`
          or :class:`~pGroupCohomology.modular_cohomology.MODCOHO`).

        TEST::

            sage: from pGroupCohomology.cochain import CohomologyHomset
            sage: from pGroupCohomology import CohomologyRing
            sage: H = CohomologyRing(8,3)
            sage: CohomologyHomset(H,H)      # indirect doctest
            Set of Homomorphisms from H^*(D8; GF(2)) to H^*(D8; GF(2))

        """
        from pGroupCohomology.cohomology import COHO
        if not isinstance(X,COHO):
            raise TypeError("Domain must be a cohomology ring")
        if not isinstance(Y,COHO):
            raise TypeError("Codomain must be a cohomology ring")
        if (X.Resl.coef()<>Y.Resl.coef()):
            raise TypeError("Domain and Codomain must be defined over the same base field")
        self._cache = {}  # caches different maps between the same rings
        self._H0Map = new_mtx(MatAlloc(X.Resl.coef(), 1, X.Resl.G_ALG().order()), None)
        self._H0Map[0,0] = 1
        self._H0Map.set_immutable()
        RingHomset_generic.__init__(self, X, Y, category=category)

    def __call__(self, GMap, H0Map=None, d=0):
        """
        INPUT:

        - ``GMap`` (see below)
        - ``H0Map`` - usually ``None`` (default), but can be a
          :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix providing a map from
          term ``-d`` of the resolution of the codomain to term zero of
          the resolution of the domain (d<0), respectively from term
          zero of the resolution of the codomain to term ``d`` of the
          resolution of the domain. We do not further document nor support
          this usage, so, it is very likely that it won't work.
        - ``d`` - an integer, the degree of the chain map.
          Must be zero if ``H0Map`` is ``None``.

        Use cases:

        1. ``GMap`` is a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix defining a
           homeomorphism of group algebras.
        2. ``GMap`` is a group homomorphism, defined in the libgap interface
        If ``H0Map`` is ``None``, we replace it by the matrix given by ``[[1,0,0,...]]``

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: HS = H2.Hom(H1)
            sage: HS(phi_star.G_map()) == HS(phi) == phi_star   # indirect doctest
            True

        """
        Name = None
        # Slight complication: We have to switch to the Sylow p-group, if
        # we have a non prime power group:
        Src = self._codomain._HSyl or self._codomain  # source of chain map, not of induced map
        Tgt = self._domain._HSyl or self._domain
        if H0Map is not None:
            if not isinstance(H0Map,MTX):
                raise TypeError("The second argument, if provided, must be an MTX matrix")
            if H0Map.is_mutable():
                H0Map.set_immutable()
                H0Mapmutable = True
            else:
                H0Mapmutable = False
        else:
            H0Map = self._H0Map
            H0Mapmutable = False

        if isinstance(GMap, MTX):
            if GMap.is_mutable():
                GMap.set_immutable()
                GMapmutable = True
            else:
                GMapmutable = False
        else: # GMap should be a group homomorphism in gap or
              # (not yet implemented) list of elements of the group of self._domain,
              # defining the images of the generators of the group of self._codomain
            if hasattr(GMap,'parent'):
                GAP = GMap.parent()
                _gap_reset_random_seed()
                if GMap.HasName():
                    Name = GMap.Name().sage()
                if not (GAP == Src.group().parent() == Tgt.group().parent()):
                    raise ValueError("The second argument and the groups of domain and codomain must be defined in the same libGAP session")
                if GMap.IsGroupHomomorphism():
                    GSrc = GMap.Source()
                    GTgt = GMap.Range()
                    for X in GSrc.GeneratorsOfGroup():
                        if GMap.Image(X) not in GTgt:
                            raise ValueError("The images of the given homomorphism are not contained in its assumed range")
                    try:
                        GSrceqGTgt = (GSrc==GTgt)
                    except:
                        GSrceqGTgt = False
                    if GSrceqGTgt and not GSrc.GeneratorsOfGroup()==GTgt.GeneratorsOfGroup():
                        # We insist that the generators coincide.
                        GTgt = GSrc
#~                         GAP.eval('%s:=GroupHomomorphismByImages(%s,%s,GeneratorsOfGroup(%s),List([1..Length(GeneratorsOfGroup(%s))],x->Image(%s,GeneratorsOfGroup(%s)[x])))'%(GMap.name(),GSrc.name(),GTgt.name(),GSrc.name(),GSrc.name(),GMap.name(),GSrc.name()))
                        GSrcGen = GSrc.GeneratorsOfGroup()
                        GMap = GSrc.GroupHomomorphismByImages(GTgt, GSrcGen, [ GMap.Image(g) for g in GSrcGen ])
                    # Replace GMap by a map starting at self._codomain.group() and ending at
                    # self._domain.group()
#~                     try:
                    GSrcAdmH = self._codomain.group().canonicalIsomorphism(GSrc)
#~                     except:
#~                         _gap_reset_random_seed()
#~                         GSrcAdmH = self._codomain.group().canonicalIsomorphism(GSrc)
                    GTgtAdmH = GTgt.canonicalIsomorphism(self._domain.group())
                    if GSrcAdmH == GAP.eval('fail'):
                        raise ValueError("The source of the group homomorphism doesn't match the range of the induced homomorphism, %s"%repr(self._codomain.group()))
                    if GTgtAdmH == GAP.eval('fail'):
                        raise ValueError("The range of the group homomorphism doesn't match the source of the induced homomorphism, %s"%repr(self._domain.group()))
#~                     GMap = GAP('GroupHomomorphismByImages(%s,%s,GeneratorsOfGroup(%s),List([1..Length(GeneratorsOfGroup(%s))],x->Image(%s,Image(%s,Image(%s,GeneratorsOfGroup(%s)[x])))))'%(self._codomain.group().name(),self._domain.group().name(),self._codomain.group().name(),self._codomain.group().name(),GTgtAdmH.name(),GMap.name(),GSrcAdmH.name(),self._codomain.group().name()))
                    CDGen = self._codomain.group().GeneratorsOfGroup()
                    GMap = self._codomain.group().GroupHomomorphismByImages(self._domain.group(), CDGen,
                                                                            [ GTgtAdmH.Image(GMap.Image(GSrcAdmH.Image(g))) for g in CDGen ])
                    # We need restriction to Src.group(), hence, if self._codomain is not Src
                    # then we map Src.group() to self._codomain._SylowGp, which is a subgroup of
                    # self._codomain.group()
                    if Src is not self._codomain:
                        Src2Sylow = Src.group().canonicalIsomorphism(self._codomain._SylowGp)
                        if Src2Sylow == GAP.eval('fail'):
                            raise RuntimeError("Theoretical error: No canonical isomorphism from %s to %s found"%(Src.group(),self._codomain._SylowGp))
#~                         GAP.eval('%s:=GroupHomomorphismByImages(%s, %s, GeneratorsOfGroup(%s), List([1..Length(GeneratorsOfGroup(%s))], x -> Image(%s,Image(%s,GeneratorsOfGroup(%s)[x]))))'%(GMap.name(),Src.group().name(), self._domain.group().name(), Src.group().name(), Src.group().name(), GMap.name(), Src2Sylow.name(), Src.group().name()))
                        SrcGrpGen = Src.group().GeneratorsOfGroup()
                        GMap = Src.group().GroupHomomorphismByImages(self._domain.group(), SrcGrpGen,
                                                                     [ GMap.Image(Src2Sylow.Image(g)) for g in SrcGrpGen ])

                    # Now the Source is fine. About the Range:
                    # We are already in self._domain.group().
                    # Finally, if necessary, conjugate the image of GMap (which starts at
                    # the p-group Src.group()) into the preferred Sylow subgroup
                    # of self._domain.group(), which currently is the range of GMap.
                    if self._domain is not Tgt:
                        # GMap starts at Src.group(). So, its image is a p-group
#~                         ConjMap = GAP('conjugateIntoSylow(%s,Image(%s),%s)'%(self._domain.group().name(), GMap.name(), (self._domain._SylowGp if self._domain._SylowGp is not None else self._domain.group()).name()))
                        ConjMap = self._domain.group().conjugateIntoSylow(GMap.Image(), self._domain._SylowGp if self._domain._SylowGp is not None else self._domain.group())
                        if ConjMap == GAP.eval('fail'):
                            raise RuntimeError("Theoretical error: Unable to conjugate a p-subgroup into a given Sylow p-subgroup")

                        # We compose GMap with ConjMap and obtain a map from Src.group() to self._domain._SylowGp and forward to Tgt.group()
                        Sylow2Tgt = (self._domain._SylowGp if self._domain._SylowGp is not None else self._domain.group()).canonicalIsomorphism(Tgt._HSyl.group() if Tgt._HSyl is not None else Tgt.group())
                        if Sylow2Tgt == GAP.eval('fail'):
                            raise RuntimeError("Theoretical Error: No canonical isomorphism from %s to %s found"%(self._domain._SylowGp, Tgt.group()))
#~                         GAP.eval('%s:=GroupHomomorphismByImages(%s, %s, GeneratorsOfGroup(%s),
#~                                     List([1..Length(GeneratorsOfGroup(%s))], x -> Image(%s,Image(%s, Image(%s, GeneratorsOfGroup(%s)[x])))))'%
#~                                     (GMap.name(), Src.group().name(), Tgt.group().name(), Src.group().name(), Src.group().name(), Sylow2Tgt.name(),
#~                                         ConjMap.name(), GMap.name(), Src.group().name()))
                        SrcGen = Src.group().GeneratorsOfGroup()
                        GMap = Src.group().GroupHomomorphismByImages( Tgt.group(), SrcGen,
                                                    [ Sylow2Tgt.Image(ConjMap.Image(GMap.Image(g))) for g in SrcGen ])
                else: # not a homomorphism
                    raise NotImplementedError("We expected a group homomorphism")

                # Hence, we can produce a temporary file providing the MTX matrix of the induced group algebra map.
                GStem = os.path.join(Tgt.gps_folder,Tgt.GStem)
                HStem = os.path.join(Src.gps_folder,Src.GStem)
                IStem = tmp_filename()
                while True:
#~                     command = 'makeInducedHomomorphismData("%s","%s","%s", %s, %d)'%(GStem,HStem,IStem,GMap.name(),Tgt.Resl.G_ALG().order())
                    GAP.function_factory('makeInducedHomomorphismData')(GStem, HStem, IStem, GMap, Tgt.Resl.G_ALG().order())
                    # The following warning occurs when computing the mod-3 cohomology of SmallGroup(44100,1)
                    if not os.path.exists(IStem+'.ima'):
                        print("WARNING")
                        print("Couldn't create data for induced homomorphism.")
                        print("If this persists, hit <Ctrl-c> and inform the author")
                    else:
                        break
                GMap = MTX.from_filename(IStem+'.ima')
                os.unlink(IStem+'.ima')
                os.unlink(IStem+'.irg')
                GMap.set_immutable()
                GMapmutable = False
            else:
                raise TypeError("First argument must be an MTX matrix or some data defined in Gap")
        try:
            OUT = self._cache[GMap,H0Map,d]
        except KeyError:
            OUT = ChMap(self, GMap, H0Map, d)
            self._cache[GMap,H0Map,d] = OUT
        if GMapmutable:
            if GMap.is_immutable():
                GMap = GMap.__copy__()
        if H0Mapmutable:
            if H0Map.is_immutable():
                H0Map = H0Map.__copy__()
        if Name is not None:
            OUT.set_name(Name+'^*')
        return OUT

    def _repr_(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.restriction_maps()[2][1].parent()   # indirect doctest
            Set of Homomorphisms from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))

        """
        return "Set of Homomorphisms from %s to %s"%(self._domain.__repr__(), self._codomain.__repr__())

class ChMap_unpickle_class:
    """
    Unpickling an instance of :class:`~pGroupCohomology.cochain.ChMap`, representing an induced homomorphism.

    EXAMPLES:

    Usually, an induced homomorphism is created by defining two groups and
    a homomorphism between them, computing the cohomology rings of the groups,
    and then invoking the :meth:`~pGroupCohomology.cohomology.COHO.hom` method
    of cohomology rings.

    We first create the cohomology rings for two different presentations of the
    dihedral group of order 8.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: G1 = libgap.SmallGroup(8,3)
        sage: H1 = CohomologyRing(8,3, from_scratch=True)
        sage: H1.make()
        sage: G2 = libgap.DihedralGroup(8)
        sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
        sage: H2.make()
        sage: phi = G1.IsomorphismGroups(G2)

    After ensuring that ``phi`` is printed nicely, we obtain the induced map and see that it is cached::

        sage: phi.SetName('phi')
        sage: phi_star = H2.hom(phi,H1)
        sage: phi_star is loads(dumps(phi_star))   # indirect doctest
        True


    """
    def __init__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi_star = H2.hom(phi,H1)
            sage: from pGroupCohomology.cochain import ChMap_unpickle_class
            sage: CU = ChMap_unpickle_class()   # indirect doctest
            sage: phi_star2 = CU(H2,H1,phi_star.G_map(),[phi_star[0]],0)
            sage: phi_star2 is phi_star
            True

        """
        self.__safe_for_unpickling__ = True

    def __call__(self, Src,Tgt,GMap,Data,Deg, name = None):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi_star = H2.hom(phi,H1)
            sage: from pGroupCohomology.cochain import ChMap_unpickle_class
            sage: CU = ChMap_unpickle_class()
            sage: phi_star2 = CU(H2,H1,phi_star.G_map(),[phi_star[0]],0)   # indirect doctest
            sage: phi_star2 is phi_star
            True

        """
        cdef ChMap OUT
        OUT = Src.hom(GMap,Tgt,Data[0], Deg)
        OUT._name = name
        OUT.Data = Data
        return OUT

chmap_unpickle=ChMap_unpickle_class()

cdef class ChMap(RingHomomorphism):
    """
    Extension class representing induced homomorphisms of cohomology rings.

    EXAMPLES:

    Usually, an induced homomorphism is created by defining two groups and
    a homomorphism between them, computing the cohomology rings of the groups,
    and then invoking the :meth:`~pGroupCohomology.cohomology.COHO.hom`` method
    of cohomology rings.

    We first create the cohomology rings for two different presentations of the
    dihedral group of order 8.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: G1 = libgap.SmallGroup(8,3)
        sage: H1 = CohomologyRing(8,3, from_scratch=True)
        sage: H1.make()
        sage: G2 = libgap.DihedralGroup(8)
        sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
        sage: H2.make()

    In order to obtain reproducible doc tests, we switch to permutation
    groups that are, from the perspective of our programs, equivalent to
    ``G1`` and ``G2``, and provide an explicit group isomorphism::

        sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
        sage: H1.group()==phi.Source()
        True
        sage: H2.group().canonicalIsomorphism(phi.Range())
        [ (1,2)(3,8)(4,6)(5,7), (1,3,4,7)(2,5,6,8) ] -> [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ]
        sage: phi.IsInjective()
        true
        sage: phi.IsSurjective()
        true

    After ensuring that ``phi`` is printed nicely, we obtain the induced map::

        sage: phi.SetName('phi')
        sage: phi_star = H2.hom(phi,H1)   #indirect doctest
        sage: phi_star
        phi^*
        sage: phi_star.domain()
        H^*(DihedralGroup(8); GF(2))
        sage: phi_star.codomain()
        H^*(D8; GF(2))
        sage: print([H1.element_as_polynomial(phi_star(X)) for X in H2.gens()])
        [1: 0-Cocycle in H^*(D8; GF(2)), b_1_0^2+c_2_2: 2-Cocycle in H^*(D8; GF(2)), b_1_1+b_1_0: 1-Cocycle in H^*(D8; GF(2)), b_1_0: 1-Cocycle in H^*(D8; GF(2))]

    Similarly, we get the induced map of the inverse map::

        sage: Src = phi.Source()
        sage: Rng = phi.Range()
        sage: Gens = Rng.GeneratorsOfGroup()
        sage: phi_inv = Rng.GroupHomomorphismByImages(Src, Gens, [phi.PreImagesRepresentative(g) for g in Gens])
        sage: phi_star_inv = H1.hom(phi_inv,H2)
        sage: print([H2.element_as_polynomial(phi_star_inv(X)) for X in H1.gens()])
        [1: 0-Cocycle in H^*(DihedralGroup(8); GF(2)), b_1_0*b_1_1+c_2_2: 2-Cocycle in H^*(DihedralGroup(8); GF(2)), b_1_1: 1-Cocycle in H^*(DihedralGroup(8); GF(2)), b_1_1+b_1_0: 1-Cocycle in H^*(DihedralGroup(8); GF(2))]

    One can compose induced maps by multiplication respectively by applying one map to the other.
    Here, we test that the composition of the induced map and its inverse is the identity::

        sage: [X == phi_star_inv(phi_star(X)) == (phi_star_inv*phi_star)(X) == phi_star_inv(phi_star)(X) for X in H2.gens()]
        [True, True, True, True]
        sage: [X == phi_star(phi_star_inv(X)) == (phi_star*phi_star_inv)(X) == phi_star(phi_star_inv)(X) for X in H1.gens()]
        [True, True, True, True]

    It is possible to convert an induced homomorphism into a map of quotient rings in the
    Singular interface. This allows for working with cohomology ring elements of very high
    degrees. However, it is always needed to take care of the ``basering`` in Singular::

        sage: S_phi_star = singular(phi_star)
        sage: singular(H2).set_ring()
        sage: I = singular.ideal(['c_2_2^50','b_1_0^50','b_1_1^50'])
        sage: singular(H1).set_ring()
        sage: imI = S_phi_star(I)

    Note that Singular does pfte not do automatic reduction in quotient rings. So, eventually we
    do the reductions explicitly, in two ways, with the same result::

        sage: imI.reduce(singular('ideal(0)'))
        b_1_0^100+c_2_2^2*b_1_0^96+c_2_2^16*b_1_0^68+c_2_2^18*b_1_0^64+c_2_2^32*b_1_0^36+c_2_2^34*b_1_0^32+c_2_2^48*b_1_0^4+c_2_2^50,
        b_1_1^50+b_1_0^50,
        b_1_0^50
        sage: singular(H2).set_ring()
        sage: I_red = I.reduce(singular('ideal(0)'))
        sage: singular(H1).set_ring()
        sage: S_phi_star(I_red).reduce(singular('ideal(0)'))
        b_1_0^100+c_2_2^2*b_1_0^96+c_2_2^16*b_1_0^68+c_2_2^18*b_1_0^64+c_2_2^32*b_1_0^36+c_2_2^34*b_1_0^32+c_2_2^48*b_1_0^4+c_2_2^50,
        b_1_1^50+b_1_0^50,
        b_1_0^50

    """

#################
## init, dealloc(automatic in this case), repr
    def __init__(self, parent, MTX m, MTX M, int d, name = None):
        """
        The following tests against a bug occuring in an earlier version of our package.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.eval('Group([(3,4,5,6,7,8,9,10),(1,2)])')
            sage: V = libgap.eval('Group([(1,2),(3,4)])')
            sage: GGen = G.GeneratorsOfGroup()
            sage: phi = V.GroupHomomorphismByImages(G,V.GeneratorsOfGroup(),[GGen[0]^4,GGen[1]])
            sage: H0 = CohomologyRing(16,5)
            sage: H0.make()
            sage: HG = CohomologyRing(G,GroupName='C8xC2', from_scratch=True)
            sage: HG.make()
            sage: HV = CohomologyRing(4,2)
            sage: HV.make()
            sage: r0 = H0.hom(phi,HV)   # indirect doctest
            sage: rG = HG.hom(phi,HV)
            sage: [HV.element_as_polynomial(r0(X)) for X in H0.gens()]
            [1: 0-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_0^2: 2-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))]
            sage: [HV.element_as_polynomial(rG(X)) for X in HG.gens()]
            [1: 0-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_0^2: 2-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))]

        """
        RingHomomorphism.__init__(self, parent)
        if not isinstance(parent, CohomologyHomset):
            raise TypeError("Parent must be a <CohomologyHomset>")
        self._sing_val = None
        self._sing_domain = ''
        self._sing_codomain = ''
        self._elim_cache = {}
        # self will be induced by a chain map
        # Here, Src denotes the source of the chain map, hence,
        # it corresponds to the codomain of the induced map.
        # Slight complication: If we have a non prime power group,
        # we need to work in a Sylow p-subgroup.
        Src = parent._codomain._HP or parent._codomain
        Tgt = parent._domain._HP or parent._domain # sic! We have *co*homology
        ## check admissibility of input
        cdef RESL S = Src.Resl
        cdef RESL T = Tgt.Resl
        if (d>0):
            if (M._nrows <> S.rank(0)*T.rank(d)):
                raise ValueError("Second matrix must have %d rows"%(S.rank(0)*T.rank(d)))
        else:
            if (M._nrows <> T.rank(0)*S.rank(-d)):
                raise ValueError("Second matrix must have %d rows"%(T.rank(0)*S.rank(-d)))
        if (M._ncols <> T.G_Alg.Data.nontips):
            raise ValueError("Second matrix must have |G|=%d colums"%T.G_Alg.Data.nontips)
        if (m._ncols <> T.G_Alg.Data.nontips):
            raise ValueError("First matrix must have |G|=%d colums"%T.G_Alg.Data.nontips)
        if (m._nrows <> S.G_Alg.Data.nontips):
            raise ValueError("First matrix must have |H|=%d rows"%S.G_Alg.Data.nontips)
        if (M.Data.Field != S.coef() or (m.Data.Field != S.coef())):
            raise ValueError("Matrices must be defined over GF(%d)"%S.coef())
        # self.HSrc = Src # this would be an unnecessary reference
        # self.HTgt = Tgt # to an object that is already determined
                          # by parent._(co)domain
        self.Src  = S
        self.Tgt  = T
        self.Deg  = d
        self.GMap = m
        self.Data = [M]
        self._name = name

    def __copy__(self):
        """
        NOTE:

        Computing higher terms of a chain map can be very time
        consuming. Therefore, chain maps are cached, i.e., chain maps
        with the same basic data are not only equal but identical.

        TEST::

            sage: from pGroupCohomology import CohomologyRing
            sage: H = CohomologyRing(8,3,websource=False)
            sage: r = H.restriction_maps()[1][1]
            sage: r is loads(dumps(r))
            True
            sage: r is copy(r)    #indirect doctest
            False
            sage: r == copy(r)
            True
        """
        return ChMap(self.parent(),self.GMap,self.Data[0],self.Deg,self._name)

    def __reduce__(self):
        """
        Return data used for pickling/unpickling ``self``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star is loads(dumps(phi_star)) # indirect doctest
            True

        """
        return chmap_unpickle, (self.domain(),self.codomain(),self.GMap,self.Data,self.Deg,self._name)

    def _repr_(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star   # indirect doctest
            Induced homomorphism of degree 0 from H^*(DihedralGroup(8); GF(2)) to H^*(D8; GF(2))
            sage: phi_star.set_name('phi^*')
            sage: phi_star
            phi^*

        """
        if self._name:
            return self._name
        return "Induced homomorphism of degree %d from %s to %s"%(self.Deg,self._parent._domain.__repr__(), self._parent._codomain.__repr__())

    def label(self):
        r"""
        Provide a short description of this chain map, using a name when available.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star.label()
            'Map H^*(DihedralGroup_8_; GF(2)) -> H^*(8gp3; GF(2))'
            sage: phi_star.set_name('phi^*')
            sage: phi_star.label()
            'phi^*'

        """
        if self._name:
            return self._name
        try:
            dlabel = self._parent._domain.label()
        except AttributeError:
            dlabel = repr(self._parent._domain)
        try:
            clabel = self._parent._codomain.label()
        except AttributeError:
            clabel = repr(self._parent._codomain)
        return "Map %s -> %s"%(dlabel, clabel)

    def __str__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: print(phi_star)    # indirect doctest
            Induced homomorphism of degree 0 from H^*(DihedralGroup(8); GF(2)) to H^*(D8; GF(2))
            defined by
            [1 0 0 0 0 0 0 0]
            sage: phi_star.set_name('phi^*')
            sage: print(phi_star)
            phi^*
            defined by
            [1 0 0 0 0 0 0 0]

        """
        OUT = self.__repr__()
        OUT = OUT + "\n"+"defined by\n"+self.__getitem__(0).__str__()
        return OUT

    def _singular_(self, S):
        """
        Represent ``self`` as a map between the Singular interface versions of domain and codomain.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: singular(phi_star.codomain()).set_ring()
            sage: f = singular(phi_star)   # indirect doctest
            sage: f
            sage...[1]=b_1_0^2+c_2_2
            sage...[2]=b_1_1+b_1_0
            sage...[3]=b_1_0
            sage: singular(H2).set_ring()
            sage: I = singular.ideal(['b_1_1^2+c_2_2','c_2_2^20'])
            sage: singular(H1).set_ring()
            sage: f(I).reduce(singular.ideal(0))
            c_2_2,
            b_1_0^40+c_2_2^4*b_1_0^32+c_2_2^16*b_1_0^8+c_2_2^20

        """
        if (self._sing_val is not None):
            if (self._sing_val.parent() is S):
                try:
                    self._sing_val._check_valid()
                except ValueError:
                    self._sing_val = None
            else:
                self._sing_val = None
        try:
            br = S('basering')
        except:
            br = None
        C = self.codomain()
        D = self.domain()
        RD = S(D)
        RC = S(C)
        if RD.name() == self._sing_domain and RC.name() == self._sing_codomain and self._sing_val is not None:
            return self._sing_val
        from sage.interfaces.singular import SingularElement
        from pGroupCohomology.modular_cohomology import MODCOHO
        if isinstance(D,MODCOHO):
            dgb = S.eval('degBound')
            S.eval('degBound=0')
            Gen = [X.as_cocycle_in_sylow()._NF_().value() for X in D.Gen]
            D = D._HSyl or D
            # Now, Gen provides cocycles in singular(D), D = self.domain()._HSyl
            CSyl = C._HSyl or C
            tmpPhi = S(D.hom(self.GMap, CSyl))
            S(CSyl).set_ring()
            try:
                GenIm = [tmpPhi(X).NF('std(0)') for X in Gen]
            except:
                S.eval('degBound='+dgb)
                raise
            GenIm = [MODCOCH(CSyl,GenIm[i], S=S, is_polyrep=True,deg=self.domain().degvec[i],is_NF=True) for i in range(len(GenIm))]
            if C is CSyl:
                Images = [X.name() for X in GenIm]
            else:
                try:
                    Images = [C.stable_to_polynomial(X, verify=False).name() for X in GenIm]
                except BaseException,msg:
                    if 'None' in repr(msg):
                        raise RuntimeError("Theoretical error: One of the generator images is not stable")
                    raise
            S.eval('degBound='+dgb)
        else:
            Images = [(self(X)).as_polynomial() for X in D.Gen]

        RC.set_ring()
        I = S.ideal(Images)
        self._sing_val = SingularElement(S, 'map', ','.join([RD.name()]+Images))
        self._sing_domain = RD.name()
        self._sing_codomain = RC.name()
        if br is not None:
            br.set_ring()
        return self._sing_val

    def exportData(self, f):
        """
        Store data describing the induced map into files.

        INPUT:

        ``f`` - a string, providing the path and the beginning of
        the name of the files into which the terms of ``self`` shall be saved

        OUTPUT:

        The matrix ``self[i]`` is saved to the file ``f+repr(i)``.

        NOTE:

        This method is internally used, in order to save memory by disposing
        of data that are currently not needed. So, a user would normally not
        directly invoke the method.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: print(phi_star(H2.1))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 0 1]
            sage: print(phi_star.__getitem_name__(1))
            [1 0 0 0 0 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 1 1 0 0 0 0]
            sage: f = tmp_dir()
            sage: phi_star.exportData(f)
            sage: phi_star.__getitem_name__(1) == f+'1'
            True

        """
        if not isinstance(f,basestring):
            raise TypeError("String expected")
        cdef int i
        cdef int M = len(self.Data)
        for i in range(1, M):
            Data_i = self.Data[i]
            if isinstance(Data_i,basestring):
                if Data_i != f+str(i):
                    coho_logger.debug('export data', self)
                    Data_i = self[i]
                    safe_save(Data_i, f+str(i))
                    self.Data[i] = f+str(i)
            else:
                coho_logger.debug('export data', self)
                safe_save(Data_i, f+str(i))
                self.Data[i] = f+str(i)

#################
## structural parts
    def src(self):
        """
        Return the source of the underlying chain map (type :class:`~pGroupCohomology.resolution.RESL`).

        NOTE:

        Since cohomology is a contravariant functor, the output of ``src()`` is
        the resolution of the *codomain*.

        EXAMPLES:

        We first create the cohomology rings for two different presentations of the
        dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi_star = H2.hom(phi,H1)
            sage: print(phi_star.src())
            Resolution:
            0 <- GF(2) <- GF(2)[D8] <- rank 2 <- rank 3 <- rank 4
            sage: phi_star.src() is phi_star.codomain().resolution()
            True

        """
        return self.Src

    def tgt(self):
        """
        Return the codomain of the underlying chain map (type :class:`~pGroupCohomology.resolution.RESL`).

        NOTE:

        Since cohomology is a contravariant functor, the output of ``tgt()`` is
        the resolution of the *domain*.

        EXAMPLES:

        We first create the cohomology rings for two different presentations of the
        dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi_star = H2.hom(phi,H1)
            sage: print(phi_star.tgt())
            Resolution:
            0 <- GF(2) <- GF(2)[DihedralGroup(8)] <- rank 2 <- rank 3 <- rank 4
            sage: phi_star.tgt() is phi_star.domain().resolution()
            True

        """
        return self.Tgt

    def G_map(self):
        """
        Return the underlying homomorphism of group algebras (given by a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix).

        EXAMPLES:

        We first create the cohomology rings for two different
        presentations of the dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: G2 = libgap.DihedralGroup(8)
            sage: H1 = CohomologyRing(8,3)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H1.make()
            sage: H2.make()

        In order to obtain reproducible doc tests, we switch to permutation
        groups that are, from the perspective of our programs, equivalent to
        ``G1`` and ``G2``, and provide an explicit group isomorphism::

            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: H1.group()==phi.Source()
            True
            sage: H2.group().canonicalIsomorphism(phi.Range()) != libgap.eval('fail')
            True
            sage: phi.IsInjective()
            true
            sage: phi.IsSurjective()
            true
            sage: phi_star = H2.hom(phi,H1)
            sage: print(phi_star.G_map())
            [1 0 0 0 0 0 0 0]
            [0 1 1 1 1 1 1 1]
            [0 1 0 0 1 1 0 0]
            [0 0 0 1 0 0 1 1]
            [0 0 0 1 1 0 0 1]
            [0 0 0 0 0 1 1 0]
            [0 0 0 0 0 1 0 1]
            [0 0 0 0 0 0 0 1]

        """
        return self.GMap

    def deg(self):
        """
        Return the degree of ``self``.

        NOTE:

        An induced homomorphism always is of degree zero. We provide this method since
        :class:`~pGroupCohomology.cochain.ChMap` in principle also works for more
        general maps so that the image has a different degree from the source.

        EXAMPLES:

        We first create the cohomology rings for two different presentations of the
        dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star.deg()
            0

        """
        return self.Deg

    def knownDeg(self):
        """
        Return the degree out to which ``self`` was constructed.

        EXAMPLES:

        We first create the cohomology rings for two different presentations of the
        dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()

        In order to obtain reproducible doc tests, we switch to permutation
        groups that are, from the perspective of our programs, equivalent to
        ``G1`` and ``G2``, and provide an explicit group isomorphism::

            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: H1.group()==phi.Source()
            True
            sage: H2.group().canonicalIsomorphism(phi.Range()) != libgap.eval('fail')
            True
            sage: phi.IsInjective()
            true
            sage: phi.IsSurjective()
            true
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star.knownDeg()
            0
            sage: print(phi_star(H2.1))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 0 1]
            sage: phi_star.knownDeg()
            2

        """
        return len(self.Data)-1

    def name(self):
        """
        Return the name of ``self``.

        NOTE:

        Since induced homomorphisms are cached, there can not be two equal induced
        homomorphisms with a different name.

        EXAMPLES:

        We first create the cohomology rings for two different presentations of the
        dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi.SetName('phi')
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star.name()
            'phi^*'

        """
        return self._name

    def set_name(self, s):
        """
        Give ``self`` a name.

        NOTE:

        Since induced homomorphisms are cached, there can not be two equal induced
        homomorphisms with a different name. If the :meth:`~pGroupCohomology.cohomology.COHO.hom`
        method is called, the name will be reset.

        EXAMPLES:

        We first create the cohomology rings for two different presentations of the
        dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi.SetName('phi')
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star.name()
            'phi^*'
            sage: phi_star.set_name('foobar')
            sage: phi_star.name()
            'foobar'
            sage: H2.hom(phi,H1).name()
            'phi^*'
            sage: phi_star.name()
            'phi^*'

        """
        if not isinstance(s, basestring):
            raise TypeError("String expected")
        self._name = s

    def __getitem_name__(self,key):
        """
        Return `n`-th lift of ``self`` either as file name or matrix.

        INPUT:

        n - an integer

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: print(phi_star(H2.1))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 0 1]
            sage: print(phi_star.__getitem_name__(1))
            [1 0 0 0 0 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 1 1 0 0 0 0]
            sage: f = tmp_dir()
            sage: phi_star.exportData(f)
            sage: phi_star.__getitem_name__(1) == f+'1'
            True

        """
        return self.Data[key]

    def __getitem__(self,key):
        """
        Return `n`-th lift of ``self`` as matrix.

        INPUT:

        n - integer

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: phi_star = H2.hom(phi,H1)
            sage: print(phi_star(H2.1))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 0 1]
            sage: print(phi_star[1]) # indirect doctest
            [1 0 0 0 0 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 1 1 0 0 0 0]
            sage: f = tmp_dir()
            sage: phi_star.exportData(f)
            sage: phi_star.__getitem_name__(1) == f+'1'
            True
            sage: print(phi_star[1]) # indirect doctest
            [1 0 0 0 0 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 1 1 0 0 0 0]

        """
        if isinstance(self.Data[key],basestring):
            sobj = '' if self.Data[key].endswith('.sobj') else '.sobj'
            try:
                return load(self.Data[key]+sobj)  # realpath here?
            except (OSError, IOError):
                # Something went wrong, probably when moving data.
                # Infer the correct root from the root of the domain!
                # This is expected to happen when being called for restriction maps
                # from inside COHO.reconstructSubgroups().
                root = self.domain().root
                rawData = self.Data[key]
                rawData,fname1 = os.path.split(rawData)
                rawData,fname2 = os.path.split(rawData)
                rawData,fname3 = os.path.split(rawData)
                newData = os.path.join(root,fname3,fname2,fname1)
                try:
                    return load(newData+sobj)  # realpath here?
                except (OSError, IOError):
                    raise IOError("Files on disk have been moved, can not find data")
        else:
            return self.Data[key]

    def __setitem__(self,key,object L):
        """
        INPUT:

        ``key`` - an integer
        ``L`` - an :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix or a list thereof.

        OUTPUT:

        A matrix ``L`` is inserted in the internal data at position ``key``,
        and the contents of a list ``L`` are inserted in the internal data
        starting with position ``key``.

        NOTE:

        This should only be of internal use.

        TEST::

            sage: from pGroupCohomology import CohomologyRing
            sage: H = CohomologyRing(8,3,websource=False)
            sage: r1 = H.restriction_maps()[1][1]
            sage: r1.knownDeg()
            2
            sage: r2 = copy(r1)
            sage: r1.lift()
            sage: r1.lift()
            sage: r1.lift()
            sage: r1.lift()
            sage: r1.knownDeg()
            6
            sage: r2.knownDeg()
            0
            sage: r2[0] = [r1[i] for i in range(3)]  #indirect doctest
            sage: r2.knownDeg()
            2
            sage: r2[1] == r1[1]
            True
            sage: r2[2] == r1[2]
            True

        """
        #C[d]=(M(d),M(d+1),...): Set the lifts to M(d),M(d+1),... (type MTX or file name) starting in term d
        if (isinstance(key,Integer)) or (isinstance(key,int)):
            if (key>=0) and (key<=len(self.Data)):
                self.Data[key:] = L
            else:
                raise IndexError("index {} out of range".format(key))
        else:
            raise TypeError("key must be an integer, not {}".format(type(key)))


#########################
## ==, <, >
    cpdef _richcmp_(self, other, int x):
        """
        M==N <=> M and N are the same chain maps.

        NOTE:

        Equality holds if the two maps are defined over the same
        source and target rings, have the same degree shift, and are
        described by the same matrix in the lowest degree.

        EXAMPLES::


            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: CohomologyRing.set_workspace(tmp_dir())
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: r = H.restriction_maps()[1][1]
            sage: r is copy(r)
            False
            sage: r == copy(r)    #indirect doctest
            True
            sage: r < copy(r)
            False
            sage: r <= copy(r)
            True

        """
        # < 0, <= 1, == 2, != 3, > 4, >= 5
        cdef ChMap S = other
        if (x==0) or (x==4):
            return False
        if (x==1) or (x==2) or (x==5):
            if self is S:
                return True
            if (self.Tgt==S.Tgt) and (self.Src==S.Src) and (self.Deg==S.Deg) and (self[0]==S[0]) and (self.GMap==S.GMap):
                return True
            if x==2:
                return False
            return NotImplemented
        ## otherwise: x==3
        if (self.Tgt==S.Tgt) and (self.Src==S.Src) and (self.Deg==S.Deg) and (self[0]==S[0]) and (self.GMap==S.GMap):
            return False
        else:
            return True

##################
## Arithmetic -- Application to (co)chains, composition of maps, inverse maps...

    def apply_to_chain(ChMap self, int d, MTX C):
        r"""
        Apply the underlying chain map of ``self`` to a `d`-chain.

        INPUT:

        - ``d``, the degree of the chain
        - ``C``, a `(r\times |G|)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix, where `r` is
          the rank of the `d`-th term of the resolution, and `|G|`  is the group order.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: f = H.2.right_multiplication()
            sage: print(f.apply_to_chain(1, MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[0,1,0,1,0,1,0,1],[1,0,1,0,1,0,1,0]])))
            [0 1 0 1 0 1 0 1]

        """
        if d<0:
            raise ValueError("There are no chains of negative degree")
        if d < -self.Deg:
            raise ValueError("The map can't be applied to a chain of degree less than %d"%(-self.Deg))
        if self.Deg >= 0:
            while len(self.Data)<d:
                self.lift()
            selfMTX = self[d]
        else:
            while len(self.Data)<(d+self.Deg):
                self.lift()
            selfMTX = self[d+self.Deg]
        cdef RESL S = self.Src
        cdef int RK = S.Data.projrank[d]
        cdef long Snontips = S.G_Alg.Data.nontips
        e = d + self.Deg  # in this degree lives the image
        cdef RESL T = self.Tgt
        cdef int rk = T.Data.projrank[e]
        cdef long Tnontips = T.G_Alg.Data.nontips
        # Test whether C represents a d-chain in S
        if C.ncols()!=Snontips:
            raise ValueError("A chain must be represented by a matrix with %d columns"%Snontips)
        if C.nrows()!=RK:
            raise ValueError("A %d-chain must be represented by a matrix with %d rows"%(d,RK))
        cdef MTX OUT = new_mtx(MatAlloc(T.G_Alg.Data.p, rk, Tnontips), C)
        cdef int i
        cdef MTX row = new_mtx(MatAlloc(OUT.Data.Field, 1, self.GMap.Data.Noc), C)
        FfSetField(OUT.Data.Field)
        for i from 0 <= i < RK:
            FfSetNoc(row.Data.Noc)
            FfMapRow(FfGetPtr(C.Data.Data, i), self.GMap.Data.Data, self.GMap.Data.Nor, row.Data.Data)
            T_rightaction = T.G_Alg.r_action(row)
            OUT += selfMTX.get_slice(i*rk, (i+1)*rk)._multiply_strassen(T_rightaction)
        OUT.set_immutable
        return OUT

    def __mul__(ChMap self, x):
        """
        CM*Co: CM of type <ChMap>, Co of type <COCH> or <ChMap>.

        If Co is a cochain (type <COCH>), CM*Co is the image of Co
        under the induced map of the chain map CM.

        If Co is a chain map (type <ChMap>), CM*Co is the composition
        of Co followed by CM.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()
            sage: phi = G1.IsomorphismGroups(G2)
            sage: phi_star = H2.hom(phi,H1)
            sage: res = H1.restriction_maps()[2][1]
            sage: res_phi_star = res*phi_star
            sage: [res_phi_star(X) == (res*phi_star)(X) == res(phi_star)(X) for X in H2.gens()]    # indirect doctest
            [True, True, True, True]

        """
        cdef ChMap OUT
        cdef MTX OUT_M,xMTX,selfMTX
        cdef COCH OUT_C
        cdef int i,j, t_rk,s_rk,cf,xLj, i_trk
        cdef long X
        cdef list L=[]
        cdef int RK, Rk, rk
        cdef int nt
        if isinstance(x, MODCOCH): # the output will be a MODCOCH
            if self.domain() != x.parent():
                raise ValueError("Argument must be contained in the domain of the map")
            if (x.deg()-self.Deg < 0):
                raise IndexError("Degree of second factor (type %s) must be at least %d"%(repr(MODCOCH),self.Deg))
            singular = x._Svalue.parent()
            # 1. get the corresponding map of the preferred subgroup of domain to the Sylow subgroup of codomain
            Pself = (self.domain()._HP or self.domain()).hom(self.G_map(), self.codomain()._HSyl or self.codomain())
            Sself = singular(Pself)
            Sx = x._Svalue
            singular(self.codomain()._HSyl or self.codomain()).set_ring()
            if self.codomain()._HSyl is not None:
                return self.codomain().stable_to_polynomial(MODCOCH(self.codomain()._HSyl, singular('NF(%s(%s),std(0))'%(Sself.name(),Sx.name())), deg=x.deg(), S=singular, is_NF=True, is_polyrep=True))
            else:
                return MODCOCH(self.codomain(), singular('NF(%s(%s),std(0))'%(Sself.name(),Sx.name())), deg=x.deg(), S=singular, is_NF=True, is_polyrep=True)
        elif isinstance(x, ChMap):
            if self.domain()!=x.codomain():
                raise ValueError("Composition of induced maps is impossible - domain and codomain don't match")
            # We have a contravariant functor. Hence, composing self after x means to
            # first apply the underlying chain map of self, followed by the underlying chain map of x
            # Notational convention: Double uppercase means stuff in the source of the underlying chain map
            # of self; upper-lowercase means stuff in the middle resolution; double lowercase denotes the
            # target resolution, the image of the underlying chain map of x. base_deg is the degree in the middle.
            nt = x.G_map().ncols()
            xMTX = None
            # Will have a map of degree self.Deg+x.deg(), first self then x.
            # We must distinguish five cases:
            if (x.deg() <= 0) and (self.deg() <= 0):
                while (self.knownDeg() <= -x.deg()):
                    self.lift()
                selfMTX = self[-x.deg()]
                xMTX = x[0]
                rk = 1
                Rk = xMTX.nrows()
                RK = selfMTX.nrows()//Rk
                base_deg = -x.deg()
            if (x.deg() > 0) and (self.deg()<0):
                raise ValueError("We can't compose a map of negative degree with a map of positive degree")
            if (self.Deg > 0) and (x.deg()>0):
                while(x.knownDeg() <= self.deg()):
                    x.lift()
                selfMTX = self[0]
                xMTX = x[self.deg()]
                RK = 1
                Rk = selfMTX.nrows()
                rk = xMTX.nrows()//Rk
                base_deg = self.Deg
            if (x.deg() < 0) and (self.deg() > 0):
                if self.Deg+x.deg() < 0:
                    while (self.knownDeg() <= -(self.Deg+x.deg())):
                        self.lift()
                    selfMTX = self[-(self.Deg+x.deg())]
                    xMTX = x[0]
                    rk = 1
                    Rk = xMTX.nrows()
                    RK = selfMTX.nrows()//Rk
                    base_deg = -x.deg()
                else:
                    while (x.knownDeg() <= (self.Deg+x.deg())):
                        x.lift()
                    selfMTX = self[0]
                    xMTX = x[self.Deg+x.deg()]
                    RK = 1
                    Rk = xMTX.nrows()
                    rk = selfMTX.nrows()//Rk
                    base_deg = self.deg()
            OUT_M = new_mtx(MatAlloc(self.Tgt.G_Alg.Data.p, RK*rk, nt), xMTX)
            for i from 0 <= i < RK:
                OUT_M[i*rk] = x.apply_to_chain(base_deg, selfMTX.get_slice(i*Rk, (i+1)*Rk))
            OUT = x.domain().hom(self.G_map()*x.G_map(), self.codomain(),OUT_M,self.Deg+x.deg())
            if self.name() is not None and x.name() is not None:
                OUT.set_name(self.name()+'('+x.name()+')')
            return OUT
        elif isinstance(x, COCH):
            if (self.domain() is not x.parent()):
                raise ValueError("Cochain must belong to the domain of the induced map")
            if (x.deg()-self.Deg < 0):
                raise IndexError("Degree of second factor (%s) must be at least %d"%(repr(COCH),self.Deg))

            # If the codomain belongs to a non prime power group, we have to return MODCOCH
            from pGroupCohomology.modular_cohomology import MODCOHO
            if isinstance(self.codomain(), MODCOHO):
                Pself = (self.domain()).hom(self.G_map(), self.codomain()._HP)
                singular = self.codomain().GenS.parent()
                Sself = singular(Pself)
                Sx = singular(x)
                singular(self.codomain()._HP).set_ring()
                if self.name():
                    outname = self.name()+'('+x.name()+')'
                else:
                    outname = '('+x.name()+')_'
                return MODCOCH(self.codomain(), singular('NF(%s(%s),std(0))'%(Sself.name(),Sx.name())), deg=x.deg(), name=outname, S=singular)

            if self.Deg > 0:
                base = x.deg() - self.Deg
            else:
                base = x.deg()
            while (base >= len(self.Data)):
                self.lift()
            selfMTX = self.__getitem__(base)
            xMTX = x.MTX()
            s_rk = self.Src.rank(x.deg()-self.Deg)
            t_rk = self.Tgt.rank(x.deg())
            if (selfMTX.Data.Nor<>s_rk*t_rk):
                raise RuntimeError("Theoretical Error")
            if (xMTX.Data.Noc<>t_rk):
                raise RuntimeError("Theoretical Error")
            OUT_M = new_mtx(MatAlloc(self.Src.coef(), 1,s_rk), xMTX)
            for i from 0 <= i < s_rk:
                cf = 0
                i_trk = i*t_rk
                for j from 0 <= j < t_rk:
                    xLj = xMTX.get_unsafe_int(0,j)
                    if xLj:
                        cf = cf + xLj*selfMTX.get_unsafe_int(i_trk,0)
                    i_trk+=1
                OUT_M[0,i]=cf
            OUT_M.set_immutable()
            if self._name is not None:
                return COCH(self._parent._codomain,x.deg()-self.Deg, self._name+'('+x.name()+')', OUT_M)
            return COCH(self._parent._codomain,x.deg()-self.Deg, '('+x.name()+")_", OUT_M)
        raise NotImplementedError("Multiplication of ChMap with %s not implemented"%(type(x)))

    def __invert__(self):
        """

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: G1 = libgap.SmallGroup(8,3)
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2,GroupName='Dihedral', from_scratch=True)
            sage: phi12 = G1.IsomorphismGroups(G2)
            sage: phi12.SetName('phi12')
            sage: Phi21 = H2.hom(phi12,H1)
            sage: Src = phi12.Source()
            sage: Rng = phi12.Range()
            sage: Gens = Rng.GeneratorsOfGroup()
            sage: phi21 = Rng.GroupHomomorphismByImages(Src, Gens, [phi12.PreImagesRepresentative(g) for g in Gens])
            sage: phi21.SetName('phi21')
            sage: Phi12 = H1.hom(phi21,H2)
            sage: Phi12
            phi21^*
            sage: Phi12 is Phi21^-1   # indirect doctest
            True
            sage: Phi12
            (phi12^*)^(-1)

        """
        try:
            M = (self.G_map())**(-1)
        except ArithmeticError:
            raise ArithmeticError("Induced homomorphism is not invertible")
        OUT = self.codomain().hom(M,self.domain())
        if self.name() is not None:
            OUT.set_name('('+self.name()+')^(-1)')
        return OUT

    def __pow__(self, n, z):
        """
        Composition of an induced homomorphism with itself.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(576,7443,prime=2)

        This cohomology ring computation is based on two automorphisms of the
        Sylow 2-subgroup of `L_3(4)`. The induced homomorphisms are available
        as an attribute of ``H``, and we raise them to some power::

            sage: f,g = H._PtoPcapCPtwist
            sage: X = H.sylow_cohomology()
            sage: all([(f^2)(t)==f(f(t)) for t in X.gens()])  # indirect doctest
            True
            sage: [X.element_as_polynomial((g^3)(t)) for t in X.gens()]
            [1: 0-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             c_4_18: 4-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             c_4_19: 4-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             b_6_47: 6-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             b_1_0: 1-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             b_1_1: 1-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             b_1_2: 1-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             b_1_3: 1-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             b_3_10: 3-Cocycle in H^*(Syl2(L3(4)); GF(2)),
             b_3_11: 3-Cocycle in H^*(Syl2(L3(4)); GF(2))]

        """
        if n<0:
            OUT = self.__invert__()
            n = -n
            i = True
        else:
            OUT = self
            i = False
        if n!=1:
            if not (OUT.domain() is OUT.codomain()):
                raise ArithmeticError("Induced homomorphism can't be composed with itself")
            OUT = OUT.domain().hom((OUT.G_map())**n, OUT.codomain())
            if self.name() is not None:
                if i:
                    OUT.set_name('('+self.name()+')^(-%d)'%n)
                else:
                    OUT.set_name('('+self.name()+')^%d'%n)
        return OUT

    def __call__(self, X):
        """
        C(X): If X is a tuple (d,n), return the image of the n-th standard cochain of degree d under C. Otherwise, return C*X.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()

        In order to obtain reproducible doc tests, we switch to permutation
        groups that are, from the perspective of our programs, equivalent to
        ``G1`` and ``G2``, and provide an explicit group isomorphism::

            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: H1.group()==phi.Source()
            True
            sage: H2.group().canonicalIsomorphism(phi.Range()) != libgap.eval('fail')
            True
            sage: phi.IsInjective()
            true
            sage: phi.IsSurjective()
            true
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star.lift()
            sage: phi_star.lift()
            sage: print(phi_star((2,2)))   #indirect doctest
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 0 1]
            sage: print(phi_star(H2.1))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 0 1]

        """
        cdef int j, t_rk,s_rk
        cdef MTX tmpM
        cdef list L=[]
        from pGroupCohomology.cochain import COCH
        if isinstance(X,tuple) or isinstance(X,list):
            if not((isinstance(X[0],int) or isinstance(X[0],Integer)) and (isinstance(X[1],int) or isinstance(X[1],Integer))):
                raise TypeError("pair of integers expected")
            if (X[0]-self.Deg < 0):
                raise IndexError("Degree of standard cochain must be at least %d"%(self.Deg))
            s_rk = self.Src.rank(X[0]-self.Deg)
            t_rk = self.Tgt.rank(X[0])
            if (X[1] >= t_rk):
                raise IndexError("Index of standard cochain must not exceed %d"%(t_rk-1))
            tmpM = self.__getitem__(X[0])
            for j from 0 <= j < s_rk:
                L.append(tmpM[j*t_rk+X[1],0])
            return COCH(self._parent._codomain, X[0]-self.Deg, "r_(%d,%d)"%(X[0],X[1]), L)
        elif isinstance(X,COCH) or isinstance(X,MODCOCH) or isinstance(X,ChMap):
            return self.__mul__(X)
        # last resort: Coerce into the codomain's basering
        OUT = self.codomain().base_ring()(X)
        if not isinstance(OUT,tuple):
            return OUT
        raise NotImplementedError("No coercion found")


    def lift(ChMap self):
        """
        Compute the next unknown term of ``self``.

        EXAMPLES:

        We first create the cohomology rings for two different presentations
        of the dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3, from_scratch=True)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()

        In order to obtain reproducible doc tests, we switch to permutation
        groups that are, from the perspective of our programs, equivalent to
        ``G1`` and ``G2``, and provide an explicit group isomorphism::

            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,7)(2,8)(3,5)(4,6), (1,6)(2,5)(3,7)(4,8) ] )')
            sage: H1.group()==phi.Source()
            True
            sage: H2.group().canonicalIsomorphism(phi.Range()) != libgap.eval('fail')
            True
            sage: phi.IsInjective()
            true
            sage: phi.IsSurjective()
            true
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star.lift()
            sage: phi_star.knownDeg()
            1
            sage: phi_star[1]
            [1 0 0 0 0 0 0 0]
            [1 1 1 1 1 1 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 1 1 0 0 0 0]

        """
        ## Next unknown term is Src[len(Data)]->Tgt[len(Data)+Deg] (if Deg>0)
        if (self.Deg > 0):
            SrcDeg = len(self.Data)
            TgtDeg = len(self.Data) + self.Deg
        else:
            TgtDeg = len(self.Data)
            SrcDeg = len(self.Data) - self.Deg
        while (TgtDeg>=self.Tgt.deg()):
            self.Tgt.nextDiff()
        while (SrcDeg>self.Src.deg()):
            self.Src.nextDiff()
        ## AIM: construct matrix describing map from Src[SrcDeg] -> Tgt[TgtDeg]
        ## 1. compose with the next differential
        coho_logger.info('lift in the source resolution', self)
#~         ct=cputime()
#~         wt=walltime()
        cdef MTX M1 = (<MTX>self.Src[SrcDeg])._matrix_times_matrix_(self.GMap) # TgtNontips columns
        cdef MTX M2 = self[-1]                   # TgtNontips columns
        cdef int i,j,k
        cdef MTX Compos
        cdef long SrcNontips = self.Src.G_Alg.Data.nontips
        cdef long TgtNontips = self.Tgt.G_Alg.Data.nontips
        FfSetField(self.Src.coef())
        sig_on()
        try:
            mat = MatAlloc(self.Src.G_Alg.Data.p, self.Src.Data.projrank[SrcDeg]*self.Tgt.Data.projrank[TgtDeg-1],TgtNontips)
        finally:
            sig_off()
        Compos = new_mtx(mat, M1)
        cdef Matrix_t *L

        cdef int RK = self.Src.Data.projrank[SrcDeg]
        cdef int Rk = self.Src.Data.projrank[SrcDeg-1]
        cdef int rk = self.Tgt.Data.projrank[TgtDeg-1]
        cdef PTR M2_ji = M2.Data.Data
        FfSetNoc(TgtNontips)
        for j in range(Rk):
            for i in range(rk):
                L = leftActionMatrix(self.Tgt.G_Alg.Data, M2_ji)
                sig_check()
                for k in range(RK):
                    FfAddMapRow(FfGetPtr(M1.Data.Data, k*Rk+j), L.Data, TgtNontips, FfGetPtr(Compos.Data.Data,k*rk+i))
                    sig_check()
                MatFree(L)
                M2_ji += FfCurrentRowSize
        Compos.set_immutable()

        coho_logger.info('lift in the target resolution to degree %d', self, TgtDeg)
        rk   = self.Tgt.Data.projrank[TgtDeg]
        cdef rk_1 = self.Tgt.Data.projrank[TgtDeg-1]
        cdef long fl = self.Src.G_Alg.Data.p
        cdef long nt = TgtNontips
        d = TgtDeg # will lift to that degree in the target resolution
        cdef MTX OUT
        OUT = new_mtx(MatAlloc(fl, RK*rk, nt), M1)
        cdef MTX TMP, DUMMY
        cdef tuple Piv
        cdef list Z
        cdef dict Autolift = self.Tgt.Autolift.get(d,{})
        if Autolift:
            coho_logger.debug('> use autolift method', self)
            Piv = tuple(Autolift['Piv'])
            ##########################
            # Lift each "long row"
            for i in range(RK):
                # 'lift long row ',i
                Z = Compos._rowlist_(i*rk_1, (i+1)*rk_1-1)
                TMP = new_mtx(MatAlloc(fl, rk, nt), M1)
                FfSetNoc(nt)
                for J in Piv:
                    if Z[J]:
                        DUMMY = Autolift[J][Z[J]]
                        MatAdd(TMP.Data, DUMMY.Data)
                memcpy(MatGetPtr(OUT.Data, i*rk), TMP.Data.Data, FfCurrentRowSize*rk)
            OUT.set_immutable()
            self.Data.append(OUT)
            return

        ## otherwise: use Urbild GB
        coho_logger.debug('> use Urbild Groebner basis', self)
        self.Tgt.load_ugb(d)
        if (self.Tgt.nRgs.ngs.r!=rk_1) or (self.Tgt.nRgs.ngs.s != rk):
            raise RuntimeError("Theoretical error")
        sig_on()
        try:
            innerPreimages(self.Tgt.nRgs, Compos.Data.Data, RK, self.Tgt.G_Alg.Data, OUT.Data.Data)
        finally:
            sig_off()
        self.Data.append(OUT)

    #################################################################################
    ## Preimages
    #################################################################################

    @cached_method
    def _urbild_data(self, d):
        # The data needed to compute the preimage of a cochain by matrix operations
        cdef int i,j,k
        while self.knownDeg() < d:
            self.lift()
        cdef int p = self.Src.coef()
        cdef MTX tmpM
        # Note: self.Src is the resolution of the codomain,
        #       self.Tgt is the resolution of the domain.
        cdef int RK = self.Tgt.rank(d)
        cdef int src_rk = self.Src.rank(d)
        cdef list ttmpL
        cdef list tmpL
        cdef Matrix_t *tmpMTX
        if coho_options['useMTX']:
            coho_logger.debug("> > Construct MTX matrix for elimination", self)
            tmpL = []
            for i from 0 <= i < RK:
                ttmpL = []
                tmpM = self[d]
                for j from 0 <= j < src_rk:
                    ttmpL.append(tmpM[j*RK+i,0])
                tmpL.append(ttmpL + i*[0]+[1]+(RK-i-1)*[0])
            tmpMTX = rawMatrix(p, tmpL)
            M = new_mtx(tmpMTX, None)
        else:
            coho_logger.debug("> Construct matrix for elimination", self)
            M = Matrix(GF(p), RK, src_rk+RK, 0)
            for i from 0 <= i < RK:
                M[i] = (self*self.domain().standardCochain(d,i)).MTX()._rowlist_(0) + i*[0]+[1]+(RK-i-1)*[0]
        coho_logger.debug("> > Compute echelon form of %dx%d matrix"%(M.nrows(),M.ncols()), self)
        M.echelonize()
        return M

    def kernel(self):
        return self.preimage()

    def preimage(self, Item = None, Id = None):
        """
        ASSUMPTION:

        ``self.codomain()`` is completely computed.

        INPUT:

        - ``Item`` -- (optional) element in ``singular(self.codomain())``
                      or element of ``self.codomain()``.
        - ``Id`` -- (optional) ideal (given by a list
          of strings) in the codomain, so that lift
          of ``Item`` will be done modulo that ideal. Only available
          if ``Item`` is not provided as an element of ``self.codomain()``
          but as element in Singular.

        OUTPUT:

        Return the preimage of ``Item`` in ``singular(self.domain())``, if
        ``self.domain()`` is completely known, and in the current basering
        of ``self.domain()`` otherwise.

        - If ``Item`` is not provided, the kernel of ``self``
          resp. the preimage of the ideal given by ``Id`` is
          returned as an ideal in ``singular(self.codomain())``.
        - If ``Item`` is a single element and ``Id`` is ``None``,
          a representative of the preimage of ``Item`` is returned,
          or ``None`` if there is no preimage.
        - If ``Item`` is a single element and ``Id`` defines an ideal,
          a pair is returned, namely one element of the preimage (or ``None``,
          if there is no preimage) and the preimage of the ideal given by
          ``Id``).

        ALGORITHM:

        According to chapter 4.3 of [Green]_.

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,3)
            sage: H.make()
            sage: r = H.restriction_maps()[1][1]
            sage: r
            Induced homomorphism of degree 0 from H^*(SmallGroup(16,3); GF(2)) to H^*(SmallGroup(4,2); GF(2))
            sage: singular(r.codomain()).set_ring()
            sage: p = singular((r.codomain().1+r.codomain().2)^2); p
            c_1_1^2+c_1_0^2
            sage: I = singular.maxideal(2); I
            c_1_1^2,
            c_1_0*c_1_1,
            c_1_0^2
            sage: singular(H).set_ring()
            sage: r.preimage()
            a_1_0,
            b_1_1,
            b_2_1
            sage: r.preimage(p)
            (c_2_3+c_2_2, a_1_0,
            b_1_1,
            b_2_1)
            sage: r.preimage(Id=I)
            a_1_0,
            b_1_1,
            c_2_2,
            c_2_3,
            b_2_1

        If both an element and an ideal are provided, one preimage of the
        preimage of the coset 'element + ideal' is returned, together with
        the preimage of the ideal. Here, the preimage of ``p`` found above
        is contained in the preimage of the ideal ``I``::

            sage: r.preimage(p,Id=I)
            (0, a_1_0,
            b_1_1,
            c_2_2,
            c_2_3,
            b_2_1)


        We verify these findings. The kernel::

            sage: [r(H(t)).as_polynomial() for t in ['a_1_0','b_1_1','b_2_1']]
            ['0', '0', '0']

        The preimage of ``I``::

            sage: [r(H(t)).as_polynomial() for t in ['a_1_0','b_1_1','c_2_2','c_2_3','b_2_1']]
            ['0', '0', 'c_1_1^2', 'c_1_0^2', '0']

        The preimage of ``p``::

            sage: r(H('c_2_3+c_2_2')).as_polynomial()
            'c_1_1^2+c_1_0^2'

        """
        # we do caching, if self.domain() is complete.
        if not self.codomain().completed:
            raise ValueError("Computation of the codomain %s is incomplete"%repr(self.codomin()))
        from pGroupCohomology.auxiliaries import singular
        # If Item is a COCH and Id is None => Use _urbild_data
        # Otherwise, we will use Singular to compute stuff.
        cdef MTX urbild_GB
        cdef tuple pivs
        cdef int i,j
        cdef MTX result
        cdef PTR urbild_p
        if isinstance(Item, COCH) and Id is None:
            urbild_GB = self._urbild_data(Item.deg())
            pivs = urbild_GB.pivots()
            result = new_mtx(MatAlloc(urbild_GB.Data.Field, 1, urbild_GB.Data.Noc), urbild_GB)
            for i in range(len(pivs)):
                j = pivs[i]
                FfAddMulRow(result.Data.Data, MatGetPtr(urbild_GB.Data, i), FfExtract((<COCH>Item).Data.Data.Data, j))
            if result[:,:(<COCH>Item).Data.Data.Noc] != Item.MTX():
                return None
            lift = COCH(self.domain(), Item.deg(), "lift", result[:,(<COCH>Item).Data.Data.Noc:])
            lift_str = lift.as_polynomial()
            if self.domain().completed:
                singular(self.domain()).set_ring()
            else:
                self.domain().set_ring()
            return singular(lift_str)

        if Id is None or Id==[] or Id==['0']:
            key = None
            _elim_cache = self._elim_cache.get(None)
        else:
            singular(self.codomain()).set_ring()
            Id = singular.ideal(Id)
            key = singular.eval('string(%s)'%Id.name())
            _elim_cache = self._elim_cache.get(key)
        have_true_value = False
        if _elim_cache and _elim_cache[2] >= self.domain().last_interesting_degree():
            # The current ring structure is compatible
            try:
                _elim_cache[0]._check_valid()
                _elim_cache[1]._check_valid()
                if _elim_cache[0].parent() is singular:
                    RTotal = _elim_cache[0]
                    G = _elim_cache[1]
                    have_true_value = True
                else:
                    RTotal = None
                    G = None
            except ValueError:
                RTotal = None
                G = None
        else:
            RTotal = None
            G = None

        if G is None and Id is not None:
            # perhaps we have some partially useful data cached
            _elim_cache = self._elim_cache.get(key)
            if _elim_cache and _elim_cache[2] >= self.domain().last_interesting_degree():
                try:
                    _elim_cache[0]._check_valid()
                    _elim_cache[1]._check_valid()
                    if _elim_cache[0].parent() is singular:
                        RTotal = _elim_cache[0]
                        G = _elim_cache[1]
                    else:
                        RTotal = None
                        G = None
                except ValueError:
                    RTotal = None
                    G = None

        Do = self.domain()
        Co = self.codomain()
        p = self.GMap.Data.Field  # should rather be the characteristc,
                                  # but for now we only work over prime fields.

        # These are the rings we have:
        dgb = singular.eval('degBound')
        singular.eval('degBound=0')
        CoS = singular(Co)
        if Do.completed:
            selfS = singular(self)
            DoS = singular(Do)
        else:
            DoS = singular(Do)
            Ims = [Co.element_as_polynomial(self(t)).name() for t in Do.Gen]
            CoS.set_ring()
            selfS = singular('%s,%s'%(DoS.name(),','.join(Ims)),'map')
        DoS.set_ring()
        IDo = singular.maxideal(1)
        CoS.set_ring()
        if Id is not None:
            IdS = singular.ideal(Id)
        ImI = selfS(IDo)
        Do.set_ring()
        Do_flat = singular('basering')
        Co.set_ring()
        Co_flat = singular('basering')

        # Create a copy of CoS with renamed variables:
        MCoS = singular(Co.order_matrix())
        CoSNew_flat = singular.ring(p,'(%s)'%','.join(['@'+t.name() for t in  Co.Gen]), 'M(%s)'%MCoS.name())
        CoRel = Co_flat.fetch(Co.relation_ideal())
        if Id is not None:
            IdS_new = CoS.fetch(IdS)
        if Item is not None:
            Item = CoS.fetch(Item)
        CoSNewI = singular.maxideal(1)

        if G is None:
            # Now, create a ring sum that has the correct
            # anti-commutativity relations. Problem is that
            # singular can't properly eliminate in nc-quotients.
            # Since G is None, RTotal should be None as well.
            if p == 2:
                RTotal_tmp = CoSNew_flat + Do_flat
                RTotal_tmp.set_ring()
                TotalId = (CoSNew_flat.imap(CoRel)+Do_flat.imap(Do.relation_ideal())).groebner()
                RTotal = singular(TotalId.name(), 'qring')
                RTotal.set_ring()
                ImITotal = CoS.fetch(ImI)
            else:
                # since there can only be *one* anti-commutative block,
                # the elimination order will look more complicated.
                # 1. Write the odd degree variables in one block
                Names = ['@'+t.name() for t in Co.Gen[:Co.firstOdd]]+[t.name() for t in Do.Gen[:Do.firstOdd]] + ['@'+t.name() for t in Co.Gen[Co.firstOdd:]]+[t.name() for t in Do.Gen[Do.firstOdd:]]
                # 2. Create an order matrix for elimination of CoSNew
                MD = Do.order_matrix()
                MC = Co.order_matrix()
                from sage.all import Matrix,ZZ
                total_len = len(Do.Gen)+len(Co.Gen)
                Mtot = Matrix(ZZ, total_len)
                Mtot[:len(Co.Gen),:Co.firstOdd] = MC[:len(Co.Gen),:Co.firstOdd]
                Mtot[len(Co.Gen):,Co.firstOdd:Co.firstOdd+Do.firstOdd] = MD[:len(Do.Gen),:Do.firstOdd]
                Mtot[:len(Co.Gen),Co.firstOdd+Do.firstOdd:len(Co.Gen)+Do.firstOdd] = MC[:len(Co.Gen),Co.firstOdd:]
                Mtot[len(Co.Gen):,len(Co.Gen)+Do.firstOdd:] = MD[:len(Do.Gen),Do.firstOdd:]
                MtotS = singular(Mtot)
                Rtmp = singular.ring(p,'(%s)'%','.join(Names),'M(%s)'%MtotS.name())
                singular.lib('ncall.lib')
                RTotal_tmp = singular('superCommutative(%d)'%(Co.firstOdd+Do.firstOdd+1))
                CoSNew_flat.set_ring()
                ImItmp = CoS.fetch(ImI)
                RTotal_tmp.set_ring()
                Itmp = (CoSNew_flat.imap(CoRel)+Do_flat.imap(Do.relation_ideal())).groebner()
                RTotal = singular(Itmp.name(), 'qring')
                RTotal.set_ring()
                ImITotal = CoSNew_flat.imap(ImItmp)
        # Now, RTotal is a ring (no quotient) in elimination order,
        # containing ImITotal (the images of self, after renaming)
        # CoSNew_flat contains CoRel, which provides the relations
        # in the codomain (again, after renaming). The names of the
        # domain (DoS) have been preserved, so that imap of IDo
        # (the list of variables of DoS) works.
        RTotal.set_ring()
        if Item is not None:
            Item = CoSNew_flat.imap(Item)
        if (G is None):
            DoRel = Do_flat.imap(Do.relation_ideal())
            coho_logger.info('Compute preimages by elimination', self)
            if Id is not None:
                G = ( (ImITotal.matrix()-DoS.imap(IDo).matrix()).ideal() + CoSNew_flat.imap(IdS_new) ).groebner()
                self._elim_cache[key] = (RTotal,G,Do.knownDeg)
            else:
                G = ((ImITotal.matrix()-DoS.imap(IDo).matrix()).ideal()).groebner()
                self._elim_cache[key] = (RTotal,G,Do.knownDeg)
            # so, we cached the difficult part.
        elif not have_true_value:
            # we know G for None and have Id != None
            G = (G + CoSNew_flat.imap(IdS_new)).groebner()
            self._elim_cache[key] = (RTotal,G,Do.knownDeg)

        # We are interested in those elements of G that do not contain
        # variables from CoSNew_flat, saved in CoSNewI.
        Filter = CoSNew_flat.imap(CoSNewI)
        singular.eval('attrib(%s,"isSB",1)'%Filter.name())
        Out = [p for p in G if singular.eval('%s==NF(%s,%s)'%(p.name(),p.name(),Filter.name()))=='1']
        # Moreover, if we want to lift one element, we apply G
        # and see if the result is in the domain.
        if (Item is not None):
            OutItem = Item.NF(G)
            # This time, "Filter" could be a problem, since
            # "1=x*y..." might occur.
            DoS.set_ring()
            OutOutItem = RTotal.imap(OutItem)
            RTotal.set_ring()
            if OutItem != DoS.imap(OutOutItem):
                OutItem = False  # indicating that there is no preimage
        else: # we just want to return the preimage ideal
            OutItem = None
        DoS.set_ring()
        if Out:
            PreIm = singular.ideal([RTotal.imap(p) for p in Out]).interred()
        else:
            PreIm = singular.ideal(0)
        singular.eval('degBound='+dgb)
        if OutItem is None:
            return PreIm
        if OutItem is False:
            if Id is not None:
                return None, PreIm
            else:
                return None
        return RTotal.imap(OutItem).NF('std(0)'), PreIm

    def poincare_of_image(self):
        r"""
        Poincaré series of the image of ``self`` (which is a sub-ring of the codomain of ``self``).

        THEORY:

        The kernel of self is computed, using Singular. Together with the
        relation ideal of the domain of self, it allows to compute the
        Poincaré series of the quotient of the domain by the kernel, which is
        isomorphic to the image of self.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()

        We study the restriction to one maximal elementary abelian subgroup::

            sage: phi = H.restriction_maps()[2][1]
            sage: phi
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))
            sage: [phi.codomain().element_as_polynomial(phi(X)) for X in H.gens()]
            [1: 0-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_0*c_1_1+c_1_0^2: 2-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))]

        Apparently, the image has dimension one in degree one (given by
        ``c_1_1``) and dimension two in degree two (given by ``c_1_1^2`` and
        ``c_1_0*c_1_1+c_1_0^2``). And this can be verified using the Poincaré
        series of the image::

            sage: phi.poincare_of_image()
            1/(t^3 - t^2 - t + 1)
            sage: R.<t> = PowerSeriesRing(QQ)
            sage: (1/(t^3 - t^2 - t + 1))[1]
            1
            sage: (1/(t^3 - t^2 - t + 1))[2]
            2

        SEE ALSO:

        :meth:`rank_of_image`

        """
        from pGroupCohomology.auxiliaries import singular
        from sage.all import PolynomialRing
        from sage.all import ZZ
        from sage.all import mul
        from sage.rings.polynomial.hilbert import first_hilbert_series

        R = PolynomialRing(ZZ,'t')
        t = R('t')

        # we make sure that both domain and codomain are completely known
        try:
            br = singular('basering')
        except:
            br = None
        try:
            self.domain().make()
            self.codomain().make()
            phi = singular(self)
            CS = singular(self.codomain())
            DS = singular(self.domain())
            CS.set_ring()
            dgb = singular.eval('degBound')
            singular.eval('degBound = 0')

            DS.set_ring()
            K = self.preimage() # the kernel

            # Something goes wrong in the non-commutative case.
            # Hence, we have to form a commutative version of the basering
            L = singular.ringlist('basering')
            tmpI = L[4]
            tmpR = singular('ring(list(%s[1..3],ideal(0)))'%(L.name()))
            tmpR.set_ring()
            HP = first_hilbert_series(singular('fetch(%s,%s)+fetch(%s,%s)'%(DS.name(),K.name(),DS.name(),tmpI.name())))
            HS = HP/mul([(1-t**X) for X in self.domain().degvec])
            singular.eval('degBound = '+dgb)
            if HS.denominator().leading_coefficient()<0:
                return (-HS.numerator()/(-HS.denominator()))
            return HS
        finally:
            try:
                br.set_ring()
            except:
                pass

    def rank_of_image(self, d):
        r"""
        Rank of the image of term number `d` of ``self``.

        THEORY:

        The rank of the image is computed by applying some linear algebra to the ``d``-th
        term of self.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()

        We study the restriction to one maximal elementary abelian subgroup::

            sage: phi = H.restriction_maps()[2][1]
            sage: phi
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))
            sage: [phi.codomain().element_as_polynomial(phi(X)) for X in H.gens()]
            [1: 0-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_0*c_1_1+c_1_0^2: 2-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))]

        Apparently, the image has dimension one in degree one (given by
        ``c_1_1``) and dimension two in degree two (given by ``c_1_1^2`` and
        ``c_1_0*c_1_1+c_1_0^2``). And this can be verified using the Poincaré
        series of the image::

            sage: phi.rank_of_image(1)
            1
            sage: phi.rank_of_image(2)
            2

        SEE ALSO:

        :meth:`poincare_of_image`

        """
        cdef RESL Tgt = self.domain().resolution()
        cdef RESL Src = self.codomain().resolution()
        while len(self.Data)<=d:
            self.lift()
        cdef MTX M = self[d]
        cdef int nt = M.ncols()
        cdef int RK,rk, i,j
        if self.deg() >= 0:
            RK = Src.rank(d)
            rk = Tgt.rank(d+self.deg())
        else:
            RK = Src.rank(d-self.deg())
            rk = Tgt.rank(d)
        if M.nrows() != RK*rk:
            raise RuntimeError("wrong implementation")
        cdef MTX N = new_mtx(MatAlloc(Tgt.coef(), rk, RK), M)
        for i from 0 <= i < rk:
            for j from 0 <= j < RK:
                N[i,j] = M[j*rk+i,0]
        return N.rank()

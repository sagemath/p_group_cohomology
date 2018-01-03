# -*- coding: utf-8 -*-

#*****************************************************************************
#
#    Bar Codes -- a tool for persistent group cohomology
#
#    Copyright (C) 2009, 2015, 2016 Simon A. King <simon.king@uni-jena.de>
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
Bar codes --- a cohomological group invariant.

AUTHORS:

- Simon King <simon.king@uni-jena.de>

The two classes provided in this module are used to store and
display 'persistent group cohomology'. Persistent group cohomology
was introduced by [EllisKing]_.

The basic idea is as follows: Any normal series of a group gives
rise to a chain of inclusion and quotient maps, which in turn
give induced homomorphisms in cohomology. The degree `d` bar code
associated with the normal series is an upper triangular non-negative
integer matrix, telling how many cocycles of degree `d` 'survive'
how long under the induced maps.

It turns out that these simple collections of integers allow to
distinguish between cohomology rings, even if the rings seem
fairly similar (same Poincaré series, same number of generators
and relations sorted by degree, same depth) and even if the normal
series of the two groups are essentially the same.

EXAMPLES:

We work here with groups of order 64, that are part of the cohomology data base
shipped with this package.
::

    sage: from pGroupCohomology import CohomologyRing
    sage: CohomologyRing.reset()
    sage: H158 = CohomologyRing(64,158)
    sage: H160 = CohomologyRing(64,160)

The Poincaré series, the `a`-invariants, the degrees of generators and of relations
of the cohomology rings coincide::

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

We consider here the bar codes associated with the upper central series. It turns
out that the non-trivial terms of the upper central series and the resulting factor
groups are isomorphic::

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

Nevertheless, the groups can be distinguished using the bar codes associated with
the upper central series::

    sage: B158 = H158.bar_code('UpperCentralSeries')
    sage: B160 = H160.bar_code('UpperCentralSeries')
    sage: B158 == B160
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

These pictures (bar codes) can be interpreted as follows. Let `G` be a finite
`p`-group and let `G=G_0 > G_1 > ... > G_n > 1` be a normal series; in our
example, we have `n=2`. The first `n+1` columns of the bar code correspond to
the normal subgroups groups `G_n, G_{n-1},..., G_0`, while the last `n` columns
correspond to the factor groups `G/G_n, G/G_{n-1},..., G/G_1`. We consider the
sequence of group homomorphisms given by inclusions and quotients. The stars
in the bar code correspond to basis vectors of the degree `d` part of the cohomology
rings of the respective groups. Stars are connected by a line (i.e., a hyphen)
if the corresponding basis vectors are mapped to each other by the induced maps
(which of course go from right to left).

As we have mentioned above, the bar code is determined by an upper triangular
'persistence matrix', which is as follows in degree 3::

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

As usual, the sequence of integers in increasing degrees gives rise to
a Poincaré series. So, in fact we get an upper triangular persistence
matrix whose coefficients are rational functions. We show how these
look in position ``(2,4)``::

    sage: B158.matrix()[2,4]
    2*t^2 + 2*t + 1
    sage: B160.matrix()[2,4]
    t^3 + 2*t^2 + 2*t + 1

"""

from __future__ import print_function, absolute_import
from sage.typeset.ascii_art import AsciiArt
from sage.structure.sage_object import SageObject

##################
# 2d bar codes
class BarCode2d(SageObject):
    r"""
    Integer valued bar codes (bar code in a single degree).

    A bar code in a fixed degree is encoded by an upper triangular
    matrix of integers and can be depicted by arrangement of bars
    of different length.

    EXAMPLES:

    This class was designed for use in persistent group cohomology.
    So, we take an example from this context.
    See :meth:`~pGroupCohomology.cohomology.COHO.bar_code` for the
    theoretical background.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: tmp_root = tmp_dir()
        sage: CohomologyRing.set_user_db(tmp_root)
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: B = H.bar_code('UpperCentralSeries')  # indirect doctest
        sage: B
        Persistence data for H^*(D8; GF(2)) associated with UpperCentralSeries
        sage: B[3]
        Barcode of degree 3 for H^*(D8; GF(2)) associated with UpperCentralSeries
        sage: ascii_art(B[3])
            *
            *
          *-*
          *-*
          *
          *
        *
        sage: B[3].matrix()
        [1 0 0]
        [0 4 2]
        [0 0 4]

    """

    def __init__(self, L, **MetaData):
        r"""
        NOTE:

        An instance of ``BarCode2d`` should not be directly constructed.
        Usually, it is obtained as output of
        :meth:`~pGroupCohomology.cohomology.COHO.bar_code`, or as a slice
        of an instance of :class:`~pGroupCohomology.barcode.BarCode`.

        INPUT:

        ``L`` - a list of persistence data
        ``M`` - Metadata in the form of optional parameters

        ASSUMPTIONS:

        ``dict(L)`` should yield a dictionary whose keys give the
        positions and whose values give the marks of a persistence
        matrix. A persistence matrix is an upper triangular
        non-negative integer matrix, with the additional
        property that the matrix columns are increasing from top to
        bottom and the maatrix rows are decreasing from left to right.
        However, this is not a sufficient condition.

        We are sorry for the fact that the numbering of rows and colums
        does not start with zero; instead, the numbering ranges from
        ``-d`` to ``d``, where ``d`` is given by the length of the
        normal series (non-trivial terms only) by which the bar code
        is defined.

        The metadata can be anything. Currently used is:

        - ``degree``, an integer, the degree to which this bar code belongs
        - ``ring``, the name (string) of the cohomology ring of a group ``G``
        - ``command``, the GAP command producing the normal series of ``G``
          by which the bar code is defined.

        EXAMPLES::

            sage: from pGroupCohomology.barcode import BarCode2d
            sage: L = [((-2,-2),2),((-2,-1),2),((-2,0),1),((-2,1),1),((-2,2),0),((-1,-1),3),((-1,0),1),((-1,1),1),((-1,2),0),((0,0),3),((0,1),2),((0,2),1),((1,1),2),((1,2),1),((2,2),2)]
            sage: B = BarCode2d(L, ring='some ring', degree=3, command='my favourite GAP command') # indirect doctest
            sage: B
            Barcode of degree 3 for some ring associated with my favourite GAP command
            sage: ascii_art(B)
                    *
                *-*-*
                *
              *
            *-*-*-*
            *-*
            sage: B.matrix()
            [2 2 1 1 0]
            [0 3 1 1 0]
            [0 0 3 2 1]
            [0 0 0 2 1]
            [0 0 0 0 2]

        """
        from sage.all import copy
        self._Meta = copy(MetaData)
        D = self._D = dict(L)
        l = self._length = max([X[1] for X in D.keys()])
        # our codes will always range from -self._length to +self._length
        bars = []
        lowerbars = dict([(k,0) for k in range(-l,l+1)])
        for i in range(-l,l+1):
            for j in range(l-i+1):
                n = D[i,l-j] - lowerbars[l-j]# - drawn
                for k in range(i,l+1-j):
                    lowerbars[k] = lowerbars[k]+n
                for k in range(n):
                    bars.append([i,l-j])
        bars.sort()
        bars.reverse()
        self._bars = bars

    def __cmp__(self,other):
        r"""
        TESTS::

            sage: from pGroupCohomology.barcode import BarCode2d
            sage: L = [((-2,-2),2),((-2,-1),2),((-2,0),1),((-2,1),1),((-2,2),0),((-1,-1),3),((-1,0),1),((-1,1),1),((-1,2),0),((0,0),3),((0,1),2),((0,2),1),((1,1),2),((1,2),1),((2,2),2)]
            sage: B = BarCode2d(L, ring='some ring', degree=3, command='my favourite GAP command')
            sage: B==loads(dumps(B))   # indirect doctest
            True

        """
        if not isinstance(other, BarCode2d):
            return -1
        return cmp(self._D, other._D)

    def data(self):
        r"""
        Return the defining data of self as a sorted list.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries',degree=3)
            sage: B
            Barcode of degree 3 for H^*(D8; GF(2)) associated with UpperCentralSeries
            sage: B.data()
            [((-1, -1), 1),
             ((-1, 0), 0),
             ((-1, 1), 0),
             ((0, 0), 4),
             ((0, 1), 2),
             ((1, 1), 4)]

        """
        OUT = self._D.items()
        OUT.sort()
        return OUT

    def matrix(self):
        r"""
        Return the persistence matrix of self.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries',degree=3)
            sage: B.matrix()
            [1 0 0]
            [0 4 2]
            [0 0 4]

        """
        from sage.all import Matrix
        M = Matrix(2*self._length + 1, 2*self._length + 1)
        for X in self._D.items():
            if not (isinstance(X[1],int) or M.base_ring().has_coerce_map_from(X[1].parent())):
                M = M*X[1].parent()(1)
            M[X[0][0]+self._length, X[0][1]+self._length] = X[1]
        return M

    def __repr__(self):
        r"""
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries',degree=3)
            sage: B         #indirect doctest
            Barcode of degree 3 for H^*(D8; GF(2)) associated with UpperCentralSeries

        """
        s = "Barcode"
        if self._Meta.has_key('degree'):
            s += " of degree %d"%self._Meta['degree']
        if self._Meta.has_key('ring'):
            s += " for "+self._Meta['ring']
        if self._Meta.has_key('command'):
            s += " associated with "+self._Meta['command']
        return s

    def _ascii_art_(self):
        r"""
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries',degree=3)
            sage: ascii_art(B)        #indirect doctest
                *
                *
              *-*
              *-*
              *
              *
            *

        """
        L = [('  '*(self._length+X[0]) + '*' + '-*'*((X[1]-X[0]))) for X in self._bars]
        return AsciiArt(L)

    def add_metadata(self, key, datum):
        r"""
        Add further information on the bar code.

        NOTE:

        Currently, only the meta data ``degree``, ``ring`` and ``command``
        are used. But further meta data are, in principle, possible.

        EXAMPLES::

            sage: from pGroupCohomology.barcode import BarCode2d
            sage: B = BarCode2d([((0,0),1)])
            sage: B
            Barcode
            sage: B.add_metadata('degree',5)
            sage: B
            Barcode of degree 5
            sage: B.add_metadata('ring','some fancy ring')
            sage: B
            Barcode of degree 5 for some fancy ring
            sage: B.add_metadata('command','some normal series')
            sage: B
            Barcode of degree 5 for some fancy ring associated with some normal series

        """
        self._Meta[key] = datum

    def plot(self,*args,**kwds):
        r"""
        Produce a picture of the bar code.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries',degree=3)
            sage: plot(B)     # render
            Graphics object consisting of 7 graphics primitives

        """
        from sage.plot.plot import circle, line
        l = len(self._bars)
        G = line([(X,l+1) for X in range(self._bars[0][0],self._bars[0][1]+1)], thickness=2, marker='.', markersize=15)
        for B in range(1,l):
            G += line([(X,l+1-B) for X in range(self._bars[B][0],self._bars[B][1]+1)], thickness=2, marker='.', markersize=15)
        return G


##################
# 3d bar codes

from sage.all import PowerSeriesRing, QQ

class BarCode:
    r"""
    Bar codes (persistent group cohomology).

    A bar code in a fixed degree is encoded by an upper triangular
    matrix of integers and can be depicted by arrangement of bars
    of different length. The full bar code combines the information
    for all degrees, by means of Poincaré series.

    EXAMPLES:

    This class was designed for use in persistent group cohomology.
    So, we take an example from this context.
    See :meth:`~pGroupCohomology.cohomology.COHO.bar_code` for the
    theoretical background.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: tmp_root = tmp_dir()
        sage: CohomologyRing.set_user_db(tmp_root)
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: B = H.bar_code('UpperCentralSeries')    # indirect doctest
        sage: B
        Persistence data for H^*(D8; GF(2)) associated with UpperCentralSeries

    The persistence data are encoded in an upper triangular matrix
    whose entries are Poincaré series::

        sage: B.matrix()
        [       -1/(t - 1)      -1/(t^2 - 1)                 1]
        [                0 1/(t^2 - 2*t + 1)  (-t - 1)/(t - 1)]
        [                0                 0 1/(t^2 - 2*t + 1)]

    The bar code in each degree can be extracted from the Poincaré series::

        sage: B[1]
        Barcode of degree 1 for H^*(D8; GF(2)) associated with UpperCentralSeries
        sage: ascii_art(B[2])
            *
          *-*
          *-*
        *-*
        sage: B[2].matrix()
        [1 1 0]
        [0 3 2]
        [0 0 3]
        sage: B[15].matrix()
        [ 1  0  0]
        [ 0 16  2]
        [ 0  0 16]

    """
    _PSRing = PowerSeriesRing(QQ, names=['t'])
    def __init__(self, L, **MetaData):
        r"""
        NOTE:

        An instance of ``BarCode`` should not be directly constructed.
        Usually, it is obtained as output of
        :meth:`~pGroupCohomology.cohomology.COHO.bar_code`

        INPUT:

        ``L`` - a list of persistence data
        ``M`` - Metadata in the form of optional parameters

        ASSUMPTIONS:

        ``dict(L)`` should yield a dictionary whose keys give the
        positions and whose values give the marks of a persistence
        matrix. A persistence matrix is an upper triangular
        matrix whose marks are univariate power series with non-negative
        integer coefficients (Poincaré series). For each degree,
        the corresponding coefficients of the Poincaré series yield
        an upper triangular integer matrix with the additional
        property that the matrix columns are increasing from top to
        bottom and the maatrix rows are decreasing from left to right.
        However, this is not a sufficient condition.

        We are sorry for the fact that the numbering of rows and colums
        does not start with zero; instead, the numbering ranges from
        ``-d`` to ``d``, where ``d`` is given by the length of the
        normal series (non-trivial terms only) by which the bar code
        is defined.

        TESTS::

            sage: from pGroupCohomology.barcode import BarCode
            sage: R.<t> = ZZ[]
            sage: L = [((-1, -1), -1/(t - 1)), ((-1, 0), -1/(t^2 - 1)), ((-1, 1), 1), ((0, 0), 1/(t^2 - 2*t + 1)), ((0, 1), (-t - 1)/(t - 1)), ((1, 1), 1/(t^2 - 2*t + 1))]
            sage: B = BarCode(L,ring='some ring')    # indirect doctest
            sage: B
            Persistence data for some ring
            sage: ascii_art(B[3])
                *
                *
              *-*
              *-*
              *
              *
            *

        """
        from sage.all import copy
        self._Meta = copy(MetaData)
        self._L = dict(copy(L))
        self._length = max([X[1] for X in self._L.keys()])

    def __cmp__(self,other):
        r"""
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries')
            sage: B == loads(dumps(B))     # indirect doctest
            True

        """
        if not isinstance(other, BarCode):
            return -1
        return cmp(self._L, other._L)

    def data(self):
        r"""
        Return the defining data of self as a sorted list.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries')
            sage: B
            Persistence data for H^*(D8; GF(2)) associated with UpperCentralSeries
            sage: B.data()
            [((-1, -1), -1/(t - 1)),
             ((-1, 0), -1/(t^2 - 1)),
             ((-1, 1), 1),
             ((0, 0), 1/(t^2 - 2*t + 1)),
             ((0, 1), (-t - 1)/(t - 1)),
             ((1, 1), 1/(t^2 - 2*t + 1))]

        """
        OUT = self._L.items()
        OUT.sort()
        return OUT

    def matrix(self):
        r"""
        Return the persistence matrix of self.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: B = H.bar_code('UpperCentralSeries')
            sage: B.matrix()
            [       -1/(t - 1)      -1/(t^2 - 1)                 1]
            [                0 1/(t^2 - 2*t + 1)  (-t - 1)/(t - 1)]
            [                0                 0 1/(t^2 - 2*t + 1)]

        """
        from sage.all import Matrix
        M = Matrix(2*self._length + 1, 2*self._length + 1)
        for X in self._L.items():
            if not (isinstance(X[1],int) or M.base_ring().has_coerce_map_from(X[1].parent())):
                M = M*X[1].parent()(1)
            M[X[0][0]+self._length,X[0][1]+self._length] = X[1]
        return M

    def __repr__(self):
        r"""
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(16,3)
            sage: H.make()
            sage: B = H.bar_code('LowerCentralSeries')
            sage: B        #indirect doctest
            Persistence data for H^*(SmallGroup(16,3); GF(2)) associated with LowerCentralSeries

        """
        s = "Persistence data"
        if self._Meta.has_key('ring'):
            s += " for "+self._Meta['ring']
        if self._Meta.has_key('command'):
            s += " associated with "+self._Meta['command']
        return s

    def __getitem__(self, d):
        r"""
        Return the degree `d` bar code.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(16,3)
            sage: H.make()
            sage: B = H.bar_code('LowerCentralSeries')
            sage: B[3]       #indirect doctest
            Barcode of degree 3 for H^*(SmallGroup(16,3); GF(2)) associated with LowerCentralSeries
            sage: ascii_art(B[3])
                *
              *-*
              *-*
              *-*
              *
              *
              *
            *
            sage: B[3].matrix()
            [1 0 0]
            [0 6 3]
            [0 0 4]

        """
        self._PSRing.set_default_prec(d+3)
        D = {}
        l = self._length
        for i in range(-l,l+1):
            for j in range(i,l+1):
                if self._L.has_key((i,j)):
                    if hasattr(self._L[i,j],'numerator'):
                        D[i,j] = (self._PSRing(self._L[i,j].numerator())/self._PSRing(self._L[i,j].denominator()))[d]
                    else:
                        D[i,j] = (self._PSRing(self._L[i,j]))[d]
                else:
                    D[i,j] = 0
        OUT = BarCode2d(D, **(self._Meta))
        OUT.add_metadata('degree',d)
        return OUT

    def show(self, *args,**kwds):
        r"""
        Show a 3D picture of self.

        INPUT:

        - ``dmin`` (default = 1): optional non-negative integer,
          the lowest shown degree
        - ``dmax`` (default = 10): optional non-negative integer,
          the highest shown degree

        The resulting picture combines the planar bar codes for
        each degree between ``dmin`` and ``dmax`` to a 3-dimensional
        arrangement of bars.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(16,3)
            sage: H.make()
            sage: B = H.bar_code('LowerCentralSeries')
            sage: show(B,dmin=3,dmax=15)
            <html><script type="math/tex">\newcommand{\Bold}[1]{\mathbf{#1}}\verb|Persistence|\phantom{\verb!x!}\verb|data|\phantom{\verb!x!}\verb|for|\phantom{\verb!x!}\verb|H^*(SmallGroup(16,3);|\phantom{\verb!x!}\verb|GF(2))|\phantom{\verb!x!}\verb|associated|\phantom{\verb!x!}\verb|with|\phantom{\verb!x!}\verb|LowerCentralSeries|</script></html>

        For seeing a nice picture, you should instead do
        ``B.show(dmin=3, dmax=15)``.

        """
        dmin = kwds.get('dmin',1)
        dmax = kwds.get('dmax',10)
        from sage.all import sphere, line
        if dmin>=dmax:
            raise ValueError("Optional parameters dmin, dmax must satisfy dmin < dmax")
        bars = [self[i]._bars for i in range(dmin,dmax+1)]
        G = None
        for d in range(0,dmax-dmin+1):
            l = len(bars[d])
            for B in range(l):
                if bars[d][B][0] != bars[d][B][1]:
                    G += line([(X,dmin+d,l+1-B) for X in range(bars[d][B][0],bars[d][B][1]+1)], thickness=2)
                G = sum([sphere(center=(X,dmin+d,l+1-B),size=0.1,color=(0,0,1)) for X in range(bars[d][B][0],bars[d][B][1]+1)],G)
        from sage.all import copy
        KWDS = copy(kwds)
        if KWDS.has_key('dmin'):
            del KWDS['dmin']
        if KWDS.has_key('dmax'):
            del KWDS['dmax']
        G.show(*args,**KWDS)


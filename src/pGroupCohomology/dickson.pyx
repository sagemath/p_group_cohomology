#*****************************************************************************
#
#    Computation of Dickson Invariants
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
Dickson Invariants.

Dickson invariants `Q_{n,s}\\in \\mathbb F_p[y_0,...,y_{n-1}]` are
generators for the invariant ring of the full linear group
`GL(n,\\mathbb F_p)`, where `s` ranges from `0` to `n`, setting
`Q_{n,n} = 1`, and `p` is a prime.

NOTE:

We choose the indices such that `\\deg(Q_{n,s}) = p^n-p^s`. There
also occurs a different convention in the literature.

AUTHORS:

- Simon King <simon.king@uni-jena.de>

THEORY:
-------

According to [Wilkerson]_, the Dickson invariants `Q_{n,s}` with `s<n`
can be defined as follows:

1.  `\\prod_{v \\in \\mathbb F_p^n}(v+X) = X^{p^n} + \\sum_{s=0}^{n-1} (-1)^{n-s} Q_{n,s} X^{p^s}`

[Pham]_ provides the following recursion for `Q_{n,s}`:

* `Q_{n,n} = 1`
* `Q_{n,0} = (V_1\\cdot \\dots \\cdot V_n)^{p-1}`
* `Q_{n,s} = Q_{n-1,s}\\cdot V_n^{p-1} + Q_{n-1,s-1}^p`

where

2. `V_k = \\prod_{\\lambda_i\\in\\mathbb Z_p} (\\lambda_0y_0 + ... + \\lambda_{k-2}y_{k-2} + y_{k-1})` for `1\\le k \\le n`

Apparently the definition of `V_k` is a stumbling block in the recursion,
as it is a product of `p^{k-1}` polynomials. However, combining 1. and 2.,
one can express `V_k` using Dickson invariants `Q_{n,s}` of lower degrees.
Namely, setting `X = y_{k-1}` in 1., 2. becomes

* `V_k = (y_{k-1}^{p^{k-1}} + \\sum_{s=0}^{k-2} (-1)^{k-s-1}\\cdot Q_{k-1,s} \cdot y_{k-1}^{p^{s}})` (in particular, `V_1 = y_0`).

The preceding formula, together with [Pham]_'s recursion, allows for
a convenient computation of the Dickson invariants: One computes
`Q_{n,s}` using `Q_{n-1,s}`, `Q_{n-1,s-1}` and `V_n`, and one computes
`V_n` using `Q_{n-1,0},...,Q_{n-1,n-2}`.

"""

from __future__ import print_function, absolute_import
import sage
import sage.all
from sage.all import prod
from sage.all import add
from sage.all import ZZ
from sage.all import Integer
from sage.all import FiniteField as GF
from sage.all import Matrix
from sage.all import MatrixSpace
from sage.all import PolynomialRing

class DICKSON:
    """
    A factory for computing Dickson invariants.

    Let `p` be a prime number. Then, ``DICKSON(p)`` can compute the Dickson
    invariants over `\\mathbb F_p`. See :mod:`~pGroupCohomology.dickson` for
    the theoretical background.

    EXAMPLES::

        sage: from pGroupCohomology.dickson import DICKSON
        sage: D = DICKSON(3)
        sage: d_3_1 = D(3,1)
        sage: d_3_1
        y0^18*y1^6 + y0^12*y1^12 + y0^6*y1^18 + y0^18*y1^4*y2^2 - y0^12*y1^10*y2^2 - y0^10*y1^12*y2^2 + y0^4*y1^18*y2^2 + y0^18*y1^2*y2^4 + y0^10*y1^10*y2^4 + y0^2*y1^18*y2^4 + y0^18*y2^6 + y0^12*y1^6*y2^6 + y0^6*y1^12*y2^6 + y1^18*y2^6 - y0^12*y1^2*y2^10 + y0^10*y1^4*y2^10 + y0^4*y1^10*y2^10 - y0^2*y1^12*y2^10 + y0^12*y2^12 - y0^10*y1^2*y2^12 + y0^6*y1^6*y2^12 - y0^2*y1^10*y2^12 + y1^12*y2^12 + y0^6*y2^18 + y0^4*y1^2*y2^18 + y0^2*y1^4*y2^18 + y1^6*y2^18
        sage: d_3_1.parent()
        Multivariate Polynomial Ring in y0, y1, y2 over Finite Field of size 3
        sage: p_5_2 = D(5,2)
        sage: p_5_2.degree() == 3^5-3^2
        True
        sage: len(p_5_2.coefficients())
        8025

    """
    def __init__(self,p):
        """
        TESTS::

            sage: from pGroupCohomology.dickson import DICKSON
            sage: D = DICKSON(2)      # indirect doctest
            sage: D(3,2)
            y0^4 + y0^2*y1^2 + y1^4 + y0^2*y1*y2 + y0*y1^2*y2 + y0^2*y2^2 + y0*y1*y2^2 + y1^2*y2^2 + y2^4
            sage: D(3,1)
            y0^4*y1^2 + y0^2*y1^4 + y0^4*y1*y2 + y0*y1^4*y2 + y0^4*y2^2 + y0^2*y1^2*y2^2 + y1^4*y2^2 + y0^2*y2^4 + y0*y1*y2^4 + y1^2*y2^4

        """
        self.K = GF(p)
        self.p = p
        self._cache_ = {}

    def __cmp__(self,other):
        """
        TESTS::

            sage: from pGroupCohomology.dickson import DICKSON
            sage: D = DICKSON(5)
            sage: E = DICKSON(2)
            sage: D == loads(dumps(D))   # indirect doctest
            True
            sage: D == E
            False

        """
        if not (hasattr(other,'__class__') and (self.__class__ == other.__class__)):
            return -1
        return cmp(self.K,other.K)

    def __call__(self,n,s):
        """
        TESTS::

            sage: from pGroupCohomology.dickson import DICKSON
            sage: D = DICKSON(5)
            sage: D(3,2)  # indirect doctest
            y0^100 + y0^80*y1^20 + y0^60*y1^40 + y0^40*y1^60 + y0^20*y1^80 + y1^100 + y0^80*y1^16*y2^4 - y0^76*y1^20*y2^4 + 2*y0^60*y1^36*y2^4 - 2*y0^56*y1^40*y2^4 - 2*y0^40*y1^56*y2^4 + 2*y0^36*y1^60*y2^4 - y0^20*y1^76*y2^4 + y0^16*y1^80*y2^4 + y0^80*y1^12*y2^8 - y0^76*y1^16*y2^8 - 2*y0^60*y1^32*y2^8 + y0^56*y1^36*y2^8 + y0^52*y1^40*y2^8 + y0^40*y1^52*y2^8 + y0^36*y1^56*y2^8 - 2*y0^32*y1^60*y2^8 - y0^16*y1^76*y2^8 + y0^12*y1^80*y2^8 + y0^80*y1^8*y2^12 - y0^76*y1^12*y2^12 - y0^60*y1^28*y2^12 - y0^56*y1^32*y2^12 + 2*y0^52*y1^36*y2^12 + 2*y0^36*y1^52*y2^12 - y0^32*y1^56*y2^12 - y0^28*y1^60*y2^12 - y0^12*y1^76*y2^12 + y0^8*y1^80*y2^12 + y0^80*y1^4*y2^16 - y0^76*y1^8*y2^16 + 2*y0^56*y1^28*y2^16 - 2*y0^52*y1^32*y2^16 - 2*y0^32*y1^52*y2^16 + 2*y0^28*y1^56*y2^16 - y0^8*y1^76*y2^16 + y0^4*y1^80*y2^16 + y0^80*y2^20 - y0^76*y1^4*y2^20 + y0^60*y1^20*y2^20 - y0^52*y1^28*y2^20 + y0^40*y1^40*y2^20 - y0^28*y1^52*y2^20 + y0^20*y1^60*y2^20 - y0^4*y1^76*y2^20 + y1^80*y2^20 - y0^60*y1^12*y2^28 + 2*y0^56*y1^16*y2^28 - y0^52*y1^20*y2^28 + 2*y0^40*y1^32*y2^28 + y0^36*y1^36*y2^28 + 2*y0^32*y1^40*y2^28 - y0^20*y1^52*y2^28 + 2*y0^16*y1^56*y2^28 - y0^12*y1^60*y2^28 - 2*y0^60*y1^8*y2^32 - y0^56*y1^12*y2^32 - 2*y0^52*y1^16*y2^32 + 2*y0^40*y1^28*y2^32 - 2*y0^36*y1^32*y2^32 - 2*y0^32*y1^36*y2^32 + 2*y0^28*y1^40*y2^32 - 2*y0^16*y1^52*y2^32 - y0^12*y1^56*y2^32 - 2*y0^8*y1^60*y2^32 + 2*y0^60*y1^4*y2^36 + y0^56*y1^8*y2^36 + 2*y0^52*y1^12*y2^36 + y0^36*y1^28*y2^36 - 2*y0^32*y1^32*y2^36 + y0^28*y1^36*y2^36 + 2*y0^12*y1^52*y2^36 + y0^8*y1^56*y2^36 + 2*y0^4*y1^60*y2^36 + y0^60*y2^40 - 2*y0^56*y1^4*y2^40 + y0^52*y1^8*y2^40 + y0^40*y1^20*y2^40 + 2*y0^32*y1^28*y2^40 + 2*y0^28*y1^32*y2^40 + y0^20*y1^40*y2^40 + y0^8*y1^52*y2^40 - 2*y0^4*y1^56*y2^40 + y1^60*y2^40 + y0^40*y1^8*y2^52 + 2*y0^36*y1^12*y2^52 - 2*y0^32*y1^16*y2^52 - y0^28*y1^20*y2^52 - y0^20*y1^28*y2^52 - 2*y0^16*y1^32*y2^52 + 2*y0^12*y1^36*y2^52 + y0^8*y1^40*y2^52 - 2*y0^40*y1^4*y2^56 + y0^36*y1^8*y2^56 - y0^32*y1^12*y2^56 + 2*y0^28*y1^16*y2^56 + 2*y0^16*y1^28*y2^56 - y0^12*y1^32*y2^56 + y0^8*y1^36*y2^56 - 2*y0^4*y1^40*y2^56 + y0^40*y2^60 + 2*y0^36*y1^4*y2^60 - 2*y0^32*y1^8*y2^60 - y0^28*y1^12*y2^60 + y0^20*y1^20*y2^60 - y0^12*y1^28*y2^60 - 2*y0^8*y1^32*y2^60 + 2*y0^4*y1^36*y2^60 + y1^40*y2^60 - y0^20*y1^4*y2^76 - y0^16*y1^8*y2^76 - y0^12*y1^12*y2^76 - y0^8*y1^16*y2^76 - y0^4*y1^20*y2^76 + y0^20*y2^80 + y0^16*y1^4*y2^80 + y0^12*y1^8*y2^80 + y0^8*y1^12*y2^80 + y0^4*y1^16*y2^80 + y1^20*y2^80 + y2^100
            sage: D(3,1)
            y0^100*y1^20 + y0^80*y1^40 + y0^60*y1^60 + y0^40*y1^80 + y0^20*y1^100 + y0^100*y1^16*y2^4 + 2*y0^80*y1^36*y2^4 - y0^76*y1^40*y2^4 - 2*y0^60*y1^56*y2^4 - 2*y0^56*y1^60*y2^4 - y0^40*y1^76*y2^4 + 2*y0^36*y1^80*y2^4 + y0^16*y1^100*y2^4 + y0^100*y1^12*y2^8 - 2*y0^80*y1^32*y2^8 - 2*y0^76*y1^36*y2^8 + y0^60*y1^52*y2^8 - y0^56*y1^56*y2^8 + y0^52*y1^60*y2^8 - 2*y0^36*y1^76*y2^8 - 2*y0^32*y1^80*y2^8 + y0^12*y1^100*y2^8 + y0^100*y1^8*y2^12 - y0^80*y1^28*y2^12 + 2*y0^76*y1^32*y2^12 - 2*y0^56*y1^52*y2^12 - 2*y0^52*y1^56*y2^12 + 2*y0^32*y1^76*y2^12 - y0^28*y1^80*y2^12 + y0^8*y1^100*y2^12 + y0^100*y1^4*y2^16 + y0^76*y1^28*y2^16 + y0^52*y1^52*y2^16 + y0^28*y1^76*y2^16 + y0^4*y1^100*y2^16 + y0^100*y2^20 + y0^80*y1^20*y2^20 + y0^60*y1^40*y2^20 + y0^40*y1^60*y2^20 + y0^20*y1^80*y2^20 + y1^100*y2^20 - y0^80*y1^12*y2^28 + y0^76*y1^16*y2^28 + 2*y0^60*y1^32*y2^28 - y0^56*y1^36*y2^28 - y0^52*y1^40*y2^28 - y0^40*y1^52*y2^28 - y0^36*y1^56*y2^28 + 2*y0^32*y1^60*y2^28 + y0^16*y1^76*y2^28 - y0^12*y1^80*y2^28 - 2*y0^80*y1^8*y2^32 + 2*y0^76*y1^12*y2^32 + 2*y0^60*y1^28*y2^32 + 2*y0^56*y1^32*y2^32 + y0^52*y1^36*y2^32 + y0^36*y1^52*y2^32 + 2*y0^32*y1^56*y2^32 + 2*y0^28*y1^60*y2^32 + 2*y0^12*y1^76*y2^32 - 2*y0^8*y1^80*y2^32 + 2*y0^80*y1^4*y2^36 - 2*y0^76*y1^8*y2^36 - y0^56*y1^28*y2^36 + y0^52*y1^32*y2^36 + y0^32*y1^52*y2^36 - y0^28*y1^56*y2^36 - 2*y0^8*y1^76*y2^36 + 2*y0^4*y1^80*y2^36 + y0^80*y2^40 - y0^76*y1^4*y2^40 + y0^60*y1^20*y2^40 - y0^52*y1^28*y2^40 + y0^40*y1^40*y2^40 - y0^28*y1^52*y2^40 + y0^20*y1^60*y2^40 - y0^4*y1^76*y2^40 + y1^80*y2^40 + y0^60*y1^8*y2^52 - 2*y0^56*y1^12*y2^52 + y0^52*y1^16*y2^52 - y0^40*y1^28*y2^52 + y0^36*y1^32*y2^52 + y0^32*y1^36*y2^52 - y0^28*y1^40*y2^52 + y0^16*y1^52*y2^52 - 2*y0^12*y1^56*y2^52 + y0^8*y1^60*y2^52 - 2*y0^60*y1^4*y2^56 - y0^56*y1^8*y2^56 - 2*y0^52*y1^12*y2^56 - y0^36*y1^28*y2^56 + 2*y0^32*y1^32*y2^56 - y0^28*y1^36*y2^56 - 2*y0^12*y1^52*y2^56 - y0^8*y1^56*y2^56 - 2*y0^4*y1^60*y2^56 + y0^60*y2^60 - 2*y0^56*y1^4*y2^60 + y0^52*y1^8*y2^60 + y0^40*y1^20*y2^60 + 2*y0^32*y1^28*y2^60 + 2*y0^28*y1^32*y2^60 + y0^20*y1^40*y2^60 + y0^8*y1^52*y2^60 - 2*y0^4*y1^56*y2^60 + y1^60*y2^60 - y0^40*y1^4*y2^76 - 2*y0^36*y1^8*y2^76 + 2*y0^32*y1^12*y2^76 + y0^28*y1^16*y2^76 + y0^16*y1^28*y2^76 + 2*y0^12*y1^32*y2^76 - 2*y0^8*y1^36*y2^76 - y0^4*y1^40*y2^76 + y0^40*y2^80 + 2*y0^36*y1^4*y2^80 - 2*y0^32*y1^8*y2^80 - y0^28*y1^12*y2^80 + y0^20*y1^20*y2^80 - y0^12*y1^28*y2^80 - 2*y0^8*y1^32*y2^80 + 2*y0^4*y1^36*y2^80 + y1^40*y2^80 + y0^20*y2^100 + y0^16*y1^4*y2^100 + y0^12*y1^8*y2^100 + y0^8*y1^12*y2^100 + y0^4*y1^16*y2^100 + y1^20*y2^100

        """
        if not ((isinstance(n,int) or isinstance(n,Integer)) and (isinstance(s,int) or isinstance(n,Integer))):
            raise TypeError("Arguments must be integers")
        if (n<1):
            raise ValueError("The first argument must be at least 1")
        if (s<0):
            raise ValueError("The second argument must be non-negative")
        if s>n:
            raise ValueError("Second argument must not exceed the first argument")
        if self._cache_.has_key((n,s)):
            return self._cache_[(n,s)]
        if n>1:
            P = PolynomialRing(self.K,n,'y')
        else:
            P = PolynomialRing(self.K,'y0')
        if s==0:
            Q=prod([self.V(k,P) for k in range(1,n+1)])**(self.p - 1)
            self._cache_[(n,0)] = Q
            return Q
        if n==s:
            self._cache_[(n,s)] = self.K(1)
            return self.K(1)
        Q = (self.__call__(n-1,s) * (self.V(n,P))**(self.p - 1)) + (P(self.__call__(n-1,s-1)))**(self.p)
        self._cache_[(n,s)] = Q
        return Q

    def V(self, k, P):
        """
        Compute [Pham]_'s `V_k` polynomials.

        See :mod:`~pGroupCohomology.dickson` for the theoretical background.

        INPUT:

        - ``k``, an integer
        - ``P``, a polynomial ring over ``GF(p)`` with at least ``k`` generators.

        EXAMPLES::

            sage: from pGroupCohomology.dickson import DICKSON
            sage: D3 = DICKSON(3)
            sage: D5 = DICKSON(5)
            sage: P = PolynomialRing(GF(3), 4, 'y')
            sage: D3.V(3, P)
            y0^6*y1^2*y2 + y0^4*y1^4*y2 + y0^2*y1^6*y2 - y0^6*y2^3 - y0^4*y1^2*y2^3 - y0^2*y1^4*y2^3 - y1^6*y2^3 + y2^9
            sage: D3.V(5, P)
            Traceback (most recent call last):
            ...
            ValueError: The first argument must not exceed the number of generators of the second argument
            sage: D5.V(3, P)
            Traceback (most recent call last):
            ...
            ValueError: The base ring of the second argument does not match Finite Field of size 5 over which self is defined

        """
        if k>P.ngens():
            raise ValueError("The first argument must not exceed the number of generators of the second argument")
        if self.K != P.base_ring():
            raise ValueError("The base ring of the second argument does not match %s over which self is defined"%self.K)
        if k==1:
            return P.gen(0)
        p = P.characteristic()
        return (P.gen(k-1))**(p**(k-1)) + add([P((-1)**(k-s-1)) * (P.gen(k-1))**(p**s)*self(k-1,s) for s in range(k-1)],P(0))

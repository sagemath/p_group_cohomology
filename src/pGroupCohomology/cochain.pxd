#*****************************************************************************
#
#    Cohomology Ring Elements and Maps
#
#    Copyright (C) 2009, 2015 Simon A. King <simon.king@uni-jena.de>
#
#  Distributed under the terms of the GNU General Public License (GPL),
#  version 2 or later (at your choice)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

#############################################################
## Cohomology Ring Elements
#############################################################

from sage.libs.modular_resolution cimport *
from sage.matrix.matrix_gfpn_dense cimport Matrix_gfpn_dense as MTX
from sage.libs.meataxe cimport *
from pGroupCohomology.resolution cimport *
from sage.structure.element cimport RingElement, ModuleElement, Element
from sage.rings.morphism cimport RingHomomorphism

####################################################################
####################################################################
## COCH and ChMap extension class
####################################################################
####################################################################

cdef class COCH(RingElement):
    cdef RESL Resl
    cdef int Deg
    cdef object Name
    cdef MTX Data
    cdef object Rdeg
    cdef object Ydeg
    cdef object _latex
    cdef object _sing_val
    cdef object _polyrep # tells whether "Name" provides a polynomial representation
    cdef void isubmul(self, COCH other, FEL c)
    cdef inline void set_mtx_globals(self)

cdef class YCOCH:
    cdef RESL _R
    cdef int _deg
    cdef list _Data
    cdef YCOCH _Cob
    cdef list _Constr

cdef class ChMap(RingHomomorphism):
    # We have a map from HSrc.Resl to HTgt.Resl --
    # and by consequence, we have a map of the cohomology ring
    # HTgt to the cohomology ring HSrc. So, Src and Tgt are switched.
    cdef object HSrc  # cohomology ring of group H
    cdef object HTgt  # cohomology ring of group G
    cdef RESL Src     # is HSrc.Resl
    cdef RESL Tgt     # is HTgt.Resl
    cdef long Deg     # maps from Src[n] to Tgt[n+Deg]
    cdef MTX GMap     # defines homomorphism kH -> kG
    cdef list Data    # List of MTX matrices describing chain map in each degree
                      # resp. a string pointing to a stored MTX matrix
    cdef object _name # name of the induced map
    cdef object _sing_val # cache for singular representation
    cdef str _sing_domain, _sing_codomain # name of singular rep of domain/codomain
    cdef dict _elim_cache # cache for a ring and an ideal that is used in elimination.

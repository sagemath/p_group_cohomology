#*****************************************************************************
#
#    Computing Minimal Free Resolutions of Finite p-Groups,
#    wrapping David J. Green's C-code
#
#    Copyright (C) 2009, 2015 Simon A. King  <simon.king@uni-jena.de>
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

from sage.libs.meataxe cimport *
from pGroupCohomology.resolution_bindings cimport *
from sage.matrix.matrix_gfpn_dense cimport Matrix_gfpn_dense as MTX

#########################################################
## Typen fuer Cohomologieberechnung
########################################################

cdef class G_ALG:
    cdef group_t *Data
    cdef object gstem
    cdef object groupname
    cdef object dependent

cdef class LIFTcontainer:
    cdef RESL Parent
    cdef dict Data

cdef class RESL:
    cdef __weakref__
    cdef resol_t *Data
    cdef list Diff   # list of differentials
    cdef G_ALG G_Alg
    cdef LIFTcontainer Lifts
    cdef dict Autolift
    cdef list Action
    cdef int _Action_saved
    cdef nRgs_t *nRgs  # points to Urbild Groebner basis
    cdef int ugb_deg   # if non-zero: What Urbild Groebner basis is loaded?
    cdef object gstem  # group identifier
    cdef object rstem  # resolution name
    cdef object gps_folder # folder for group data...
    cdef object res_folder # ... and resolution data
    cpdef tuple CochainToChainmap(self, long n, MTX Coc)

cdef MTX makeMTX(Matrix_t *Data)

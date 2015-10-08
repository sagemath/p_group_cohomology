#*****************************************************************************
#
#    Computing Minimal Free Resolutions of Finite p-Groups,
#    wrapping David J. Green's C-code
#
#    Copyright (C) 2009 Simon A. King  <simon.king@uni-jena.de>
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

from sage.libs.modular_resolution cimport *
from sage.matrix.matrix_gfpn_dense cimport Matrix_gfpn_dense as MTX

#########################################################
## Typen fuer Cohomologieberechnung
########################################################

cdef class G_ALG:
    cdef group_t *Data
    cdef object gstem
    cdef object dependent

cdef class LIFTcontainer:
    cdef RESL Parent
    cdef dict Data

cdef class RESL:
    cdef resol_t *Data
    cdef list Diff   # list of differentials
    cdef G_ALG G_Alg
    cdef LIFTcontainer Lifts  # in order to make doc tests
    cpdef list ToBeLifted      # in order to make doc tests
    cdef dict Autolift #cdef list Autolift
    cdef list Action
    cdef int _Action_saved
    cdef nRgs_t *nRgs  # points to Urbild Groebner basis
    cdef int ugb_deg   # if non-zero: What Urbild Groebner basis is loaded?
    cdef object gstem  # group name
    cdef object rstem  # resolution name
    cdef object gps_folder # folder for group data...
    cdef object res_folder # ... and resolution data

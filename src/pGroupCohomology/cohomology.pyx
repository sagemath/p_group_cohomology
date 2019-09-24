# -*- coding: utf-8 -*-

#*****************************************************************************
#
#    Cohomology Rings of Finite p-Groups
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

r"""
Modular Cohomology Rings of Finite `p`-Groups.

This module contains :class:`COHO`, that provides a framework for the
computation of the cohomology rings with coefficients in `\mathbb
F_p` for any finite `p`-group.  It is based on algorithms of David
Green and Dave Benson. See :mod:`pGroupCohomology` for an extensive
introduction. Note that :class:`~pGroupCohomology.modular_cohomology.MODCOHO`,
the basic class for the non prime power case, inherits from :class:`COHO`,
so that many methods of the former work in the non prime power case
as well.

AUTHORS:

- Simon King <simon.king@uni-jena.de>

"""

###########################################################
## Imports

from __future__ import print_function, absolute_import
import os, sys
if (2, 8) < sys.version_info:
    unicode = str
elif str == unicode:
    raise RuntimeError("<str> is <unicode>, which is a bug. Please recompile.")

from libc.string cimport memcpy

# Sage generalities
import sage
import sage.all
from sage.all import cached_method
from sage.all import cputime
from sage.all import walltime
from sage.all import dumps
from sage.all import loads
from sage.all import load
from sage.all import deepcopy
from sage.all import copy
from sage.all import add
from sage.all import mul
from sage.env import DOT_SAGE, SAGE_ROOT
from sage.misc.sageinspect import sage_getargspec
from sage.misc.lazy_attribute import lazy_attribute
from sage.docs.instancedoc import instancedoc
from sage.structure.richcmp import richcmp, richcmp_method, op_LT, op_NE, op_GT

# Sage rings etc.
from sage.all import Matrix
from sage.all import Ring
from sage.all import FiniteField as GF
from sage.all import PolynomialRing
from sage.all import ZZ
from sage.all import QQ
from sage.all import infinity
from sage.all import Integer
from sage.all import Algebras, CommutativeAlgebras
from sage.rings.polynomial.hilbert import hilbert_poincare_series, first_hilbert_series
from sage.interfaces.gap import GapElement
from sage.interfaces.singular import SingularElement

from pGroupCohomology.resolution_bindings cimport *
from sage.matrix.matrix_gfpn_dense cimport Matrix_gfpn_dense as MTX
from sage.matrix.matrix_gfpn_dense cimport new_mtx
from sage.libs.meataxe cimport *
from sage.cpython.getattr cimport AttributeErrorMessage
cdef AttributeErrorMessage default_filename_error_message = AttributeErrorMessage()
default_filename_error_message.name = '_default_filename'

from pGroupCohomology.auxiliaries import singular, _gap_eval_string, Failure

# pGroupCohomology Cython and Python types
from pGroupCohomology.resolution cimport RESL, G_ALG
from pGroupCohomology.cochain cimport COCH, ChMap
from pGroupCohomology.auxiliaries import coho_options, coho_logger, safe_save, _gap_reset_random_seed
from pGroupCohomology.resolution import resl_sparse_unpickle, makeGroupData, makeSpecialGroupData, gap
from pGroupCohomology.dickson import DICKSON
from pGroupCohomology.resolution cimport *

## CACHE for CohomologyHomsets
from weakref import WeakValueDictionary
from weakref import ref

##########################################################################
##########################################################################
###                                                                    ###
###         Pickling                                                   ###
###                                                                    ###
##########################################################################
##########################################################################

def COHO_unpickle(GroupKey, StateFile):
    """
    Unpickling of a cohomology ring.

    TESTS::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: H is loads(dumps(H)) # indirect doctest
        True

    """
    # Since the cache is indexed by (GroupKey, StateFile),
    # we first see if the cohomology ring is already there.
    # But there is a complication: Typically, we will move
    # data from potentially write protected local data
    # to a writeable workspace, by means of symbolic
    # links. Hence, the root of the statefile will point to
    # local sources, but we want it to point to the workspace.
    from pGroupCohomology import CohomologyRing
    _cache = CohomologyRing._cache
    if not StateFile.endswith('.sobj'):
        StateFile = StateFile+'.sobj'
    # corresponds to '/'.join(...).split('/')[:-3]) ::
    original_root = str(os.path.split(os.path.split(os.path.split(StateFile)[0])[0])[0])
    original_GStem = str(os.path.split(os.path.split(os.path.split(StateFile)[0])[0])[1]) # this is like StateFile.split('/')[-3]

    if original_root == '@user_db@': # Probably data have been moved.
        StateFile = os.path.join(coho_options.get('@use_this_root@') or COHO.workspace, original_GStem, "dat", os.path.split(StateFile)[1])
        root = coho_options.get('@use_this_root@') or COHO.workspace
    elif original_root == '@public_db@' and os.access(coho_options.get('@use_this_root@') or COHO.local_sources,os.W_OK):
        # realpath here?
        # We can use the local sources only if we have write permission
        StateFile = os.path.join(coho_options.get('@use_this_root@') or COHO.local_sources, original_GStem, "dat", os.path.split(StateFile)[1])
        root = coho_options.get('@use_this_root@') or COHO.local_sources
    elif os.path.realpath(StateFile) == os.path.realpath(os.path.join(coho_options.get('@use_this_root@') or COHO.workspace, original_GStem, "dat", os.path.split(StateFile)[1])):  # Moving to the workspace
        # Here it *is* realpath, because we want to know whether we have a symlink to the local sources
#~         coho_logger.warning("WARNING: Moving %r to the workspace", None, original_GStem)
        StateFile = os.path.join(coho_options.get('@use_this_root@') or COHO.workspace, original_GStem, "dat", os.path.split(StateFile)[1])
        root = coho_options.get('@use_this_root@') or COHO.workspace
    else:
        StateFile = os.path.join(coho_options.get('@use_this_root@') or original_root, original_GStem, "dat", os.path.split(StateFile)[1])
        root = coho_options.get('@use_this_root@') or original_root

    ## Now, StateFile should point to a file providing the state of the cohomology ring.
    ## If it doesn't, then we need to find out *after* loading
    second_cache_attempt = False
    if not '@newroot@' in coho_options:
        try:
            OUT = _cache.get((GroupKey,StateFile)) or _cache.get((GroupKey,StateFile[:-5]))
        except Exception as msg:
            coho_logger.error("The given group key seems to contain invalid data.", None, exc_info=1)
            coho_logger.warning("> Will try to recover later.",None)
            OUT = None
            second_cache_attempt = True
        if OUT is not None:
            if '@use_this_root@' in coho_options:
                del coho_options['@use_this_root@']
            return OUT
    OUT = COHO()
    # We need write access to the data. If we don't, it is needed
    # to move data to a different location -- *after* loading!
    coho_logger.debug( 'The state descriptor of the to-be-unpickled ring is expected to be provided at %r', None, StateFile)
    if not os.access(StateFile, os.W_OK):
        # realpath here?
        coho_logger.warning("WARNING: Files on disk have been moved or are not writeable.", None)
        coho_logger.warning("> Will try to recover later.", None)
        OUT.GStem = original_GStem
        try:
            q,n = [Integer(nb) for nb in original_GStem.split('gp')]
            OUT.setprop('_key', ((q,n),StateFile))
        except Exception:
            coho_logger.warning("> Group identifier not reconstructible from %s.", None, original_GStem)
        OUT.setprop('_need_new_root', coho_options.get('@use_this_root@',True))
        return OUT
    try:
        if StateFile.endswith('.sobj'):
            ST = load(StateFile)  # realpath here?
        else:
            ST = load(StateFile+'.sobj')  # realpath here?
    except (OSError, IOError),msg:
        coho_logger.error("Files on disk have been moved or are not readable.", None, exc_info=1)
        coho_logger.warning("> Will try to recover later.", None)
        OUT.setprop('_need_new_root', coho_options.get('@use_this_root@',True))
        if '@use_this_root@' in coho_options:
            del coho_options['@use_this_root@']
        coho_logger.warning("Trying to reconstruct cache key for %s", None, original_GStem)
        try:
            q,n = [Integer(nb) for nb in original_GStem.split('gp')]
            OUT.setprop('_key', ((q,n),StateFile))
        except Exception:
            coho_logger.warning("Y Group identifier not reconstructible from %s.", None, original_GStem)
        if second_cache_attempt:
            NewOUT = _cache.get(OUT._key)
            if NewOUT is not None:
                return NewOUT
        return OUT
    # Apparently the root given by StateFile is correct. So, use it,
    # regardless what the contents of the file pointed at by StateFile say!
    OUT.__setstate__(ST, newroot=coho_options.get('@use_this_root@') or root)
    if second_cache_attempt:
        NewOUT = _cache.get(OUT._key)
        if NewOUT is not None:
            return NewOUT
    _cache[GroupKey, StateFile] = OUT
    if '@use_this_root@' in coho_options:
        del coho_options['@use_this_root@']
    return OUT

############
# Ensure old pickles can be opened
from sage.structure.sage_object import register_unpickle_override
register_unpickle_override('pGroupCohomology.cohomology', 'COHO_unpickle', COHO_unpickle)
register_unpickle_override('sage.groups.modular_cohomology.cohomology', 'COHO_unpickle', COHO_unpickle)

###############
# GAP doesn't provide serialisation.
# Let's try to pickle via string representations.
class GapPickler(object):
    """
    This is an auxiliary class for pickling data involving the libgap interface.

    NOTE:

    The only purpose of an instance of this class is to carry
    a string that allows for reconstruction of an object in Gap.
    Applying :func:`pickle_gap_data` to data will work recursively
    on dictionaries, lists and tuples, and will return most other
    data unchanged. But when it encounters an object in Gap, it
    will try whether the object can be reconstructed from its string
    representation. If this is the case, then it returns an
    instance of :class:`GapPickler`. When :func:`unpickle_gap_data`
    is applied to the result, then it will create an object in Gap
    in lieue of any string that is stored in a :class:`GapPickler`
    class.

    EXAMPLES::

        sage: from pGroupCohomology.cohomology import GapPickler, unpickle_gap_data, pickle_gap_data
        sage: G = libgap.SmallGroup(8,3).IsomorphismPermGroup().Image()
        sage: D = {(1, G, "abc"):5}
        sage: unpickle_gap_data(pickle_gap_data(D)) == D  # indirect doctest
        True

    """
    gap = None
    def __init__(self, G):
        """
        INPUT:

        A string

        TESTS::

            sage: from pGroupCohomology.cohomology import GapPickler
            sage: G = GapPickler("15")  # indirect doctest
            sage: G.value
            '15'
            sage: loads(dumps(G)).value
            '15'

        """
        self.value = G
    def __reduce__(self):
        """
        TESTS::

            sage: from pGroupCohomology.cohomology import GapPickler
            sage: G = GapPickler("15")
            sage: G.value
            '15'
            sage: loads(dumps(G)).value   # indirect doctest
            '15'

        """
        return GapPickler, (self.value,)

def unpickle_gap_data(G):
    """
    Unpickle data involving objects in Gap.

    INPUT:

    - ``G``: Any object.

    NOTE:

    Applying :func:`pickle_gap_data` to data will work recursively on
    dictionaries, lists and tuples, and will return most other data
    unchanged. But when it encounters an object in Gap, it will try whether
    the object can be reconstructed from its string representation. If this is
    the case, then it returns an instance of :class:`GapPickler`. When this
    function is applied to the result, then it will create an object in Gap in
    lieue of any string that is stored in a :class:`GapPickler` class.

    EXAMPLES::

        sage: from pGroupCohomology.cohomology import GapPickler, unpickle_gap_data, pickle_gap_data
        sage: G = libgap.SmallGroup(8,3).IsomorphismPermGroup().Image()
        sage: D = {(1, G, "abc"):5}
        sage: unpickle_gap_data(pickle_gap_data(D)) == D
        True

    """
    if isinstance(G, (str, unicode)):
        return G
    if isinstance(G, GapPickler):
        from pGroupCohomology.auxiliaries import gap
        return gap.eval(G.value)
    if G == SingularElement:
        return SingularElement(None,None,None) # invalid element, on purpose
    if not isinstance(G, (dict,tuple,list)):
        return G
    if isinstance(G,dict):
        return dict((unpickle_gap_data(k), unpickle_gap_data(v)) for k,v in G.items())
    try:
        I = iter(G)
    except:
        return G
    return type(G)(unpickle_gap_data(X) for X in I)


def pickle_gap_data(G):
    """
    Pickle data involving objects in Gap.

    INPUT:

    ``G``: Any object.

    NOTE:

    Applying this function to data will work recursively on dictionaries,
    lists and tuples, and will return most other data unchanged. But when it
    encounters an object in Gap, it will try whether the object can be
    reconstructed from its string representation. If this is the case, then it
    returns an instance of :class:`GapPickler`. When :func:`unpickle_gap_data`
    is applied to the result, then it will create an object in Gap in lieue of
    any string that is stored in a :class:`GapPickler` class.

    EXAMPLES::

        sage: from pGroupCohomology.cohomology import GapPickler, unpickle_gap_data, pickle_gap_data
        sage: G = libgap.SmallGroup(8,3).IsomorphismPermGroup().Image()
        sage: D = {(1, G, "abc"):(5,G)}
        sage: unpickle_gap_data(pickle_gap_data(D)) == D
        True

    If Gap data can not be reconstructed from its string representation, a
    type error is raised::

        sage: G = libgap.SmallGroup(8,3)
        sage: D = {(1, G, "abc"):5}
        sage: pickle_gap_data(D)
        Traceback (most recent call last):
        ...
        TypeError: Can not pickle 'Group( [ f1, f2, f3 ] )'

    """
    if isinstance(G, (str, unicode)):
        return G
    if isinstance(G, SingularElement):
        # In previous Sage versions, most Singular elements pickled
        # as invalid objects. Our spkg could deal with these invalid
        # pickles. But Sage has now changed: Either they pickle
        # fine or they raise an error at *pickling* (not unpickling).
        # We thus return the type "SingularElement", unpickle it as invalid
        # object, and deal with it as we used to.
        return SingularElement
    if isinstance(G, GapElement):
        try:
            if G == G.parent()(G.String().sage()):
                return GapPickler(repr(G))
        except:
            raise TypeError("Can not pickle '{}'".format(G))
    from pGroupCohomology.auxiliaries import gap
    try:
        if G.parent() is gap:
            try:
                if G == gap.eval(G.String().sage()):
                    return GapPickler(G.String().sage())
            except:
                raise TypeError("Can not pickle '{}'".format(G))
    except AttributeError:
        pass
    if isinstance(G, dict):
        return dict((pickle_gap_data(k), pickle_gap_data(v)) for k,v in G.items())
    if isinstance(G, (list, tuple)):
        return type(G)(pickle_gap_data(X) for X in G)
    return G


####################################################################
## Auxiliary functions
####################################################################

def Mul(L,L0):
    """
    Compute the product of a list of elements, bracketed from the right.

    INPUT:

    - ``[L_1,...,L_n]``, a list of elements that can be multiplied
    - ``L_0``, an element

    OUTPUT:

    The product ``(L_1...*(L_{n-1}*(L_n*L_0))...)``

    EXAMPLES::

        sage: from pGroupCohomology.cohomology import Mul
        sage: M=Matrix(GF(5),[[1,2],[1,1]])
        sage: M1=Matrix(GF(5),[[1,2],[1,1]])
        sage: M2=Matrix(GF(5),[[1,3],[2,1]])
        sage: M3=Matrix(GF(5),[[1,4],[3,1]])
        sage: Mul([M1,M2],M3)
        [0 0]
        [0 1]
        sage: Mul([M2,M3],M1)
        [2 2]
        [4 4]
        sage: M2*M3*M1==Mul([M2,M3],M1)
        True

    """
    OUT = L0
    cdef int i
    cdef int m = len(L)
    for i from m > i >= 0:
        OUT=L[i]*OUT
    return OUT

def str2html(s,linelength=80):
    """
    HTML representation of a string representation of a polynomial.

    INPUT:

    - ``s``             - a string representing a polynomial
    - ``linelength=80`` - (optional) approximate line length of the output

    OUTPUT:

    HTML representation of the polynomial (string).
    If the polynomial is too long, there will be line breaks.

    NOTE:

    * It is expected that all exponents are positive integer numbers,
      written without signs.
    * The multiplication sign '*' is replaced by '&middot;'
    * In order to group the terms nicely, there is a small space around
      plus and minus signs.
    * There is an indentation after a line break.

    EXAMPLES::

        sage: from pGroupCohomology.cohomology import str2html
        sage: R.<x,y>=QQ[]
        sage: s=str(x^2+2*x*y+y^4)
        sage: s
        'y^4 + x^2 + 2*x*y'
        sage: str2html(s)
        '<nobr>y<sup>4 </sup>&thinsp;+&thinsp; x<sup>2 </sup>&thinsp;+&thinsp; 2&middot;x&middot;y</nobr>'

    If we choose a very small line length, the result breaks into several lines::

        sage: str2html(s,linelength=15)
        '<nobr>y<sup>4 </sup>&thinsp;+&thinsp; x<sup>2 </sup></nobr><br>&nbsp;&nbsp;<nobr>&thinsp;+&thinsp; 2&middot;x&middot;y</nobr>'

    """
    cdef list L=s.replace('+','\n+').replace('-','\n-').split('\n')
    cdef list O=['<nobr>']
    cdef list mon
    cdef int i, e
    cdef int lenL = len(L)
    lenO = 0
    for i from 0<=i<lenL:
        mon = []
        e=0
        s = L[i]
        for c in s:
            if c=='^':
                e+=1
                mon.append('<sup>')
            elif c=='*':
                if e:
                    e=0
                    mon.append('</sup>&middot;')
                else:
                    mon.append('&middot;')
            elif c==')':
                if e:
                    e=0
                    mon.append('</sup>)')
                else:
                    mon.append(')')
            elif c=='-':
                mon.append('&thinsp;&#8722;&thinsp;')
            elif c=='+':
                mon.append('&thinsp;+&thinsp;')
            else:
                mon.append(c)
        if e:
            mon.append('</sup>')
        #mon.append('</nobr>')
        if lenO==0:
            O.extend(mon)
            lenO=len(mon)
        elif ((lenO+len(mon)>linelength) and (linelength>0)):
            O.append('</nobr><br>&nbsp;&nbsp;<nobr>')
            O.extend(mon)
            lenO=len(mon)
        else:
            O.extend(mon)
            lenO+=len(mon)
    O.append('</nobr>')
    return ''.join(O)

def HV2Poly(L):
    """
    Translate a list of integers into a univariate polynomial, using the given integers as coefficients.

    INPUT:

    ``L``: a list of integers

    OUTPUT:

    A univariate polynomials with coefficients given by ``L``

    EXAMPLES::

        sage: from pGroupCohomology.cohomology import HV2Poly
        sage: HV2Poly([3,2,4])
        4*t^2 + 2*t + 3

    """
    R = PolynomialRing(QQ,'t')
    t = R('t')
    return sum([L[i]*t**i for i in range(len(L))])

cdef Matrix_t *nil_preimages(list Maps, list Cochains) except NULL:
    """
    Linear combinations of cochains simultaneously restricting to the nil radical.

    INPUT:

    - ``Maps`` -- list of restriction maps from a group to elementary abelian (!) subgroups
    - ``Cochains`` -- list of cochains of the group

    OUTPUT:

    A pointer to the underlying data of a MeatAxe matrix whose rows define
    linear combinations of the given cochains restricting to the nil radical
    under all given restriction maps.

    ASSUMPTIONS:

    All cochains are of the same degree and belong to the same cohomology
    ring, that is the domain of all restriction maps. The codomains of all
    restriction maps are cohomology rings of elementary abelian groups.

    WARNING:

    The list ``Cochains`` is altered by this function. So, make a copy if
    you need to re-use the list.
    """
    cdef COCH imC
    cdef ChMap Rest
    cdef list ImageList = []
    cdef size_t LongRowSize = 0
    cdef int Field
    assert Maps and Cochains
    C = Cochains.pop(0)
    for Rest in Maps:
        imC = Rest(C)
        ImageList.append(imC)
        LongRowSize += imC.Data.Data.RowSize # That's number of bytes in memory
    cdef int d = imC.Deg
    Field = imC.Data.Data.Field
    cdef Matrix_t *Images = MatAlloc(Field, len(Cochains)+1, LongRowSize*MPB)
    if Images == NULL:
        raise MemoryError("Error allocating a matrix")
    cdef PTR col_head
    cdef PTR p_imC = Images.Data
    # Create matrix given by the images
    for imC in ImageList:
        memcpy(p_imC, imC.Data.Data.Data, imC.Data.Data.RowSize)
        p_imC += imC.Data.Data.RowSize
    for C in Cochains:
        for Rest in Maps:
            imC = Rest(C)
            memcpy(p_imC, imC.Data.Data.Data, imC.Data.Data.RowSize)
            p_imC += imC.Data.Data.RowSize
    # nil radical for elementary abelian groups is trivial
    if Field==2:
        return MatNullSpace__(Images)

    # Reduce modulo nilradical
    col_head = Images.Data
    FfSetNoc(Images.Noc)
    assert FfCurrentRowSize == LongRowSize, "Conflicting row sizes {} vs {}".format(FfCurrentRowSize, LongRowSize)
    cdef MTX nil_basis
    cdef int piv_j_imC
    cdef int piv_j_nilbasis
    cdef FEL piv_f_imC
    cdef FEL piv_f_nilbasis
    cdef int row_nr, k
    cdef PTR p_nilbasis
    cdef FEL mark_imC
    cdef tuple pivots_nilbasis
    for imC in ImageList:
        # The data of imC is already taken care of.
        # Now, we are merely interested in information
        # on sizes, to control the computation
        ElAb = imC._parent
        if not ElAb.NilBasis[d]:
            col_head += imC.Data.Data.RowSize
            continue
        if isinstance(ElAb.NilBasis[d], MTX):
            nil_basis = ElAb.NilBasis[d]
        else:
            nil_basis = new_mtx(rawMatrix(Field,ElAb.NilBasis[d]), None)
            nil_basis.echelonize()
            ElAb.NilBasis[d] = nil_basis
        pivots_nilbasis = nil_basis.pivots()
        FfSetNoc(imC.Data.Data.Noc)
        p_imC = col_head
        for row_nr in range(Images.Nor):
            piv_j_imC = FfFindPivot(p_imC, &piv_f_imC)
            if piv_j_imC < 0:
                p_imC += LongRowSize
                continue
            p_nilbasis = nil_basis.Data.Data
            for k in range(len(pivots_nilbasis)):
                piv_j_nilbasis = pivots_nilbasis[k]
                if piv_j_imC > piv_j_nilbasis:
                    p_nilbasis += FfCurrentRowSize
                    continue
                mark_imC = FfExtract(p_imC, piv_j_nilbasis)
                if mark_imC == FF_ZERO:
                    p_nilbasis += FfCurrentRowSize
                    continue
                # M = M - B[k]*M[0,jB]/fB, which in boilerplate expands to this:
                piv_f_nilbasis = FfExtract(p_nilbasis, piv_j_nilbasis)
                assert piv_f_nilbasis != FF_ZERO, "Zero pivot"
                FfAddMulRow(p_imC, p_nilbasis, <FEL>mtx_taddinv[<int><unsigned char>(mtx_tmult[<int><unsigned char>mark_imC][<int><unsigned char>(mtx_tmultinv[<int><unsigned char>piv_f_nilbasis])])])
                piv_j_imC = FfFindPivot(p_imC, &piv_f_imC)
                if piv_j_imC < 0:
                    break
                p_nilbasis += FfCurrentRowSize
            p_imC += LongRowSize
        col_head += imC.Data.Data.RowSize
    return MatNullSpace__(Images)

#############################
## Tools to enumerate filter regular parameters

def explore_one_parameter(Id, L0, p, BreakPoint = None, regularity=0, H1 = None, is_monomial = True):
    r"""
    Find a parameter for the quotient ring given by an ideal.

    INPUT:

    - ``Id`` -- Ideal in a graded commutative ring of prime characteristic `p`.
              Must be a Groebner basis.
    - ``L0``  -- a list of homogeneous elements (given by strings) of the same degree.
    - ``p``  -- a prime.
    - ``BreakPoint`` -- (optional integer or infinity) test at most that many candidates
                      for a parameter (default: infinity).
    - ``regularity`` -- (optional int, default ``0``) If ``1`` (not default), find
                      a parameter that is filter regular modulo ``Id``.
                      If ``2``, find a parameter that is regular modulo ``Id``.
    - ``H1`` -- (optional) the Hilbert Poincaré series of ``Id``.
    - ``is_monomial`` -- (optional) whether the element in ``L0`` are monomials.

    OUTPUT:

    - 1. An element `v` in Singular that lowers the dimension of ``Id`` by one (aka
         "parameter" for ``Id``),
      2. A tuple of integers, namely the list of coefficients that defines ``v`` as
         linear combination of the monomials in ``L``.
      3. The return value of ``is_filter_regular``, if ``regularity==1``,
         or ``[]``.
    - ``False, False, []``, if no linear combination of elements of ``L`` provides a
      parameter for ``Id``, or
    - ``None, None, []``, if the search for a parameter was stopped since the number
      of candidates exceeded ``BreakPoint``.

    NOTE:

    If `is_monomial` is true, then only lineare combinations of the standard monomials
    in ``L0`` relative to ``Id`` will be considered.

    TESTS::

        sage: from pGroupCohomology import CohomologyRing
        sage: from pGroupCohomology.cohomology import explore_one_parameter
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(32,33)
        sage: H.make()
        sage: H.set_ring()
        sage: Id = H.relation_ideal()
        sage: L = H.standard_monomials(3)
        sage: explore_one_parameter(Id,L,2)
        (b_1_0^3, (0, 0, 0, 0, 0, 0, 0, 1, 0, 0), [])
        sage: explore_one_parameter(Id,L,2, regularity=1)
        (False, False, [])
        sage: Id.dim()
        3
        sage: Id.std('b_1_0^3').dim()
        2

    Now, we use two non-commutative examples. We do not need to
    distinguish Singular versions 3-1-1 and older versions, since in this
    example there are regular respectively filter-regular parameters.
    ::

        sage: H = CohomologyRing(27,4)
        sage: H.make()
        sage: H.dimension()
        2
        sage: H.depth()
        1
        sage: H.set_ring()
        sage: Id = H.relation_ideal()
        sage: L = H.standard_monomials(6)
        sage: explore_one_parameter(Id,L,3,regularity=2)
        (c_6_2, (0, 0, 0, 0, 0, 1), [0])
        sage: Id = Id.std('c_6_2')
        sage: L = H.standard_monomials(2)
        sage: explore_one_parameter(Id,L,3)
        (b_2_1, (0, 0, 1, 0), [])
        sage: explore_one_parameter(Id,L,3,regularity=1)
        (b_2_1, (0, 0, 1, 0), [0, 1, 1, 1, 1])
        sage: explore_one_parameter(Id,L,3,regularity=2)
        (False, False, [])

    """
    cdef list CE, CO
    cdef list Kicked
    cdef tuple EssT, OptT
    cdef ssize_t j
    singular = Id._check_valid()
    if BreakPoint is None:
        from sage.all import Infinity
        BreakPoint = Infinity
    from sage.all import cartesian_product_iterator
    dgb = singular.eval('degBound')
    singular.eval('degBound=0')
    d0 = int(getattr(Id,'dim' if p==2 else 'GKdim')())
    if d0 <= 0:
        return '0',[0]*len(L0),[]
    cdef size_t lenL, lenEss, lenOpt, total
    cdef list L = []
    cdef list nonstd = []
    if is_monomial:
        cmd = '{}==NF({},'+Id.name()+')'
        for j,s in enumerate(L0):
            if singular.eval(cmd.format(s,s))!='0':
                L.append(s)
                nonstd.append(j)
    else:
        L = list(L0)
    lenL = len(L)
    if lenL==0:
        return False,False,[]
    Optional  = singular.ideal(0)
    if regularity:
        Optional[lenL] = 0
    if lenL<50:
        Essential = singular.ideal(L)
    else:
        Essential = singular.ideal(0)
        Essential[lenL] = 0
        for j in range(lenL):#from 0<=j<lenL:
            Essential[j+1] = L[j]
    counter = 0
    Poly_tmp = singular.poly(0)

    try:
        if (int(singular('%s(std(%s,%s))'%('dim' if p==2 else 'GKdim',Id.name(),Essential.name()))) >= d0):
            return False,False,None
        # Detect the monomials that *must* appear in a parameter.
        Kicked = []
        for j in range(1,lenL+1):#from 1 <=j <=lenL:
            singular.eval('%s=%s[%d]'%(Poly_tmp.name(),Essential.name(),j))
            singular.eval('%s[%d]=0'%(Essential.name(),j))
            # std(...,...) was buggy at some point
            if int(singular('%s(std(%s,%s))'%('dim' if p==2 else 'GKdim', Id.name(),Essential.name()))) >= d0:
                singular.eval('%s[%d]=%s'%(Essential.name(),j,Poly_tmp.name()))
            else:
                Kicked.append(j-1)
                if regularity:
                    coho_logger.debug("%s will be optional", "explore_one_parameter", singular.eval(Poly_tmp.name()))
                    singular.eval('%s[%d]=%s'%(Optional.name(),j,Poly_tmp.name()))
        singular.eval('%s=simplify(%s,2)'%(Essential.name(),Essential.name()))
        singular.eval('%s=simplify(%s,2)'%(Optional.name(),Optional.name()))
        if singular.eval('%s[1]'%Essential.name()) == '0':
            return False, False, []
        lenEss = int(singular.eval('size(%s)'%Essential.name()))
        if singular.eval('%s[1]'%Optional.name()) == '0':
            lenOpt = 0
        else:
            lenOpt = int(singular.eval('size(%s)'%Optional.name()))
        total = (p-1)**lenEss*p**lenOpt
        if lenOpt:
            coho_logger.info('%d = (%d-1)^%d*%d^%d parameter candidates',"explore_one_parameter", total, p, lenEss , p, lenOpt)
        else:
            coho_logger.info('%d = (%d-1)^%d parameter candidates',"explore_one_parameter", total, p, lenEss)
        if BreakPoint < total:
            coho_logger.info('Will break after %d candidates', "explore_one_parameter", BreakPoint)
        got_something = False
        from sage.all import add
        # we kicked stuff, so, we don't need coefficient zero
        EssIter = cartesian_product_iterator([range(1,p)]*lenEss)
        reg_vec = []
        coho_logger.debug('Computing first Hilbert Poincaré series of start ideal', "explore_one_parameter")
        if H1 is None:
            H1 = first_hilbert_series(Id)
        for EssT in EssIter:
            v  = singular.intmat(singular.intvec(*EssT),lenEss,1)
            xp = Essential*v
            OptIter = cartesian_product_iterator([range(p)]*lenOpt)
            for OptT in OptIter:
                if OptT:
                    v  = singular.intmat(singular.intvec(*OptT),lenOpt,1)
                    vp = xp + Optional*v
                else:
                    vp = xp
                counter +=1
                # Did we find something?
                Idvp = Id.std(vp.name()+'[1][1]')
                if int(singular.eval('%s(%s)'%('dim' if p==2 else 'GKdim', Idvp.name())))<d0:
                    #     getattr(Id.std(vp.name()+'[1][1]'),'dim' if p==2 else 'GKdim')()) < d0:
                    coho_logger.info("We found a parameter.", "explore_one_parameter")
                    coho_logger.debug("> %r (%d/%d)", "explore_one_parameter", vp, counter, total)
                    if regularity==1:
                        reg_vec_tmp = is_filter_regular(Id, vp, H1, Idvp)
                        if reg_vec_tmp:
                            coho_logger.info('> It is filter-regular.', "explore_one_parameter")
                            got_something = True
                            reg_vec = reg_vec_tmp
                            break
                        else:
                            coho_logger.info('> But it is not filter-regular.', "explore_one_parameter")
                    elif regularity>1:
                        reg_vec_tmp = is_filter_regular(Id, vp, H1, Idvp)
                        if reg_vec_tmp == [0]:
                            coho_logger.info('> It is regular.', "explore_one_parameter")
                            got_something = True
                            reg_vec = reg_vec_tmp
                            break
                        else:
                            coho_logger.info('> But it is not regular.', "explore_one_parameter")
                    else:
                        got_something = True
                        break
                if counter >= BreakPoint:
                    singular.eval('degBound='+dgb)
                    return None, None, []
            if got_something:
                break
        if not got_something: # Means: We didn't hit the breakpoint, so, it is proved that there is nothing
            singular.eval('degBound='+dgb)
            return False,False,[]
        # get the coefficients related with the original list of monomials
        if not Kicked:
            singular.eval('degBound='+dgb)
            return vp[1][1], EssT, reg_vec
        CE = list(EssT)
        CO = list(OptT)
        Coef = []
        for j in range(len(L)):
            if j in Kicked:
                if regularity:
                    Coef.append(CO.pop(0))
                else:
                    Coef.append(0)
            else:
                Coef.append(CE.pop(0))
        for j in nonstd:
            Coef.insert(j,0)
        singular.eval('degBound='+dgb)
        return vp[1][1],tuple(Coef),reg_vec
    except BaseException:
        try:
            singular.eval('degBound='+dgb)
        except:
            pass
        raise

def FilterDegreeType(dv, rt):
    """
    Compute the filter degree type.

    INPUT:

    - ``d`` - list of degrees (`n` integers) of a filter regular
      homogeneous system of parameters, and
    - ``r`` - the 'raw filter degree type' (list of `n+1` integers)
      of these parameters.

    OUTPUT:

    The filter degree type, a list of integers

    EXAMPLES::

        sage: from pGroupCohomology.cohomology import FilterDegreeType
        sage: d=[8,4,6,4]
        sage: r=[-1,4,7,14,18]
        sage: FilterDegreeType(d,r)
        [-1, -2, -3, -4, -4]
        sage: d=[8,4,6,3]
        sage: FilterDegreeType(d,r)
        [-1, -2, -3, -3, -3]

    """
    cdef int i,j
    if not (isinstance(dv,list) and isinstance(rt,list)):
        raise TypeError("arguments must be lists of integers")
    if not (len(rt)==len(dv)+1):
        raise ValueError("length of second arguments must be length of first argument plus one")
    # start with the smallest possible sequence
    ft = [-k for k in range(1,len(rt)+1)]
    i = 0
    while(i<len(ft)):
        # if the current index is too small,
        # given the raw filter degree type, raise it
        if sum(dv[:i])+ft[i] < rt[i]:
            ft[i]=ft[i]+1
            i=0
        elif (i>0) and (ft[i]>ft[i-1]):
            # if the sequence fails to be admissible
            # at position i-1,i: Cure it!
            ft[i-1]=ft[i-1]+1
            i=0
        elif (i>0) and (ft[i]<ft[i-1]-1):
            ft[i]=ft[i]+1
            i=0
        else:
            i+=1
    return ft

def is_filter_regular(I, f, H1=None, I2=None):
    r"""
    Test if `f` is filter-regular with respect to `I`.

    INPUT:

    - `I`, complete standard basis of a weighted homogeneous ideal;
      Singular element or string.
    - `f`, weighted homogeneous element; Singular element or string.
    - `H1` (optional) -- first Hilbert Poincaré series of `I`, if that has already been computed
    - `I2` (optional) -- ``std(I,f)``, if that has already been computed

    OUTPUT:

    Finite list of vector space dimensions of the annulator of `f` with
    respect to `I`, i.e., `\{p|f\cdot p\in I\}`, or ``False`` if the annulator
    is not finite dimensional.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: from pGroupCohomology.cohomology import is_filter_regular
        sage: CohomologyRing.doctest_setup()
        sage: H = CohomologyRing(64, 23, from_scratch=True)
        sage: H.make(4)
        sage: F = H.filter_regular_parameters()
        sage: is_filter_regular(H.relation_ideal(), F[0])
        False
        sage: is_filter_regular(H.relation_ideal().std(F[1]), F[0])
        [0]
        sage: is_filter_regular(H.relation_ideal().std(F[0]).std(F[1]).std(F[2]), F[3])
        False
        sage: H.make()
        sage: is_filter_regular(H.relation_ideal().std(F[0]).std(F[1]).std(F[2]), F[3])
        [0, 2, 1, 1, 2]

    """
    if isinstance(I, (str, unicode)):
        S = singular
        nI = str(I)
        I = S.ideal(nI)
    else:
        S = I._check_valid()
        nI = I.name()
    if isinstance(f, (str, unicode)):
        nf = str(f)
        f = S(nf)
    else:
        assert f.parent() is S
        nf = f.name()
    dv = [Integer(d) for d in S('ringweights(basering)')]
    if I2 is None:
        dgb = S.eval('degBound')
        S.eval('degBound=0')
        I2 = singular('std(%s,%s)'%(nI,nf))
        S.eval('degBound='+dgb)
    H2 = first_hilbert_series(I2)
    if H1 is None:
        H1 = first_hilbert_series(I)
    P = H1.parent()
    t = P.gen()
    Den = P.prod([(1-t**d) for d in dv])
    d = Integer(S.eval('deg(%s)'%nf))
    # Hilbert series of the annulator:
    HA = ((H2-H1)/t**d + H1)/Den
    if HA == 0:
        return [0]
    if HA.denominator().degree():
        return False
    return HA.numerator().list()

def is_filter_regular_parameter_system(I, FRS):
    r"""
    Test if `FRS` is a filter-regular parameter system with respect to `I`.

    INPUT:

    - `I`, complete standard basis of a weighted homogeneous ideal;
      Singular element or string.
    - `FRS`, an iterable of Singular elements or strings representing weighted
      homogeneous elements.

    OUTPUT:

    ``False``, or the raw filter degree type, which is a list of ``len(FRS)+1`` lists of
    integers: The `i`-th list provides the vector space dimensions of each degree
    layer of the annulator of the `i`-th element of `FRS` modulo the preceeding elements;
    the last list provides the vector space dimensions of each degree layer of the
    quotient modulo `FRS`. If some annulator or the final quotient is not finite
    dimensional, then ``False`` is returned.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()
        sage: H = CohomologyRing(64, 23, from_scratch=True)
        sage: H.make(4)

    There exists a set of elements of degree at most four that are
    guaranteed to form a filter regular system of parameters of the
    cohomology ring::

        sage: F = H.filter_regular_parameters()
        sage: F
        ['c_2_4', 'c_4_14', 'b_2_3+b_2_2+b_2_1', 'b_3_6']

    However, they are not filter regular in the ring approximations out to
    degree 4 or 7. They are filter regular in the ring approximation out
    to degree 8, and this is in fact the complete cohomology ring::

        sage: from pGroupCohomology.cohomology import is_filter_regular_parameter_system
        sage: is_filter_regular_parameter_system(H.relation_ideal(), F)
        False
        sage: H.make(7)
        sage: is_filter_regular_parameter_system(H.relation_ideal(), F)
        False
        sage: H.make(8)
        sage: is_filter_regular_parameter_system(H.relation_ideal(), F)
        [[0], [0], [0], [0, 2, 1, 1, 2], [1, 2, 3, 4, 5, 2, 0, 1]]
        sage: H.completed
        True

    """
    if isinstance(I, (str, unicode)):
        S = singular
        I0 = S.ideal(I)
    else:
        S = I._check_valid()
        I0 = I
    frs = []
    for f in FRS:
        if isinstance(f, (str, unicode)):
            frs.append(S(f))
        else:
            assert f.parent() is S
            frs.append(f)
    dv = [Integer(d) for d in S('ringweights(basering)')]
    dgb = S.eval('degBound')
    S.eval('degBound=0')
    H0 = first_hilbert_series(I0)
    P = H0.parent()
    t = P.gen()
    Den = P.prod([(1-t**d) for d in dv])
    rfdt = []
    try:
        for f in frs:
            coho_logger.debug('Parameter %r', "Study filter regular sequence", f)
            nf = f.name()
            I1 = I0.std(f)
            coho_logger.debug('  quotient computed', "Study filter regular sequence")
            H1 = first_hilbert_series(I1)
            coho_logger.debug('  Hilbert series computed', "Study filter regular sequence")
            d = Integer(S.eval('deg(%s)'%nf))
            HA = ((H1-H0)/t**d + H0)/Den
            if HA == 0:
                rfdt.append([0])
            elif HA.denominator().degree():
                coho_logger.debug('Sequence is not filter regular', "Study filter regular sequence")
                return False
            else:
                rfdt.append(HA.numerator().list())
            I0 = I1
            H0 = H1
        # Now, I1 is the final quotient, and H1 is its first Hilbert series
        HA = H1/Den
        if HA == 0:
            rfdt.append([0])
        elif HA.denominator().degree():
            coho_logger.debug('Sequence is not filter regular', "Study filter regular sequence")
            return False
        else:
            rfdt.append(HA.numerator().list())
        coho_logger.debug('Sequence is filter regular', "Study filter regular sequence")
        return rfdt
    finally:
        try:
            S.eval('degBound='+dgb)
        except:
            pass

####################################################################
####################################################################
## The COHO extension class
####################################################################
####################################################################

#################
## An auxiliary class used to provide a distinct number
## to each COHO instance, so that data in the singular
## interface can be told apart

class COHO_prefix:
    """
    COHO_prefix()() returns the next safe prefix.

    Used for naming Singular interface data of a :class:`~pGroupCohomology.cohomology.COHO` instance.

    TESTS::

        sage: from pGroupCohomology.cohomology import COHO_prefix
        sage: COHO_prefix.instance=0  # initialization, for avoiding other doc tests to interfere
        sage: COHO_prefix()()
        'COHO1'
        sage: COHO_prefix()()
        'COHO2'

        """
    instance = 0

    def __init__(self):
        """
        TESTS::

            sage: from pGroupCohomology.cohomology import COHO_prefix
            sage: COHO_prefix.instance=0  # initialization, for avoiding other doc tests to interfere
            sage: C = COHO_prefix()  # indirect doctest
            sage: COHO_prefix.instance
            1

        """
        self.__safe_for_unpickling__ = True # don't know if this is needed
        self.__class__.instance = self.__class__.instance + 1

    def __call__(self):
        """
        Provide the next unused prefix for internal use in cohomology computations.

        TESTS::

            sage: from pGroupCohomology.cohomology import COHO_prefix
            sage: COHO_prefix.instance=0  # initialization, for avoiding other doc tests to interfere
            sage: COHO_prefix()()      # indirect doctest
            'COHO1'
            sage: COHO_prefix()()
            'COHO2'

        """
        return 'COHO%d'%(self.__class__.instance)

########################################
## An auxiliary class for deletion of
## the Ring's data in the Singular interface.
## This is since COHO must not have a __del__
## method since this would prevent COHO from
## being garbage collected.

class COHO_Terminator:
    """
    Remove cohomology data from the Singular interface.

    This is an auxiliary class, with the purpose to remove all data
    from the Singualar interface that are related with a certain
    cohomology ring.

    Each cohomology ring has a member that is an instance of this
    class. Hence, when the ring is deleted then the member's
    ``__del__`` method is called, which clears the Singular interface.

    The somewhat hidden reason for introducing an auxiliar class is
    that circular references of cohomology rings can not be avoided;
    hence, if they had a ``__del__`` method, they could never be
    garbage collected (the reason is described in the `Python
    references
    <http://www.python.org/doc/2.6.2/reference/datamodel.html#object.__del__>`_);
    hence, we moved the ``__del__`` method to here.

    TESTS::

        sage: from pGroupCohomology.cohomology import COHO_Terminator
        sage: T = COHO_Terminator(singular(1), 'MyPrefix')
        sage: singular.eval('ring MyPrefixR = 0,(a,b,c),dp')
        ''
        sage: print(singular.eval('MyPrefixR'))
        // coefficients: QQ
        // number of vars : 3
        //        block   1 : ordering dp
        //                  : names    a b c
        //        block   2 : ordering C
        sage: singular.eval('ideal MyPrefixI = a^2,b^2,c')
        ''
        sage: print(singular.eval('MyPrefixI'))
        MyPrefixI[1]=a2
        MyPrefixI[2]=b2
        MyPrefixI[3]=c
        sage: del T
        sage: singular('MyPrefixI')
        Traceback (most recent call last):
        ...
        TypeError: Singular error:
           ? `MyPrefixI` is undefined
           ? error occurred in ...

    """
    def __init__(self, S, prefix):
        """
        TESTS::

            sage: from pGroupCohomology.cohomology import COHO_Terminator
            sage: T = COHO_Terminator(singular,'MyPrefix')    # indirect doctest
            sage: T._S is singular
            True
            sage: T._prefix
            'MyPrefix'

        """
        self._S = S
        self._prefix = prefix
        self._l = len(prefix)
    def __del__(self):
        """
        This del-method kills all elements in the interface ``self._S`` whose name starts with ``self._prefix``.

        TESTS::

            sage: from pGroupCohomology.cohomology import COHO_Terminator
            sage: T = COHO_Terminator(singular(1), 'MyPrefix')
            sage: singular.eval('ring MyPrefixR = 0,(a,b,c),dp')
            ''
            sage: print(singular.eval('MyPrefixR'))
            // coefficients: QQ
            // number of vars : 3
            //        block   1 : ordering dp
            //                  : names    a b c
            //        block   2 : ordering C
            sage: singular.eval('ideal MyPrefixI = a^2,b^2,c')
            ''
            sage: print(singular.eval('MyPrefixI'))
            MyPrefixI[1]=a2
            MyPrefixI[2]=b2
            MyPrefixI[3]=c
            sage: del T      # indirect doctest
            sage: singular('MyPrefixI')
            Traceback (most recent call last):
            ...
            TypeError: Singular error:
               ? `MyPrefixI` is undefined
               ? error occurred in ...

        """
        cdef list ITEM
        if not hasattr(self._S,'_check_valid'):
            return
        try:
            S = self._S._check_valid()
        except ValueError:
            return
        try:
            L = S.eval('listvar(ring)').split('//')[1:]
        except TypeError:
            L = []
        for X in L:
            ITEM = X.strip().split(' ')
            if len(ITEM):
                n = ITEM[0]
                # Singular data must be deleted if
                # their name begins with the right prefix.
                # But this is not enough: COHO11r(1) must not
                # be deleted when deleting COHO1...
                # But our data in Singular are named with
                # prefix + something that starts with no digit.
                if n.startswith(self._prefix) and (not n[self._l].isdigit()):
                    S.eval('kill '+n)
        try:
            L = S.eval('listvar(intmat)').split('//')[1:]
        except TypeError:
            L = []
        for X in L:
            ITEM = X.strip().split(' ')
            if len(ITEM):
                n = ITEM[0]
                if n.startswith(self._prefix) and (not n[self._l].isdigit()):
                    S.eval('kill '+n)
        if hasattr(self._S,'_name'):
            if S('defined('+self._S._name+')'):
                S.eval('kill '+self._S._name)

#################
## Some decorators that automate caching

from sage.misc.sageinspect import __embedded_position_re, _sage_getdoc_unformatted, sage_getargspec

def _split_embedding_info(obj):
    """
    Extract information that is embedded in the docstring of an object.

    EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cohomology import _split_embedding_info
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,67)
            sage: print(_split_embedding_info(H.restriction_maps()[2][1].preimage)[0])
            ChMap.preimage(self, Item=None, Id=None)

    """
    docstring = _sage_getdoc_unformatted(obj)
    try:
        res = __embedded_position_re.search(docstring)
    except TypeError:
        res = None
    if res is not None:
        start_orig_doc = docstring.find(os.linesep, res.start())+1
        return docstring[:start_orig_doc], docstring[start_orig_doc:].strip(os.linesep)
    # Test if the first docstring line provides information on the argspec
    docstring = docstring.strip(os.linesep)
    name = getattr(obj, '__name__', '')
    if not name:
        return '', docstring
    cls = getattr(obj, 'im_class', None) or getattr(obj, '__objclass__', None)
    clsname = getattr(cls, '__name__', None)
    if clsname is None:
        cls_obj = None
    else:
        cls_obj = '{}.{}'.format(clsname, name)
    firstline_seconds = docstring.split(os.linesep,1)
    if len(firstline_seconds) == 1:
        firstline = firstline_seconds[0]
        seconds = ''
    else:
        firstline, seconds = firstline_seconds
    if cls_obj is not None:
        if not firstline.startswith(cls_obj):
            return '', docstring
    else:
        cls_obj = name
    preamble_argstring = firstline.split(cls_obj,1)
    if len(preamble_argstring) == 1:
        return '', docstring
    if not (preamble_argstring[1].startswith('(') and preamble_argstring[1].endswith(')')):
        return '', docstring
    return firstline+os.linesep, seconds.strip(os.linesep)

class permanent_result(object):
    """
    Cache a method and reconstruct data in interfaces when needed.

    NOTE:

    The value ``None`` will not be cached.

    The decorator only works if it is used for a method of an instance ``X``
    that either has an attribute ``_decorator_cache`` (a dictionary) or allows
    its creation.

    If the result is in the Singular interface and Singular
    crashes, then sometimes it is necessary for reconstruction of data
    that ``X`` has an attribute ``GenS`` whose parent is Singular, and
    it needs to have an interpretation in Singular.

    If the method arguments are in an interface then it is imperative
    that they can be reconstructed from its string representation.

    If the method raised a ``KeyboardInterrupt``, this is cached as well,
    but a new computation can be attempted with the optional argument
    ``forced`` added to the method's arguments. Note that ``forced``
    is *not* passed as an argument to the underlying function.

    NOTE:

    Sometimes, the results stored with this decorator involve data
    defined in GAP. GAP does by default not provide data serialisation,
    and even GAP's optional IO package would only write data directly
    to a file object, which is awkward when otherwise relying on Python's
    pickling protocols. However, often a GAP object can be reconstructed
    from its string representation, and that's what we are using here.

    ASSUMPTION:

    If the result is in the Singular interface, it is assumed that
    ``singular(X).set_ring()`` is possible and that the result either
    belongs to this ring or is ring independent.

    EXAMPLES:

    This decorator is designed for use in cohomology rings, but the
    examples show that it works more generally::

        sage: from pGroupCohomology.cohomology import permanent_result
        sage: class FOO:
        ....:   def __init__(self,R):
        ....:       self.R = R
        ....:       self.GenS = singular.int(1)
        ....:   def _singular_(self,S):
        ....:       return S(self.R)
        ....:   @permanent_result
        ....:   def bar(self, G):
        ....:       '''
        ....:       Here is the documentation.
        ....:       '''
        ....:       singular(self).set_ring()
        ....:       print('Group of order',G.Order())
        ....:       return singular.maxideal(G.Order())
        sage: R.<x,y> = QQ[]
        sage: f = FOO(R)
        sage: G2 = libgap.eval('Group( [ (1,2) ] )')
        sage: G3 = libgap.eval('Group( [ (1,2,3) ] )')

    It can be seen from the printed statement that the actual
    computation is only done when the method is called first.
    ::

        sage: I2 = f.bar(G2); I2
        Group of order 2
        y^2,
        x*y,
        x^2
        sage: f.bar(G2)
        y^2,
        x*y,
        x^2
        sage: I3 = f.bar(G3); I3
        Group of order 3
        y^3,
        x*y^2,
        x^2*y,
        x^3
        sage: f.bar(G3)
        y^3,
        x*y^2,
        x^2*y,
        x^3
        sage: I2 is f.bar(G2)
        True

    The point is that even when Singular crashes, the data can be
    reconstructed without a new computation (note that the printed
    statement does not appear)::

        sage: singular.quit()
        sage: G2 = libgap.eval('Group( [ (1,2) ] )')
        sage: f.bar(G2)
        y^2,
        x*y,
        x^2
        sage: I2 is f.bar(G2)
        False
        sage: I2 = f.bar(G2)

    Note, moreover, that the given doc string is modified by
    the decorator::

        sage: print(f.bar.__doc__)
        Permanently cached method: Here is the documentation.
        <BLANKLINE>

    Last, we simulate a ``KeyboardInterrupt`` being cached,
    and force recomputation afterwards::

        sage: f.bar.set_cache(KeyboardInterrupt('simulation'),G2)
        sage: try:
        ....:     f.bar(G2)
        ....: except KeyboardInterrupt as msg:
        ....:     print(msg)
        simulation
        sage: f.bar(G2, forced=True)
        Group of order 2
        y^2,
        x*y,
        x^2
        sage: I2 is f.bar(G2)
        False

    Note that when a ``KeyboardInterrupt`` really occurs in the
    method, the error message will mention the possibility of
    forcing a recomputation. Here is an example::

        sage: class FOO:
        ....:     _t = 0
        ....:     @permanent_result
        ....:     def bar(self, n):
        ....:         if not self._t:
        ....:             raise KeyboardInterrupt
        ....:         return n+self._t
        ....:     @permanent_result
        ....:     def foo(self,n):
        ....:         return libgap.SymmetricGroup(self.bar(n))
        sage: f = FOO()
        sage: try:
        ....:     f.foo(1)
        ....: except KeyboardInterrupt as msg:
        ....:     print(msg)
        bar interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
        foo interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``

    The ``KeyboardInterrupt`` is cached. So, even if we set the attribute
    ``_t`` above to a non-zero value, the error won't go away, unless we
    force re-computation::

        sage: f._t = 2
        sage: try:
        ....:     f.bar(1)
        ....: except KeyboardInterrupt as msg:
        ....:     print(msg)
        bar interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
        sage: f.bar(1, forced=True)
        3
        sage: try:
        ....:     f.foo(1)
        ....: except KeyboardInterrupt as msg:
        ....:     print(msg)
        bar interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
        foo interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
        sage: f.foo(1,forced=True)
        Sym( [ 1 .. 3 ] )

    In the next example, we demonstrate that pickling works, even if Gap data
    are involved::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(184,5, prime=2)
        sage: H.make()
        sage: type(H.essential_ideal)
        <class 'pGroupCohomology.cohomology.permanent_result'>
        sage: H.essential_ideal([H.group().SylowSubgroup(2).Centre()])
        b_1_0,
        b_1_1

    Now, we store the result on disc, empty the cache, reload, and demonstrate
    by logging that the previously computed result has been stored, even though
    the data are defined in the Singular interface and are indexed by an object
    in Gap::

        sage: save(H, H.autosave_name())
        sage: CohomologyRing._cache.clear()
        sage: CohomologyRing.global_options('warn')
        sage: H2 = load(H.autosave_name())
        sage: H2 is H
        False
        sage: H2.essential_ideal([H.group().SylowSubgroup(2).Centre()])
        b_1_0,
        b_1_1
        sage: CohomologyRing.global_options('warn')
        sage: H.group().SylowSubgroup(2).Centre().parent()
        C library interface to GAP
        sage: H2.essential_ideal([H.group().SylowSubgroup(2).Centre()]).parent()
        Singular

    """
    _mode = 'Permanently cached method: '

    def __init__(self, f):
        """
        INPUT:

        ``f`` -- a callable

        TESTS::

            sage: from pGroupCohomology.cohomology import permanent_result
            sage: def f(self): return None
            ...
            sage: A = permanent_result(f)    # indirect doctest
            sage: A()
            Traceback (most recent call last):
            ...
            ValueError: <class 'pGroupCohomology.cohomology.permanent_result'> instance can not be called unboundedly

        """
        self._f = f
        self._name = f.__name__
        self._inst = None

    def _instancedoc_(self):
        """
        Return documentation of the wrapped method.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cohomology import _split_embedding_info
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,67)
            sage: 'Temporarily cached method' in H.poincare_series._instancedoc_()
            True

        """
        emb_doc = _split_embedding_info(self._f)
        second = emb_doc[1].lstrip()
        pad = (len(emb_doc[1])-len(second))*' '
        return (pad+self._mode).join([emb_doc[0],second])

    def _sage_argspec_(self):
        """
        Return the argspec of the wrapped method.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cohomology import _split_embedding_info
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,67)
            sage: H.poincare_series._sage_argspec_()
            ArgSpec(args=['self', 'test_duality'], varargs=None, keywords=None, defaults=(False,))

        """
        return sage_getargspec(self._f)

    def __get__(self, inst, cl):
        """
        TESTS::

            sage: from pGroupCohomology.cohomology import permanent_result
            sage: class FOO:
            ....:     def __init__(self,R):
            ....:         self.R = R
            ....:         self.GenS = singular.int(1)
            ....:     def _singular_(self,S):
            ....:         return S(self.R)
            ....:     @permanent_result
            ....:     def bar(self, G):
            ....:         '''
            ....:         Here is documentation
            ....:         '''
            ....:         singular(self).set_ring()
            ....:         print('Group of order',G.Order())
            ....:         return singular.maxideal(G.Order())
            sage: R.<x,y> = QQ[]
            sage: f = FOO(R)
            sage: print(f.bar.__doc__)   #indirect doctest
            Permanently cached method:
                     Here is documentation
            <BLANKLINE>

        """
        if inst is not None:
            self._inst = ref(inst)
        return self
    def set_cache(self,val, *args,**kwds):
        """
        Set the cache for the given arguments to a certain value.

        INPUT:

        - ``val`` -- any object, that is to be cached
        - Any position and keyword arguments. They must be immutable
          or lists of immutables.

        EXAMPLE::

            sage: from pGroupCohomology.cohomology import permanent_result
            sage: class FOO:
            ....:     @permanent_result
            ....:     def bar(self, G):
            ....:         return G.Order()
            ....:     @permanent_result
            ....:     def foo(self, G):
            ....:         raise KeyboardInterrupt
            sage: f = FOO()
            sage: G2 = libgap.eval('Group( [ (1,2) ] )')
            sage: f.bar(G2)
            2
            sage: try:
            ....:     f.foo(3)
            ....: except KeyboardInterrupt as msg:
            ....:     print(msg)
            foo interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``

        This results in creating a cache for ``f``. Note that
        even the ``KeyboardInterrupt`` is cached::

            sage: sorted(f._decorator_cache.items())    #indirect doctest
            [(('bar', Group([ (1,2) ])), [2]),
             (('foo', 3),
              [KeyboardInterrupt('foo interrupted. Force re-computation ...)])]

        """
        key = tuple([self._name]+[repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t) for t in args]+sorted([(a,repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t)) for a,t in kwds.items()]))
        inst = self._inst() if self._inst is not None else None
        if inst is None:
            return
        try:
            if inst._decorator_cache is None:
                inst._decorator_cache = {}
        except AttributeError:
            inst._decorator_cache = {}
        if hasattr(val,'_check_valid'): # some interface
            if repr(val.parent()) == 'Singular':
                inst._decorator_cache[key] = [val, repr(val.typeof()), val.parent().eval('string(%s)'%val.name())]
            else:
                inst._decorator_cache[key] = [val,repr(val)]
        else:
            inst._decorator_cache[key] = [val]

    def get_cache(self, *args,**kwds):
        """
        Return the value that was saved using :meth:`set_cache`.

        NOTE:

        If necessary, data in interfaces (in particular in GAP
        and Singular) are reconstructed. This of course only
        works to some extent (e.g., for GAP, it is needed that
        the saved value can be reconstructed from its string
        representation, and in Singular, it needs to be
        reconstructible from the string representation and
        the type information.

        EXAMPLE::

            sage: from pGroupCohomology.cohomology import permanent_result
            sage: class FOO:
            ....:     GenS = singular.int(0) # needed for Singular reconstruction
            ....:     def _singular_(self, S):
            ....:         return S(QQ['x','y'])
            ....:     @permanent_result
            ....:     def bar(self, n):
            ....:         return libgap.SymmetricGroup(n)
            ....:     @permanent_result
            ....:     def foo(self, n):
            ....:         singular(self).set_ring()
            ....:         return singular.maxideal(n)
            sage: f = FOO()
            sage: f = FOO()
            sage: G = f.bar(4); G
            Sym( [ 1 .. 4 ] )
            sage: G is f.bar(4)
            True

        Setting the cache to a different value::

            sage: f.bar.set_cache(gap.AlternatingGroup(3), 4)
            sage: f.bar(4)
            AlternatingGroup( [ 1 .. 3 ] )
            sage: f.bar.get_cache(4)
            AlternatingGroup( [ 1 .. 3 ] )

        Now, similarly for data in Singular::

            sage: I = f.foo(3); I
            y^3,
            x*y^2,
            x^2*y,
            x^3
            sage: I is f.foo(3)
            True
            sage: f.foo(3).typeof()
            ideal
            sage: f.foo.set_cache(singular.poly('x*y'),3)
            sage: f.foo.get_cache(3)
            x*y
            sage: f.foo(3).typeof()
            poly

        """
        key = tuple([self._name]+[repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t) for t in args]+sorted([(a,repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t)) for a,t in kwds.items()]))
        # for whatever reason, sometimes BLA._decorator_cache is not set
        # in the init method - it is renamed to _<classname>_decorator_cache
        inst = self._inst() if self._inst is not None else None
        if inst is None:
            return
        try:
            if inst._decorator_cache is None:
                inst._decorator_cache = {}
        except AttributeError:
            inst._decorator_cache = {}
        val = inst._decorator_cache[key]
        if len(val)>1 and not isinstance(val[-1], (str, unicode)):
            # If val comes from a permanent cache, then either it is
            # of length 1, or belongs to an interface, and the last
            # item is a string to reconstruct the interface data.
            # Hence, if the length is at least two but the last entry
            # is no string, then it comes from a method that was previously
            # wrapped with temporary_result but is now permanent_result
            # (e.g., dependent_parameters).
            # If the cohomology ring is completely known, it should
            # be safe to use the stored value, otherwise we force recomputation.
            if inst.completed:
                val.pop(-1)
            else:
                raise KeyError("The saved data were not permanent")
        if len(val) == 1:
            return val[0]
        # The value is defined in some interface. Test if it is valid
        if len(val) == 2:
            a,b = val
            try:
                a._check_valid()
                return a
            except ValueError:
                # if the interface has not been pickled,
                # we assume that it is libGAP
                GAP = a.parent() or inst.group().parent()
                a = GAP.eval(b)
                inst._decorator_cache[key][0] = a
                return a
        # it is in Singular!
        a,t,b = val
        try:
            a._check_valid()
            return a
        except ValueError:
            S = a.parent() or inst.GenS.parent()
            S(inst).set_ring()
            a = S(b, t)   # includes the type information!
            inst._decorator_cache[key][0] = a
            return a

    def __call__(self,*args,**kwds):
        """
        Cache the returned value (or the raised ``KeyboardInterrupt``).

        NOTE:

        Recomputation can be achieved by providing the optional
        argument ``forced``.

        TESTS::

            sage: from pGroupCohomology.cohomology import permanent_result
            sage: class FOO:
            ....:     _t = 0
            ....:     @permanent_result
            ....:     def bar(self, n):
            ....:         if not self._t:
            ....:             raise KeyboardInterrupt
            ....:         return n+self._t
            ....:     @permanent_result
            ....:     def foo(self,n):
            ....:         return libgap.SymmetricGroup(self.bar(n))
            sage: f = FOO()
            sage: try:
            ....:     f.foo(1)
            ....: except KeyboardInterrupt as msg:
            ....:     print(msg)
            bar interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
            foo interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``

        The ``KeyboardInterrupt`` is cached. So, even if we set the attribute
        ``_t`` above to a non-zero value, the error won't go away, unless we
        force re-computation::

            sage: f._t = 2
            sage: try:
            ....:     f.bar(1)    # indirect doctest
            ....: except KeyboardInterrupt as msg:
            ....:     print(msg)
            bar interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
            sage: f.bar(1, forced=True)
            3
            sage: try:
            ....:     f.foo(1)
            ....: except KeyboardInterrupt as msg:
            ....:     print(msg)
            bar interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
            foo interrupted. Force re-computation at <....FOO ... at ...> with ``forced=True``
            sage: f.foo(1,forced=True)
            Sym( [ 1 .. 3 ] )

        """
        inst = self._inst() if self._inst is not None else None
        if inst is None:
            raise ValueError('%s instance can not be called unboundedly'%repr(self.__class__))
        if kwds.get('forced'):
            del kwds['forced']
            coho_logger.info('Forced recomputation of %s', inst, self._name)
        else:
            try:
                val = self.get_cache(*args,**kwds)
                if isinstance(val,KeyboardInterrupt):#val is NotImplemented:
                    raise val
                if isinstance(val, list):
                    return list(val)
                return val
            except KeyError:
                pass
        coho_logger.info('Compute %s', inst, self._name)
        try:
            val = self._f(inst,*args,**kwds)
        except KeyboardInterrupt as msg:
            if msg.args:
                val = KeyboardInterrupt(msg.args[0]+'\n%s interrupted. Force re-computation at %s with ``forced=True``'%(self._name,repr(inst)))
            else:
                val = KeyboardInterrupt('%s interrupted. Force re-computation at %s with ``forced=True``'%(self._name,repr(inst)))
        if val is not None:
            self.set_cache(val,*args,**kwds)
        if isinstance(val,KeyboardInterrupt):
             raise val
        if isinstance(val, list):
            return list(val)
        return val

class temporary_result(permanent_result):
    """
    Decorator for caching methods of a cohomology ring approximation.

    NOTE:

    This decorator is designed for application to cohomology rings
    (:class:`COHO`). Unlike :class:`permanent_result`, the cached
    value is re-computed if the structure of the ring approximation
    has changed, i.e., if a new generator or a new relation was
    found after the value was cached.

    ``KeyboardInterrupt`` is cached -- see :class:`permanent_result`
    for more details.

    EXAMPLE:

    The method :meth:`~pGroupCohomology.cohomology.COHO.poincare_series`
    uses our decorator for temporary results. In order to avoid
    using a stored value, we force a new computation in the first place.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(8,4, from_scratch=True)
        sage: H.make(1)
        sage: CohomologyRing.global_options('info')
        sage: p = H.poincare_series(); p   # indirect doctest
        H^*(Q8; GF(2)):
            Compute poincare_series
            Computing complete Groebner basis
        1/(t^2 - 2*t + 1)
        sage: p is H.poincare_series()
        True

    We now overwrite the cached value, also demonstrating that
    a ``KeyboardInterrupt`` is cached as well::

        sage: H.poincare_series.set_cache(KeyboardInterrupt('bla'))
        sage: try:
        ....:     H.poincare_series()
        ....: except KeyboardInterrupt as msg:
        ....:     print(msg)
        bla

    We can use the optional argument ``forced`` for restoring the
    cache::

        sage: H.poincare_series(forced=True)
            Forced recomputation of poincare_series
            Compute poincare_series
        1/(t^2 - 2*t + 1)

    The value in the cache is automatically updated if the ring
    structure changes by a computation in higher degree. The use of
    the optional argument ``forced`` is not necessary in this case::

        sage: CohomologyRing.global_options('warn')
        sage: H.make(2)
        sage: CohomologyRing.global_options('info')
        sage: H.poincare_series()
        H^*(Q8; GF(2)):
            Compute poincare_series
        (t + 1)/(-t + 1)

    """
    # assumption: If it is data in Singular, then it belongs
    # to the ring singular(self._inst).
    _mode = 'Temporarily cached method: '

    def set_cache(self,val, *args,**kwds):
        """
        Set the cache of this method to a specific value.

        INPUT:

        - ``val`` -- the value to be cached.
        - Any further position or keyword arguments that are
          suitable as dictionary keys (lists are automatically
          transformed into tuples).

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,4, from_scratch=True)
            sage: H.make(1)
            sage: H.poincare_series()
            1/(t^2 - 2*t + 1)
            sage: H.poincare_series.set_cache('hello world',42,foo='bar')
            sage: H.poincare_series(42, foo='bar')
            'hello world'
            sage: H.poincare_series(42, foo='bar', forced=True)
            Traceback (most recent call last):
            ...
            TypeError: poincare_series() got an unexpected keyword argument 'foo'
            sage: H.poincare_series(42, foo='bar')
            'hello world'

        Note that the cache is automatically cleared if the ring structure
        changes::

            sage: H.make()
            sage: H.poincare_series(42, foo='bar')
            Traceback (most recent call last):
            ...
            TypeError: poincare_series() got an unexpected keyword argument 'foo'
            sage: H.poincare_series()
            (-t^2 - t - 1)/(t^3 - t^2 + t - 1)

        """
        key = tuple([self._name]+[repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t) for t in args]+sorted([(a,repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t)) for a,t in kwds.items()]))
        # this here is specialized to cohomology rings,
        # where there is no problem with the existence of ._decorator_cache
        inst = self._inst() if self._inst is not None else None
        if inst is None:
            return
        deg = inst.last_interesting_degree()
        if hasattr(val,'_check_valid'): # some interface
            if repr(val.parent())=='Singular':
                inst._decorator_cache[key] = [val, repr(val.typeof()), val.parent().eval('string(%s)'%val.name()),deg]
            else:
                inst._decorator_cache[key] = [val,repr(val),deg]
        else:
            inst._decorator_cache[key] = [val,deg]

    def get_cache(self, *args,**kwds):
        """
        Get the value that was cached for the given arguments.

        NOTE:

        If the ring structure has changed after storing the value,
        a ``KeyError`` is raised.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,4, from_scratch=True)
            sage: H.make(1)
            sage: p = H.poincare_series(); p
            1/(t^2 - 2*t + 1)
            sage: p is H.poincare_series.get_cache()
            True
            sage: H.make(2)
            sage: H.poincare_series.get_cache()
            Traceback (most recent call last):
            ...
            KeyError: 'The saved data belong to a previous stage of the computation'

        """
        key = tuple([self._name]+[repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t) for t in args]+sorted([(a,repr(t) if hasattr(t,'_check_valid') else (tuple(t) if isinstance(t,list) else t)) for a,t in kwds.items()]))
        inst = self._inst() if self._inst is not None else None
        if inst is None:
            return
        val = inst._decorator_cache[key]
        if val[-1] != inst.last_interesting_degree():
            raise KeyError('The saved data belong to a previous stage of the computation')
        if len(val)==2:
            return val[0]
        # The value is defined in some interface. Test if it is valid
        from pGroupCohomology.auxiliaries import gap
        if len(val) == 3:
            a,b,d = val
            if a == gap: # that's in fact libgap
                return a.eval(b)
            try:
                a._check_valid()
                return a
            except ValueError:
                P = a.parent()
                a = P(b)
                inst._decorator_cache[key][0] = a
                return a
        # it is in Singular!
        a,t,b,d = val
        try:
            a._check_valid()
            return a
        except ValueError:
            S = a.parent()
            if inst.completed:
                S(inst).set_ring()
            else:
                inst.set_ring()
            a = S(b,t)   # includes the type information!
            inst._decorator_cache[key][0] = a
            return a

instancedoc(permanent_result)
instancedoc(temporary_result)

#########################################
##
## The main course...
##
#########################################

@richcmp_method
class COHO(Ring):
    r"""
    Modular Cohomology Rings of Finite `p`-Groups with coefficients in `\mathbb F_p`.

    AUTHORS:

    - Simon King <simon.king@uni-jena.de>

    INPUT:

    A finite `p`-group, either given by its coordinates in the
    SmallGroups library of Hans Ulrich Besche, Bettina Eick and Eamonn
    O'Brien, or given as a group in the libgap interface.

    OUTPUT:

    An object set up to compute the cohomology ring of the given
    `p`-group with coefficients in `\mathbb F_p`.

    ALGORITHM:

    The methods are based on algorithms due to Dave Benson, David
    Green, Simon King and Peter Symonds.

    Eventually, a minimal generating set for the cohomology ring and a
    minimal set of algebraic relations is computed, together with
    various other information (e.g., Poincaré series).

    By :meth:`~pGroupCohomology.factory.CohomologyRingFactory.global_options`
    and by various parameters (see below), it can be
    influenced by what methods the results are computed, how the
    computation is documented, and where files created during the
    computation are stored.

    The purpose of this examples is to document some internals of the
    implementation. For examples of the actual use of this package, we
    refer to :mod:`pGroupCohomology`. Note that usually one would not
    construct an instance of the class COHO directly. Just for
    documentation, we use COHO in all but the first example. In the
    first example, we use the constructor
    :func:`pGroupCohomology.CohomologyRing`, which is the recommended
    way of creating a cohomology ring.

    EXAMPLES:

    First, a small example with logging enabled. We use the
    constructor :func:`pGroupCohomology.CohomologyRing` in
    a way that prevents the ring from being downloaded from the web
    repository or reloaded from the data based shipped with this package.

    When setting up the cohomology ring, the cohomology of various
    elementary abelian subgroups is computed first. But if they'd
    happen to be found in the local sources, they would simply be
    loaded from there. In order to make the doctest independent of the
    contents of this database, we compute the two rings in question
    separately and insist on a computation from scratch. For one of them,
    we show details of the computation by logging::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: tmp_root = tmp_dir()
        sage: CohomologyRing.set_workspace(tmp_root)
        sage: X = CohomologyRing(4,2, from_scratch=True)
        sage: X.make()
        sage: X = CohomologyRing(2,1, from_scratch=True, options='info')
        _get_p_group_from_scratch:
            We compute this cohomology ring from scratch
        H^*(SmallGroup(2,1); GF(2)):
            Initialising maximal p-elementary abelian subgroups
        sage: X.make()
        Resolution of GF(2)[SmallGroup(2,1)]:
            Computing next term
            > rk P_02 =   1
        H^*(SmallGroup(2,1); GF(2)):
            We have to choose 1 new generator in degree 1
            > There is 1 Duflot regular generator in degree 1
            Summary: 0 relations and 1 generators in degree 1
            Ring approximation computed out to degree 1!
            Storing approximation data
            Determine degree 2 standard monomials
            We got 1 standard monomials
            There is no new generator in degree 2
            Summary: 0 relations and 0 generators in degree 2
            Ring approximation computed out to degree 2!
            Storing approximation data

    Since the group of order two is abelian, it is known a priori that
    the cohomology ring can be presented in degree at most two. So, we
    don't need to use any complicated completeness criterion. Now, for
    the dihedral group of order 8. This package contains a list of
    custom names for some groups from the SmallGroups library, and the
    dihedral group is part of that list.

    Note that we don't need to give the argument ``options='info'``
    again, since this option is already in use.
    ::

        sage: H = CohomologyRing(8,3, from_scratch=True)
        _get_p_group_from_scratch:
            We compute this cohomology ring from scratch
            Computing basic setup for Small Group number 3 of order 8
        H^*(D8; GF(2)):
            Initialising maximal p-elementary abelian subgroups
            Inserting SmallGroup(2,1) as a subgroup
            ...
            Computing Dickson invariants in elementary abelian subgroup of rank 2

    Now, the basic setup is done. We compute the ring structure, logging
    the computation::

        sage: H
        H^*(D8; GF(2))
        sage: H.make()
            Compute group_is_abelian
            We have no degree bound yet
            Start computation in Degree 1
        Resolution of GF(2)[D8]:
            Make degree 1 autolift data
        H^*(D8; GF(2)):
            There are new generators, we have to lift the restriction maps
        Resolution of GF(2)[D8]:
            Computing next term
            > rk P_02 =   3
        Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(2,1); GF(2)):
            lift in the source resolution
            lift in the target resolution to degree 1
        Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
            lift in the source resolution
            lift in the target resolution to degree 1
        Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
            lift in the source resolution
            lift in the target resolution to degree 1
        H^*(D8; GF(2)):
            We have to choose 2 new generators in degree 1
            > There are 0 nilpotent generators in degree 1
            > There are 2 "boring" generators in degree 1
            Summary: 0 relations and 2 generators in degree 1
            Try to lift 1st power of 0th Dickson invariant
            Simultaneously lifting subgroup cochains of degree 1
            Simultaneous lift was successful!
            Factorising an element; it can be interrupted with Ctrl-c
            Ring approximation computed out to degree 1!
            Storing approximation data
            We expect a relation in degree at least 2
            Start computation in Degree 2
            Determine degree 2 standard monomials
            We got 3 standard monomials
            There are new generators, we have to lift the restriction maps
        Resolution of GF(2)[D8]:
            Computing next term
            > rk P_03 =   4
        Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(2,1); GF(2)):
            lift in the source resolution
            lift in the target resolution to degree 2
        Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
            lift in the source resolution
            lift in the target resolution to degree 2
        Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
            lift in the source resolution
            lift in the target resolution to degree 2
        H^*(D8; GF(2)):
            We have to choose 1 new generator in degree 2
            > There are 0 nilpotent generators in degree 2
            > There are 0 "boring" generators in degree 2
            > There is 1 Duflot regular generator in degree 2
            Summary: 1 relations and 1 generators in degree 2
            Ring approximation computed out to degree 2!
            Storing approximation data
            Compute dependent_parameters
            Try to find a set of generators over which the cohomology ring is finite.
            Computing complete Groebner basis
        H^*(SmallGroup(4,2); GF(2)):
            Computing complete Groebner basis
        H^*(D8; GF(2)):
            Trying Symonds' criterion
            Successful application of the Symonds criterion
            Finished computation of the ring structure
            Storing approximation data
        sage: CohomologyRing.global_options('warn')
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

    Now, without logging, an example using a group defined in Gap.
    This time, just for documentation, we invoke the class COHO directly
    (but in practice, one should of course use
    :func:`~pGroupCohomology.CohomologyRing`).
    ::

        sage: from pGroupCohomology.cohomology import COHO
        sage: CohomologyRing.global_options('warn')
        sage: G = libgap.DihedralGroup(8)
        sage: G
        <pc group of size 8 with 3 generators>
        sage: G.SetName("OtherName")
        <BLANKLINE>
        sage: G
        OtherName
        sage: H2 = COHO(G,root=tmp_root)
        sage: H2
        H^*(OtherName; GF(2))
        sage: H2.make()
        sage: print(H2)
        Cohomology ring of OtherName with coefficients in GF(2)
        <BLANKLINE>
        Computation complete
        Minimal list of generators:
        [c_2_2: 2-Cocycle in H^*(OtherName; GF(2)),
         b_1_0: 1-Cocycle in H^*(OtherName; GF(2)),
         b_1_1: 1-Cocycle in H^*(OtherName; GF(2))]
        Minimal list of algebraic relations:
        [b_1_0*b_1_1+b_1_0^2]

    Next, a slightly bigger example::

        sage: H4 = COHO(64,14,root=tmp_root)
        sage: H4.make()    # about 20 seconds
        sage: H4.gens()
        [1,
         a_2_1: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_2_2: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_4_4: 4-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_0: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_1: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_3_3: 3-Cocycle in H^*(SmallGroup(64,14); GF(2))]

    It depends on the python version whether or not the relations are
    tail-reduced and how they are sorted::

        sage: if (2, 8) < sys.version_info:
        ....:     expected_rels = ['a_1_0^2', 'a_1_0*a_1_1', 'a_1_1^3', 'a_2_1*a_1_0',
        ....:           'a_2_1^2+a_2_1*a_1_1^2', 'a_1_0*a_3_3+a_2_1*a_1_1^2',
        ....:           'a_1_1*a_3_3+a_2_1*a_1_1^2', 'a_2_1*a_3_3', 'a_3_3^2']
        ....: else:
        ....:     expected_rels = ['a_1_0^2', 'a_1_0*a_1_1', 'a_1_1^3', 'a_2_1*a_1_0',
        ....:           'a_2_1^2+a_2_1*a_1_1^2', 'a_1_1*a_3_3+a_2_1^2',
        ....:           'a_1_0*a_3_3+a_2_1^2', 'a_2_1*a_3_3', 'a_3_3^2']
        ....:
        sage: H4.rels() == expected_rels
        True

    An example with `p=3`, so that the cohomology ring is
    non-commutative::

        sage: R = COHO(27,3,root=tmp_root)
        sage: R.make()
        sage: R.gens()
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
        sage: print(R('a_1_0*a_3_4'))
        4-Cocycle in H^*(E27; GF(3)),
        represented by
        [1 0 0 0 0 0 0]
        sage: print(R('a_3_4*a_1_0'))
        4-Cocycle in H^*(E27; GF(3)),
        represented by
        [2 0 0 0 0 0 0]
        sage: print(R.6*R.8)
        4-Cocycle in H^*(E27; GF(3)),
        represented by
        [1 0 0 0 0 0 0]
        sage: c=R('a_1_0*a_1_1*b_2_0+b_2_1^2')
        sage: c.name()
        '((a_1_0)*(a_1_1))*(b_2_0)+(b_2_1)**2'
        sage: c.setname('C')
        sage: c
        C: 4-Cocycle in H^*(E27; GF(3))
        sage: R.poincare_series()
        (t^4 + 2*t^2 + 1)/(t^6 - 2*t^5 + 2*t^4 - 2*t^3 + 2*t^2 - 2*t + 1)
        sage: R._poincare_without_parameters()
        (t^4 + 2*t^2 + 1)/(t^6 - 2*t^5 + 2*t^4 - 2*t^3 + 2*t^2 - 2*t + 1)

    We return to our standard example, the cohomology of the dihedral
    group of order 8::

        sage: CohomologyRing.set_workspace(tmp_root)
        sage: H = CohomologyRing(8,3)
        sage: H.make()

    First of all, the attribute 'completed' tells whether the
    cohomology computation has been successfully finished. The
    attribute 'knownDeg' tells up to what degree the ring structure is
    explored, 'lastRel' is the degree of the last found relation, and
    '_method' states whose criterion was used to prove completeness::

        sage: H.completed
        True
        sage: H.knownDeg
        2
        sage: H.lastRel
        2
        sage: H._method
        'Symonds'

    A cohomology ring is based on some minimal projective resolution
    (see :class:`~pGroupCohomology.resolution.RESL`)::

        sage: H.resolution()
        Resolution of GF(2)[D8]

    The lists of generators and relations of a cohomology ring can be
    obtained with :meth:`gens` and :meth:`rels`.

    The attribute ``H.GenS`` provides a ring defined in the Singular
    interface, and ``H.RelG`` is a list of strings defining a Groebner
    basis for the relation ideal. The cohomology ring is isomorphic to
    the quotient of ``H.GenS`` by the ideal of ``H.RelG``. The same
    ring is created when putting ``H`` into the singular interface::

        sage: H.GenS.set_ring()
        sage: I=H.GenS.parent().ideal(H.RelG)
        sage: s=H.GenS.parent().eval('qring Q = %s'%(I.name()))
        sage: H.GenS.parent()('Q')
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
        sage: singular(H)
        polynomial ring, over a field, global ordering
        // coefficients: ZZ/2
        // number of vars : 3
        //        block   1 : ordering M
        //                  : names    c_2_2 b_1_0 b_1_1
        //                  : weights      2     1     1
        //                  : weights     -1     0     0
        //                  : weights      0    -1     0
        //        block   2 : ordering C
        // quotient ring from ideal ...

    The computation of a cohomology ring makes heavy use of the
    Singular interface. The names of all data in Singular that are
    related with a specific cohomology ring ``H`` have a common
    prefix, namely ``H.prefix``.  The prefix is chosen automatically
    and is different for any instance of
    :class:`~pGroupCohomology.cohomology.COHO`::

        sage: H.prefix==H.subgps[(4,2)].prefix
        False

    In the Singular interface, a graded commutative polynomial ring is
    defined and can be addressed as follows::

        sage: print(singular.eval('%sr(%d)'%(H.prefix,H.knownDeg)))
        // coefficients: ZZ/2
        // number of vars : 3
        //        block   1 : ordering M
        //                  : names    c_2_2 b_1_0 b_1_1
        //                  : weights      2     1     1
        //                  : weights     -1     0     0
        //                  : weights      0    -1     0
        //        block   2 : ordering C

    Note that in Singular, ideals are only available if the ring to
    which the ideal belongs is Singular's current
    ``basering``. Currently, the quotient ring defined above is
    ``basering``. We change the base ring, and then a Groebner basis
    at least up to degree ``H.knownDeg`` is given as follows::

        sage: H.set_ring()
        sage: singular('%sI'%(H.prefix))
        b_1_0*b_1_1

    We change the base ring again,
    ::

        sage: H.subgroups()[(4,2)].set_ring()

    and then of course the relation ideal of ``H`` is not available
    anymore::

        sage: singular('%sI'%(H.prefix))
        Traceback (most recent call last):
        ...
        TypeError: Singular error:
          ? ... is undefined
          ? error occurred in ...: `def ...;`

    **Custom attributes**

    In Python, it is possible to add attributes to any object.
    However, when adding a Python attribute to a cohomology ring, it
    would be lost when saving.

    Therefore we provide another way to add custom "attributes"
    to a cohomology ring. We refer to such attribute as a "property"
    of the ring.

    Properties can be retreived in the same way as usual attributes,
    they are visible in tab completion and in introspection, and they
    are preserved when the cohomology ring is saved and reloaded.
    This is very useful for adding more information.

    When an attribute of the requested name (``Status`` in the
    following example) does not exist, it is checked whether a
    property of that name has yet been defined. If this is the case,
    it is returned, otherwise None is returned. Note that *for
    cohomology rings you will never get an ``AttributeError`` except
    for attributes that start and end with an underscore*::

        sage: H._foobar_
        Traceback (most recent call last):
        ...
        AttributeError: 'COHO' object has no attribute '_foobar_'
        sage: print(H.Status)  # not defined at that point, hence "None"
        None
        sage: 'Status' in dir(H)
        False
        sage: H.setprop('Status','Our main example')
        sage: H.Status
        'Our main example'
        sage: 'Status' in dir(H)
        True

    Usually, cohomology rings that are created using the constructor
    :func:`~pGroupCohomology.CohomologyRing` are cached::

        sage: H is loads(dumps(H))
        True

    We destroy the cache on purpose and demonstrate that the additional
    property is preserved by pickling::

        sage: del CohomologyRing._cache[H._key]
        sage: HR = loads(dumps(H))
        sage: HR is H
        False
        sage: HR.Status
        'Our main example'

    Among many other data, the group name (that we passed on by
    the parameter ``GroupName``) and a more detailed autogenerated
    group description (that can be overwritten using
    ``setprop('GroupDescr',...)`` ) are provided in form of custom
    attributes::

        sage: H.GroupName  # This comes from a list of known group names
        'D8'
        sage: H.GroupDescr # This comes from a list of known group descriptions
        'Dihedral group of order 8'

    The custom attribute 'Status' can be deleted with
    ::

        sage: H.delprop('Status')
        sage: print(H.Status)
        None
        sage: 'Status' in dir(H)
        False

    TESTS:

    As mentioned above, there are various global options (both in the
    definition of a cohomology ring and by using
    CohomologyRing.global_options(...)) that influence the choice of
    algorithm. For unit testing, we repeat here one of the examples from
    above. In order to not loose too much time, we now allow to reload data.
    ::

        sage: CohomologyRing.global_options('reload')

    First, we use linear algebra and not elimination for finding the
    Dickson classes::

        sage: H4 = COHO(64,14,root=tmp_root, useElimination=False)
        sage: H4.make()
        sage: H4.gens()
        [1,
         a_2_1: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_2_2: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_4_4: 4-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_0: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_1: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_3_3: 3-Cocycle in H^*(SmallGroup(64,14); GF(2))]

    It depends on the python version whether or not the relations are
    tail-reduced and how they are sorted::

        sage: if (2, 8) < sys.version_info:
        ....:     expected_rels = ['a_1_0^2', 'a_1_0*a_1_1', 'a_1_1^3', 'a_2_1*a_1_0',
        ....:           'a_2_1^2+a_2_1*a_1_1^2', 'a_1_0*a_3_3+a_2_1*a_1_1^2',
        ....:           'a_1_1*a_3_3+a_2_1*a_1_1^2', 'a_2_1*a_3_3', 'a_3_3^2']
        ....: else:
        ....:     expected_rels = ['a_1_0^2', 'a_1_0*a_1_1', 'a_1_1^3', 'a_2_1*a_1_0',
        ....:           'a_2_1^2+a_2_1*a_1_1^2', 'a_1_1*a_3_3+a_2_1^2',
        ....:           'a_1_0*a_3_3+a_2_1^2', 'a_2_1*a_3_3', 'a_3_3^2']
        ....:
        sage: H4.rels() == expected_rels
        True

    We repeat the example, but this time use elimination.
    ::

        sage: H4 = COHO(64,14,root=tmp_root, useElimination=True)
        sage: H4.make()
        sage: H4.gens()
        [1,
         a_2_1: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_2_2: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_4_4: 4-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_0: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_1: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_3_3: 3-Cocycle in H^*(SmallGroup(64,14); GF(2))]
        sage: H4.rels() == expected_rels
        True

    Now we switch the 'sparse' option on::

        sage: CohomologyRing.global_options('sparse')
        sage: H4 = COHO(64,14,root=tmp_root)
        sage: H4.make()
        sage: H4.gens()
        [1,
         a_2_1: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_2_2: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_4_4: 4-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_0: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_1: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_3_3: 3-Cocycle in H^*(SmallGroup(64,14); GF(2))]
        sage: H4.rels() == expected_rels
        True
        sage: CohomologyRing.global_options('nosparse')

    And finally, we allow to convert to Sage matrices in some
    steps of the computation::

        sage: H4 = COHO(64,14,root=tmp_root)
        sage: CohomologyRing.global_options('nouseMTX')
        sage: H4.make()
        sage: H4.gens()
        [1,
         a_2_1: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_2_2: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_4_4: 4-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_0: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_1: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_3_3: 3-Cocycle in H^*(SmallGroup(64,14); GF(2))]
        sage: H4.rels() == expected_rels
        True
        sage: CohomologyRing.global_options('useMTX')

    """

####################
## Initialise the dictionary of group names as class variable
    GroupNames ={(8, 3): ['D8', 'Dihedral group of order 8'],
                 (8, 4): ['Q8', 'Quaternion group of order 8'],
                 (16, 6): ['Mod16', 'Modular group of order 16'],
                 (16, 7): ['D16', 'Dihedral group of order 16'],
                 (16, 8): ['SD16', 'Semidihedral group of order 16'],
                 (16, 9): ['Q16', 'Quaternion group of order 16'],
                 (16, 11): ['D8xC2', 'Direct product D8 x C_2'],
                 (16, 12): ['Q8xC2', 'Direct product Q8 x C_2'],
                 (16, 13): ['D8*C4', 'Central product D8 * C_4'],
                 (27, 3): ['E27', 'Extraspecial 3-group of order 27 and exponent 3'],
                 (27, 4): ['M27', 'Extraspecial 3-group of order 27 and exponent 9'],
                 (32, 17): ['Mod32', 'Modular group of order 32'],
                 (32, 18): ['D32', 'Dihedral group of order 32'],
                 (32, 19): ['SD32', 'Semidihedral group of order 32'],
                 (32, 20): ['Q32', 'Quaternion group of order 32'],
                 (32, 22): ['16gp3xC2', 'Direct product 16gp3 x C_2'],
                 (32, 23): ['16gp4xC2', 'Direct product 16gp4 x C_2'],
                 (32, 25): ['D8xC4', 'Direct product D8 x C_4'],
                 (32, 26): ['Q8xC4', 'Direct product Q8 x C_4'],
                 (32, 37): ['Mod16xC2', 'Direct product Mod16 x C_2'],
                 (32, 39): ['D16xC2', 'Direct product D16 x C_2'],
                 (32, 40): ['SD16xC2', 'Direct product SD16 x C_2'],
                 (32, 41): ['Q16xC2', 'Direct product Q16 x C_2'],
                 (32, 46): ['D8xV4', 'Direct product D8 x V_4'],
                 (32, 47): ['Q8xV4', 'Direct product Q8 x V_4'],
                 (32, 48): ['16gp13xC2', 'Direct product 16gp13 x C_2'],
                 (32, 49): ['E32+', 'Extraspecial 2-group of order 32 and type +'],
                 (32, 50): ['E32-', 'Extraspecial 2-group of order 32 and type -'],
                 (64, 51): ['Mod64', 'Modular group of order 64'],
                 (64, 52): ['D64', 'Dihedral group of order 64'],
                 (64, 53): ['SD64', 'Semidihedral group of order 64'],
                 (64, 54): ['Q64', 'Quaternion group of order 64'],
                 (64, 82): ['Syl2(Sz(8))', 'Sylow 2-subgroup of Suzuki Group Sz(8)'],
                 (64, 134): ['Syl2(M12)', 'Sylow 2-subgroup of Mathieu Group M_12'],
                 (64, 239): ['Q8xQ8', 'Direct product Q8 x Q8'],
                 (64, 242): ['Syl2(L3(4))', 'Sylow 2-subgroup of L_3(4)'],
                 (64, 245): ['Syl2(U3(4))', 'Sylow 2-subgroup of U_3(4)'],
                 (64, 261): ['D8xV8', 'Direct product D8 x V_8'],
                 (64, 262): ['Q8xV8', 'Direct product Q8 x V_8'],
                 (64, 266): ['E32+*C4', 'Central product E32+ * C_4'],
                 (81, 6): ['Mod81', 'Modular group of order 81'],
                 (81, 7): ['Syl3(A9)', 'Sylow 3-subgroup of A_9'],
                 (81, 9): ['Syl3(U3(8))', 'Sylow 3-subgroup of U_3(8)'],
                 (81, 12): ['E27xC3', 'Direct product E27 x C_3'],
                 (81, 13): ['M27xC3', 'Direct product M27 x C_3'],
                 (81, 14): ['E27*C9', 'Central product E27 * C_9'],
                 (125, 3): ['E125', 'Extraspecial 5-group of order 125 and exponent 5'],
                 (125, 4): ['M125', 'Extraspecial 5-group of order 125 and exponent 25'],
                 (128, 67): ['Syl2(U3(7))', 'Sylow 2-subgroup of U_3(7)'],
                 (128, 147): ['Syl2(2PGU2(31))', 'Sylow 2-subgroup of 2.PGU_2(31)'],
                 (128, 160): ['Mod128', 'Modular group of order 128'],
                 (128, 161): ['D128', 'Dihedral group of order 128'],
                 (128, 162): ['SD128', 'Semidihedral group of order 128'],
                 (128, 163): ['Q128', 'Quaternion group of order 128'],
                 (128, 836): ['Syl2(2Sz8)', 'Sylow 2-subgroup of one double cover of Sz(8)'],
                 (128, 850): ['64gp32xC2', 'Direct product 64gp32 x C_2'],
                 (128, 928): ['Syl2(S8)', 'Sylow 2-subgroup of Symmetric Group S_8'],
                 (128, 931): ['Syl2(M22)', 'Sylow 2-subgroup of Mathieu Group M_22'],
                 (128, 932): ['Syl2(G2(3):2)', 'Sylow 2-subgroup of exceptional group G_2(3):2'],
                 (128, 934): ['Syl2(J2)', 'Sylow 2-subgroup of Hall-Janko Group J_2'],
                 (128, 937): ['Syl2(Sp4(3))', 'Sylow 2-subgroup of Symplectic Group Sp_4(3)'],
                 (128, 1578): ['V8wrC2', 'Wreath product V_8 wr C_2'],
                 (128, 1755): ['64gp138xC2', 'Direct product 64gp138 x C_2'],
                 (128, 2023): ['SD16*SD16', 'Central product SD_16 * SD_16'],
                 (128, 2320): ['D8xV16', 'Direct product D8 x V_16'],
                 (128, 2321): ['Q8xV16', 'Direct product Q8 x V_16'],
                 (128, 2326): ['E128+', 'Extraspecial 2-group of order 128 and type +'],
                 (128, 2327): ['E128-', 'Extraspecial 2-group of order 128 and type -'],
                 (243, 24): ['Mod243', 'Modular group of order 243'],
                 (243, 32): ['81gp3xC3', 'Direct product 81gp3 x C_3'],
                 (243, 33): ['81gp4xC3', 'Direct product 81gp4 x C_3'],
                 (243, 35): ['E27xC9', 'Direct product E27 x C_9'],
                 (243, 36): ['M27xC9', 'Direct product M27 x C_9'],
                 (243, 49): ['81gp6xC3', 'Direct product 81gp6 x C_3'],
                 (243, 51): ['81gp7xC3', 'Direct product 81gp7 x C_3'],
                 (243, 52): ['81gp8xC3', 'Direct product 81gp8 x C_3'],
                 (243, 53): ['81gp9xC3', 'Direct product 81gp9 x C_3'],
                 (243, 54): ['81gp10xC3', 'Direct product 81gp10 x C_3'],
                 (243, 62): ['E27xV9', 'Direct product E27 x C_3 x C_3'],
                 (243, 63): ['M27xV9', 'Direct product M27 x C_3 x C_3'],
                 (243, 64): ['(E27*C3)xC3', 'Direct product E27*C3 x C_3'],
                 (243, 65): ['E243', 'Extraspecial 3-group of order 243 and exponent 3'],
                 (243, 66): ['M243', 'Extraspecial 3-group of order 243 and exponent 9'],
                 (256, 6661): ['Syl2(S4(7))', 'Sylow 2-group of Symplectic group S4(7)'],
                 (256, 6665): ['Syl2(Ly)', 'Sylow 2-group of 2A_11 and of Ly'],
                 (256, 8935): ['Syl2(S4(4))', 'Sylow 2-group of Symplectic group S4(4)'],
                 (343, 3): ['E343', 'Extraspecial 7-group of order 343 and exponent 7'],
                 (343, 4): ['M343', 'Extraspecial 7-group of order 343 and exponent 49'],
                 (625, 7): ['Syl5(Co1)', 'Sylow 5-subgroup of Co_1'],
                 (625, 12): ['E125xC5', 'Direct product E125 x C_5'],
                 (625, 13): ['M125xC5', 'Direct product M125 x C_5'],
                 (625, 14): ['E125*C25', 'Central product E125 * C_25'],
                 (729, 498): ['E27xV27', 'Direct product E27 x V_27'],
                 (729, 499): ['M27xV27', 'Direct product M27 x V_27 ']}
## Determine the standard locations for workspace and sources
    # workspace
    workspace = os.path.join(DOT_SAGE,'pGroupCohomology','db')

    # local
    try:
        from sage.env import SAGE_SHARE
    except ImportError:
        try:
            from sage.misc.misc import SAGE_SHARE
        except ImportError:
            from sage.misc.misc import SAGE_DATA as SAGE_SHARE

    local_sources = os.path.join(SAGE_SHARE,'pGroupCohomology')

    # remote
    remote_sources = ('http://cohomology.uni-jena.de/db/',)

####################
## init, repr, str
    def __init__(self, *args, **kwds):
        """
    TESTS::

        sage: from pGroupCohomology.cohomology import COHO
        sage: tmp_root = tmp_dir()
        sage: H4 = COHO(64,14,root=tmp_root)   # indirect doctest
        sage: H4.make()
        sage: H4.gens()
        [1,
         a_2_1: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_2_2: 2-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         c_4_4: 4-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_0: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_1_1: 1-Cocycle in H^*(SmallGroup(64,14); GF(2)),
         a_3_3: 3-Cocycle in H^*(SmallGroup(64,14); GF(2))]

    It depends on the python version whether or not the relations are
    tail-reduced and how they are sorted::

        sage: if (2, 8) < sys.version_info:
        ....:     expected_rels = ['a_1_0^2', 'a_1_0*a_1_1', 'a_1_1^3', 'a_2_1*a_1_0',
        ....:           'a_2_1^2+a_2_1*a_1_1^2', 'a_1_0*a_3_3+a_2_1*a_1_1^2',
        ....:           'a_1_1*a_3_3+a_2_1*a_1_1^2', 'a_2_1*a_3_3', 'a_3_3^2']
        ....: else:
        ....:     expected_rels = ['a_1_0^2', 'a_1_0*a_1_1', 'a_1_1^3', 'a_2_1*a_1_0',
        ....:           'a_2_1^2+a_2_1*a_1_1^2', 'a_1_1*a_3_3+a_2_1^2',
        ....:           'a_1_0*a_3_3+a_2_1^2', 'a_2_1*a_3_3', 'a_3_3^2']
        ....:
        sage: H4.rels() == expected_rels
        True
        sage: G = libgap.DihedralGroup(8)
        sage: G
        <pc group of size 8 with 3 generators>
        sage: H2 = COHO(G,GroupName='OtherName',root=tmp_root)
        sage: H2
        H^*(OtherName; GF(2))
        sage: H2.make()
        sage: print(H2)
        Cohomology ring of OtherName with coefficients in GF(2)
        <BLANKLINE>
        Computation complete
        Minimal list of generators:
        [c_2_2: 2-Cocycle in H^*(OtherName; GF(2)),
         b_1_0: 1-Cocycle in H^*(OtherName; GF(2)),
         b_1_1: 1-Cocycle in H^*(OtherName; GF(2))]
        Minimal list of algebraic relations:
        [b_1_0*b_1_1+b_1_0^2]

        """
        # argument "root" declares the name of the root directory
        self._property_dict = {}  # It is important that this attribute is present!
                          # Otherwise, an error in __init__ would produce a seg fault.
        self._decorator_cache = {}
        self._HomsetCache = WeakValueDictionary({})

        self.setprop('KeepBases',kwds.get('KeepBases'))
        Subgroups = kwds.get('Subgroups',True)
        cdef str root = str(kwds.get('root', COHO.workspace))
        coho_logger.debug("Group data are rooted at %r.", None, root)
        Hfinal = None
        if len(args) == 1:
            if not hasattr(args[0],'parent'):
                raise ValueError("The group must be given in the gap interface")
            gap = args[0].parent()
        else:
            from pGroupCohomology.auxiliaries import gap
        _gap_reset_random_seed()
        if len(args) == 2:
            # We expect an address in the Small Groups library
            q,n = args
            q = Integer(q)
            n = Integer(n)
            if q == 1:
                raise ValueError("We don't consider the trivial group")
            if (n<0) or (n<=0 and q>0): #(0,0) is for eating very old pickles...
                raise ValueError("SmallGroup number must be positive")
            if (q>0) and (n > gap.NumberSmallGroups(q).sage()): # will raise another error if SmallGroups is not installed
                raise ValueError("(%d,%d) is not in the SmallGroups library"%(q,n))

            ####
            ## make up (stem) name and unique group key
            GStem = kwds.get('GStem','%dgp%d'%(q,n))
            # Priorities for choosing GroupName: 1. user defined, 2. known from list, 3. default: GStem
            GroupName = kwds.get('GroupName')
            if GroupName is None:
                GroupName = COHO.GroupNames.get((q,n), ('SmallGroup(%d,%d)'%(q,n),))[0]
            GroupKey = kwds.get('key',[(q,n),''])[0]
            if n == gap.NumberSmallGroups(q):
                self.setprop('ElAb',True)


        elif len(args) == 0: # *only* used in pickling/unpickling
            q = 0
            n = 0
            GStem = ''


        elif len(args) == 1:
            ## We expect a group that is defined in Gap
            ##############
            ## It is assumed here that the group is given by minimal generators, and that there is a unique
            ## descriptor for the group provided (by the option 'key'). Moreover, GStem and GroupName must
            ## be explicitly provided. This is taken care of in
            ##       pGroupCohomology.CohomologyRing
            ## So, we see if there are proper key words (provided by CohomologyRing) and otherwise
            ## we test the input explicitly.
            if kwds.get('gap_input'):
                q = kwds['gap_input']  # it is supposed to be the group order
                GStem = kwds['GStem']  # *Must* be provided
                GroupName = kwds['GroupName']
                GroupKey = kwds['key'][0]
                Hfinal = args[0]
                n = -1
            else:
                H0 = args[0]
                if not hasattr(H0,'parent'):
                    raise TypeError("We expected a group defined in Gap")
                if H0.parent() is not gap:
                    try:
                        H0 = gap.eval(H0.String().sage())
                    except:
                        try:
                            H0 = gap.Group(H0.GeneratorsOfGroup())
                        except:
                            raise ValueError("We don't know how to convert {} to libGAP".format(H0))
                _gap_reset_random_seed()

                ####
                ## make up the (stem) name
                if H0.HasName():
                    GroupName = H0.Name().sage()
                else:
                    GroupName = None
                GroupName = kwds.get('GroupName', GroupName)
                GStem = kwds.get('GStem', GroupName)
                if (GStem is None):
                    raise ValueError("Either 'GroupName' or 'GStem' must be provided")
                if not (isinstance(GStem, basestring) and GStem.isalnum()):
                    raise TypeError("'GroupName' must be an alphanumeric string")
                if GroupName is None:
                    GroupName = GStem

                ####
                ## process the gap input:
                #   1. good group order?
                #   2. minimal generators given?
                #      if not, find them!
                #   3. transform into permutation group
                q = H0.Order().sage()
                if not q.is_prime_power():
                    raise ValueError("The group must be of prime power order")
                n = -1

                ## Try to make up minimal generators
                if H0.RankPGroup() == H0.GeneratorsOfGroup().Length():
                    # We already have minimal generators, and then we are supposed to use exactly *these* generators!
                    Hfinal = H0
                else:
                    coho_logger.info("Try to find minimal generators for %s", None, GroupName)
                    phi = H0.IsomorphismPermGroup()
                    HP = gap.Group([phi.Image(x) for x in H0.GeneratorsOfGroup()])
                    ## Hopefully gap can find minimal generating sets for permutation groups...
                    Hfinal = HP.Subgroup(HP.MinimalGeneratingSet())
                ####
                ## Finally, make up a description of the group which preserves the generators
                ## -- unless the user wants a different key (which may fail badly, but this is not our problem... :)
                if 'key' in kwds:
                    GroupKey = kwds['key'][0]
                else:
                    GroupKey = 'Group(['+','.join([g.String().sage() for g in Hfinal.asPermgroup().GeneratorsOfGroup()])+'])'
        else:
            raise TypeError("COHO initialisation requires between 0 and 2 arguments (%d given)"%(len(args)))

        if not isinstance(GStem, basestring):
            raise TypeError("Group stem name must be a string")

        self.GenS = singular(0)
        singular.eval('option(redSB,redTail,redThrough)')
        if q==0:  # only used for Python style unpickling of old data (Simon King only... :)
            self.prefix = COHO_prefix()()
            self._Terminator = COHO_Terminator(self.GenS, self.prefix)
            self.suffDeg = -1
            self.completed = False
            return
        if not ((q>0) and Integer(q).is_prime_power()):
            raise ValueError("The group order must be a prime power")

        ##################################
        ##################################
        ## Now the preparation is done, we have q, GStem, GroupName and GroupKey.
        ##################################
        ##################################
        self.GStem = GStem

        #########
        ## Store group name and group description
        self.setprop('GroupName',GroupName)
        if n>0:
            GroupDescr = 'Small Group number %d of order %d'%(n,q)
        else:
            GroupDescr = GroupName
        self.setprop('GroupDescr', kwds.get('GroupDescr',COHO.GroupNames.get((q,n), ('',GroupDescr))[1]))

        #####
        ## Determine data location relative to the root directory ...
        gps_folder = GStem
        dat_folder = os.path.join(gps_folder,'dat')
        res_folder = os.path.join(gps_folder,'dat')
        inc_folder = os.path.join(gps_folder,'sgp')
        ## ... and now absolutely:
        self.setprop('root',root)
        self.gps_folder = os.path.join(root,gps_folder)
        self.dat_folder = os.path.join(root,dat_folder)
        self.res_folder = os.path.join(root,res_folder)
        self.inc_folder = os.path.join(root,inc_folder)

        # store the key for this ring and insert itself to the cache
        if 'key' in kwds:
            if not kwds['key'][1].startswith(self.dat_folder):
                raise ValueError('Invalid location %s of State descriptor'%(kwds['key'][1]))
            self.setprop('_key', kwds['key'])
        else:
            self.setprop('_key', (GroupKey, os.path.join(self.dat_folder,'State')))
        from pGroupCohomology import CohomologyRing
        _cache = CohomologyRing._cache
        _cache[self._key] = self  # Note that there is no entry yet with this key --
                                  # provided that the ring
                                  # initialisation is done with
                                  # CohomologyRing!

        ## Auxiliaries for cleaning up singular
        self.prefix = COHO_prefix()()  # that way, we can distinguish the instances of COHO in the Singular interface
        self._Terminator = COHO_Terminator(self.GenS, self.prefix) # ensures that self's data in the singular interface are killed

        ###########
        ## Make the group data on disc ready for use!
        if Hfinal is None:
            if not os.access(os.path.join(self.gps_folder,GStem+'.nontips'),os.R_OK):
                if q==1:
                    raise ValueError("The group data for %s are not present in folder %s, and we don't know how to create them"%(GStem,gps_folder))
                makeGroupData(q,n,folder=root)
        else:
            makeSpecialGroupData(Hfinal,GStem,folder=root)
        self.Resl  = RESL(GStem, self.gps_folder, self.res_folder)
        (<RESL>self.Resl).G_Alg.groupname = self.printed_group_name()
        self.Gen = [] # Gen contains the list of generators
        self.firstOdd = 0
        self.Rel = []  # shall be a list of polynomials given by strings
        self.knownDeg = 0
        self.completed = False
        self.suffDeg = -1
        self.degvec = []

        ## attributes of more internal use
        self.Triangular = {} # Contains (for each degree) an echelon basis for decomposable classes.
        self.NilBasis = {} # Contains (for each degree) an echelon basis for the nilpotent classes.
                           # Only makes sense under the implicit assumption that the
                           # cohomology ring is a product of polynomial and outer algebras.
        self.lastRel = 0
        self.subgps = {}
        self.RestrMaps = {}
        self.RelG = None # shall be a list of polynomials given by strings
        self.Monomials = {} # keyname of standard monomial -> COCH
        self.StdMon = {0:{'1':singular('1')}}
        self.RelGName = ''
        self.Dickson = [] # shall contain strings that eventually help to define a filter regular sequence
        self.alpha = None # used in Dickson's criterium. Is very likely to be -1, if the cohomology ring is computed
        self.setprop('DicksonExp',kwds.get('DicksonExp',3))  # up to what p-power will we try to lift Dickson classes?
        if kwds.get('auto') is not None:          # Up to what degree will we use the autolift method?
            self.setprop('auto', kwds['auto'])
        elif self.ElAb:    # Creation of basic autolift data in high degrees may be expensive
            self.setprop('auto', coho_options['autoliftElAb'])
        else:
            self.setprop('auto', coho_options['autolift'])
        self.setprop('useFactorization', kwds.get('useFactorization', True))

        ###########
        ## Prepare Singular
        if self.Resl.coef()!=2: # non-commutative case
            singular.LIB('ncall.lib')
        singular.LIB('general.lib')
        singular.LIB('poly.lib')
        singular.LIB('dickson.lib')
        singular.eval('option(redSB)');
        singular.eval('int i')
        self.CElPos = 1
        self.CenterRk = None
        self.NumSubgps = 0
        self.MaxelPos = []
        self.MaxelRk  = []
        self.pRank = None
        self._property_dict['useElimination'] = kwds.get('useElimination')
        if kwds.get('useSlimgb'):
            self.setprop('useSlimgb',True)
        elif kwds.get('useStd'):
            self.setprop('useStd',True)

        #############
        ## Initialisation of subgroups
        if Subgroups:
            self.InitSubgroups()
        base_ring = GF(self.Resl.coef())
        if base_ring.characteristic() == 2:
            cat = CommutativeAlgebras(base_ring)
        else:
            cat = Algebras(base_ring)
        # Avoid some generic stuff that would override essential methods
        self._no_generic_basering_coercion = True
        Ring.__init__(self,base_ring, category=cat)

    ## there will be no copy method

    def _element_constructor_(self, s):
        """
        Interprete a string as a cocycle in ``self``.

        INPUT:

        ``s``: a string (representing a polynomial in the
        generators of self) or an element of ``self``

        OUTPUT:

        An element of ``self``.

        * If the input is an element of self, it is returned without change.
        * If the input is a string, it is attempted to evaluate it
          as an algebraic expression in the generators of self.
        * Otherwise, if the input can be converted into an element of the
          base field then a cocycle of degree zero is returned.

        If all of the above fails, a ``TypeError`` is raised.


        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.Gen
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            sage: print(H('b_1_1+b_1_0'))    # indirect doctest
            1-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1]
            sage: print(H.2+H.3)
            1-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1]
            sage: print(H(H.2+H.3))
            1-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1]
            sage: H.subgps[4,2](H.2+H.3)
            Traceback (most recent call last):
            ...
            ValueError: Cochain belongs to a different cohomology ring, namely H^*(D8; GF(2))

        """
        from pGroupCohomology.cochain import MODCOCH
        from pGroupCohomology.modular_cohomology import MODCOHO
        if isinstance(s, COCH) or isinstance(s, MODCOCH):
            if s.parent() is self:
                return s
            else:
                raise ValueError("Cochain belongs to a different cohomology ring, namely %s"%(repr(s.parent())))
        try:
            s = self.base_ring()(s)
        except TypeError:
            pass
        if not isinstance(s, (str, unicode)):
            # The following is necessary, since by some oddity the above might
            # return a tuple of an error with an error message!
            if not s in self.base_ring():
                raise TypeError("We don't know how to interprete %s"%(s))
            if isinstance(self, MODCOHO):
                return MODCOCH(self, singular(s), deg=0, name=repr(s), S=singular, is_polyrep=True)
            return COCH(self, 0, repr(s), [s], is_polyrep=True)
        L = {}
        for X in self.Gen:
            L[X.name()] = X
        from sage.misc.sage_eval import sage_eval
        if isinstance(self, MODCOHO):
            return sage_eval(s,locals=L)._NF_()
        return sage_eval(s,locals=L)

    def from_base_ring(self, r):
        """
        Return a degree zero cohomology class.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.from_base_ring(GF(2)(1))
            1: 0-Cocycle in H^*(D8; GF(2))

        """
        from pGroupCohomology.cochain import MODCOCH
        from pGroupCohomology.modular_cohomology import MODCOHO
        if isinstance(self, MODCOHO):
            return MODCOCH(self, singular(r), deg=0, name=repr(r), S=singular, is_polyrep=True)
        return COCH(self, 0, repr(r), [r], is_polyrep=True)

    def _coerce_map_from_(self, S):
        """
        There is a coercion from this ring to itself and from any ring that coerces into the base ring.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.coerce_map_from(ZZ)   # indirect doctest
            Coercion map:
              From: Integer Ring
              To:
            Cohomology ring of Dihedral group of order 8 with  coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        """
        return S is self or self.base_ring().has_coerce_map_from(S)

    def fraction_field(self):
        """
        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H = CohomologyRing(8,3)
            sage: H.fraction_field()
            Traceback (most recent call last):
            ...
            TypeError: A cohomology ring is, in general, not an integral domain.

        """
        raise TypeError("A cohomology ring is, in general, not an integral domain.")

    ## Homomorphisms -- Option "cat" is not supported yet
    def Hom(self, other, category=None):
        """
        Return a homset of induced homomorphisms between two cohomology rings.

        INPUT:

        - A cohomology ring that will be the codomain for all elements of the homset
        - ``cat`` (not implemented) a category of homomorphisms.

        EXAMPLES:

        We first create the cohomology rings for two different
        presentations of the dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H1 = CohomologyRing(8,3)
            sage: H2 = CohomologyRing(libgap.DihedralGroup(8), GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H1.Hom(H2)
            Set of Homomorphisms from H^*(D8; GF(2)) to H^*(DihedralGroup(8); GF(2))

        """
        if not isinstance(other, COHO):
            raise TypeError("The codomain must be %s, not %s"%(type(COHO),type(other)))
        try:
            return self._HomsetCache[other._key, category]
        except KeyError:
            pass
        from pGroupCohomology.cochain import CohomologyHomset
        H = CohomologyHomset(self, other, category=category)
        self._HomsetCache[other._key, category] = H
        return H

    def hom(self, m, other, M=None, d=0):
        """
        Create an induced homomorphism.

        INPUT:

        - ``m``, which usually is a group homomorphism defined in the
          libgap interface, but in principle could also be a
          :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix describing a
          homomorphism of the group algebras (not documented). The
          domain must be equivalent to the underlying group of ``other``,
          the codomain must be equivalent to the underlying group of
          ``self``.
        - ``other``, a cohomology ring
        - ``M`` (optional :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix):
          By this matrix one could prescribe a mapping of the first
          terms of the respective resolutions (not documented, and not
          needed for induced maps of group homomorphisms).
        - ``d`` (optional, default 0): Degree of the map. If it is
          non-zero then ``M`` must be provided.

        NOTE:

        The resulting homomorphism is cached.

        EXAMPLES:

        We first create the cohomology rings for two different
        presentations of the dihedral group of order 8.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G1 = libgap.SmallGroup(8,3)
            sage: H1 = CohomologyRing(8,3)
            sage: H1.make()
            sage: G2 = libgap.DihedralGroup(8)
            sage: H2 = CohomologyRing(G2, GroupName = 'DihedralGroup(8)', from_scratch=True)
            sage: H2.make()

        In order to obtain reproducible doc tests, we switch to
        permutation groups that are, from the perspective of our
        programs, equivalent to ``G1`` and ``G2``, and provide an
        explicit group isomorphism::

            sage: phi = libgap.eval('GroupHomomorphismByImages( Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] ), Group( [ (1,5)(2,6)(3,8)(4,7), (1,3,2,4)(5,7,6,8) ] ), [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ], [ (1,5)(2,6)(3,8)(4,7), (1,8)(2,7)(3,6)(4,5) ] )')
            sage: H1.group()==phi.Source()
            True
            sage: H2.group().canonicalIsomorphism(phi.Range()) != libgap.eval('fail')
            True
            sage: phi.IsInjective()
            true
            sage: phi.IsSurjective()
            true

        After ensuring that ``phi`` is printed nicely, we obtain the
        induced map::

            sage: phi.SetName('phi')
            sage: phi_star = H2.hom(phi,H1)
            sage: phi_star
            phi^*
            sage: phi_star.domain()
            H^*(DihedralGroup(8); GF(2))
            sage: phi_star.codomain()
            H^*(D8; GF(2))
            sage: [H1.element_as_polynomial(phi_star(X)) for X in H2.gens()]
            [1: 0-Cocycle in H^*(D8; GF(2)),
             b_1_1^2+c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_1+b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]

        The induced maps are cached::

            sage: phi_star is H2.hom(phi,H1)
            True
            sage: phi_star is loads(dumps(phi_star))
            True

        Cohomology rings of prime power and non prime power groups can
        be freely combined. We compute the mod-2 cohomology ring of
        some group of order 48. The ring presentation depends on the
        choice of a generating system for its Sylow 2-subgroup. Since
        an internal computation would yield a randomised result, we
        provide a Sylow 2-subgroup explicitly.
        ::

            sage: G = libgap.SmallGroup(48,36)
            sage: g1,g2,g3,g4,g5 = G.GeneratorsOfGroup()
            sage: S = g1.Group(g1*g2*g3,g2,g4)
            sage: HG = CohomologyRing(G,prime=2,Subgroup=S,GroupName='SmallGroup(48,36)', from_scratch=True)
            sage: HG.make()

        There is an embedding of the dihedral group into ``G``,
        and a quotient of ``G`` is isomorphic to the dihedral group.
        ::

            sage: G1toG = G1.GroupHomomorphismByImages(G, G1.GeneratorsOfGroup(), [g1*g2,g1*g2*g3,g4])
            sage: g11,g12,g13 = G1.GeneratorsOfGroup()
            sage: GtoG1 = G.GroupHomomorphismByImages(G1, G.GeneratorsOfGroup(),[g12*g13,g13,g11*g12,g13,G1.Identity()])
            sage: GtoG1.Image().IdGroup()
            [ 8, 3 ]
            sage: G1toG.Image().IdGroup()
            [ 8, 3 ]
            sage: GtoG1_star = H1.hom(GtoG1,HG)
            sage: G1toG_star = HG.hom(G1toG,H1)
            sage: [H1.element_as_polynomial(G1toG_star(x)) for x in HG.gens()]
            [1: 0-Cocycle in H^*(D8; GF(2)), c_2_2: 2-Cocycle in H^*(D8; GF(2)), b_1_0: 1-Cocycle in H^*(D8; GF(2)), b_1_1: 1-Cocycle in H^*(D8; GF(2)), b_1_0: 1-Cocycle in H^*(D8; GF(2))]
            sage: [HG.element_as_polynomial(GtoG1_star(x)) for x in H1.gens()[1:]]
            [b_1_1*c_1_2+b_1_0*c_1_2+c_2_5+c_1_2^2: 2-Cocycle in H^*(SmallGroup(48,36); GF(2)), b_1_1: 1-Cocycle in H^*(SmallGroup(48,36); GF(2)), b_1_0: 1-Cocycle in H^*(SmallGroup(48,36); GF(2))]

        And finally, we consider a homomorphism from ``G`` to ``G``, by
        composition of the previous homomorphisms::

            sage: GtoG = G1toG.CompositionMapping(GtoG1)
            sage: GtoG_star = HG.hom(GtoG,HG)
            sage: [HG.element_as_polynomial(GtoG_star(x)) for x in HG.gens()[1:]]
            [b_1_1*c_1_2+b_1_0*c_1_2+c_2_5+c_1_2^2: 2-Cocycle in H^*(SmallGroup(48,36); GF(2)), b_1_1: 1-Cocycle in H^*(SmallGroup(48,36); GF(2)), b_1_0: 1-Cocycle in H^*(SmallGroup(48,36); GF(2)), b_1_1: 1-Cocycle in H^*(SmallGroup(48,36); GF(2))]

        ``GtoG`` should coincide with the composition of the previous
        two induced homomorphisms, and indeed it does::

            sage: GtoG1_star*G1toG_star == GtoG_star
            True

        """
        return self.Hom(other)(m,M,d)

    ###########################################################
    ###########################################################
    ## Pickling and unpickling
    #
    # We use __reduce__, since this allows for caching,
    # uniqueness of parent structures, and other nice features.
    ###########################################################
    ###########################################################

    def __reduce__(self):
        """
        Serialise ``self``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H is loads(dumps(H))    # indirect doctest
            True

        """
        # self._key provides a unique description of the p-Group,
        # namely either a pair of integers (p,q) providing an address
        # in the SmallGroups library, or (s,) with a string s providing
        # the definition of a permutation group in Gap.
        # Moreover, self._key tells where to find self's data
        import os
        if '_dont_save_the_State' in self._property_dict:
            self.delprop('_dont_save_the_State')
        else:
            safe_save(self.__getstate__(), os.path.join(self.dat_folder,'State.sobj'))
        if self.root == COHO.workspace:
            StateFile = os.path.join('@user_db@',self.GStem,'dat','State')
        elif self.root == COHO.local_sources:
            StateFile = os.path.join('@public_db@',self.GStem,'dat','State')
        else:
            StateFile = self._key[1]
        return COHO_unpickle, (self._key[0], StateFile)

    def __getstate__(self):
        """
        Returns data that allow __setstate__ to reconstruct self when unpickling.

        OUTPUT:

        A list of length 35

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: from pGroupCohomology.cohomology import COHO
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
            sage: len(H.__getstate__())
            35

        Now, we initialize a cohomology ring "without properties"::

            sage: K = COHO()
            sage: print(K.knownDeg)
            None

        We change ``K`` into the same state as ``H``, making ``K`` a copy of ``H``::

            sage: K.__setstate__(H.__getstate__())
            sage: print(K)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        """
        #########
        ## The following data need special treatment:
        ## subgroups:
        cdef COCH X
        if self.subgps:
            import os
            subgps = [(i,os.path.join(gp.gps_folder,'H'+gp.GStem)) for i,gp in self.subgps.items()]
        else:
            subgps = []
        if self.subgpDickson:
            self.setprop('sgpDickson',[(i,[[X.deg(),X.name(),X.MTX()] for X in gpDickson]) for i,gpDickson in self.subgpDickson.items()])
        else:
            self.setprop('sgpDickson',[])
                  # new version: subgroup is already saved (as a group on its own!), and this is the location.
        ## Singular elements:
        StdMon = []
        # we need to set the singular ring of self
        if singular.eval('defined(%sr(%d))'%(self.prefix,self.lastRelevantDeg or self.knownDeg))=='1':
            singular.eval('setring %sr(%d)'%(self.prefix,self.lastRelevantDeg or self.knownDeg))
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
            DG = [s.strip() for s in singular.eval('print(%sDG)'%self.prefix).split(',')]
        else:
            DG=['0']
        #########
        ## Apparently it is a problem to pickle dictionaries.
        ## Cochains:
        Gen = [[X.Deg,X.Name,X.Data,X.Rdeg,X.Ydeg] for X in self.Gen]
        Triangular = [[i,[[X.Deg,X.Name,X.Data] for X in Tr]] for i,Tr in self.Triangular.items()]

        ## Chain maps:
        if self.RestrMaps:
            RestrMaps = [[i,[Restr[0], [Restr[1].G_map(),[Restr[1].__getitem_name__(k) for k in range(Restr[1].knownDeg()+1)]]]] for i,Restr in self.RestrMaps.items()]
        else:
            RestrMaps = []
        ## Save self.Monomials and self.Resl externally, instead of returning self.Resl.__reduce()[1]
        import os
        gps_folder = os.path.join(self.GStem,os.path.split(self.gps_folder)[1])
        res_folder = os.path.join(self.GStem,os.path.split(self.res_folder)[1])
        dat_folder = os.path.join(self.GStem,os.path.split(self.dat_folder)[1])
        inc_folder = os.path.join(self.GStem,os.path.split(self.inc_folder)[1])
        Resl = os.path.join(res_folder,'R'+self.GStem+'.sobj')
        safe_save(self.Resl,os.path.join(self.root,Resl))
        self.exportMonomials()

        ######
        ## ROOT: Should be explicitly defined as a property of self.
        ## If it isn't it can still be infered.
        ## We have a special location for local sources and workspace.
        ## We handle these explicitly. It is possible for the user to
        ## copy the data to a completely different location -- then
        ## we are confident that loading still works, but we can't give
        ## a guarantee since this is a difficult business...
        root = self.root
        if root is None: # try to infer the root
            root = os.path.split(self.gps_folder)[0]
        if root == COHO.workspace:
            self.setprop('root','@user_db@')
        elif root == COHO.local_sources:
            self.setprop('root','@public_db@')
        else:
            self.setprop('root',root)
        # _property_dict may contain data defined in terms of Gap.
        GapPickler.gap = self.group().parent()
        _property_dict = list(self._property_dict.items())
        self.setprop('root',root)

        if self.Dickson:
            if isinstance(self.Dickson[0],COCH): # ... then self is a subgroup, hence, Dickson data depend on the super-group
                return (RestrMaps,self.degvec,self.CElPos,self.CenterRk,gps_folder,self.Rel,res_folder,subgps,dat_folder,Triangular,inc_folder,self.lastRel,self.MaxelPos,self.MaxelRk,self.pRank,self.knownDeg,self.RelG,Gen,StdMon,self.NilBasis,self.SingularTime,self.completed,'Monomials',self.suffDeg,self.Automatic,self.RelGName,self.NumSubgps,self.GStem,Resl,self.firstOdd,DG,  []  ,self.alpha, pickle_gap_data(_property_dict), pickle_gap_data(list(self._decorator_cache.items())))
        return (RestrMaps,self.degvec,self.CElPos,self.CenterRk,gps_folder,self.Rel,res_folder,subgps,dat_folder,Triangular,inc_folder,self.lastRel,self.MaxelPos,self.MaxelRk,self.pRank,self.knownDeg,self.RelG,Gen,StdMon,self.NilBasis,self.SingularTime,self.completed,'Monomials',self.suffDeg,self.Automatic,self.RelGName,self.NumSubgps,self.GStem,Resl,self.firstOdd,DG,self.Dickson,self.alpha, pickle_gap_data(_property_dict), pickle_gap_data(list(self._decorator_cache.items())))

    def __setstate__(self, s, newroot=None): #s = (RestrMaps,degvec,CElPos,CenterRk,gps_folder,Rel,res_folder,subgps,dat_folder,Triangular,inc_folder,lastRel,MaxelPos,MaxelRk,pRank,knownDeg,RelG,Gen,StdMon,NilBasis,SingularTime,completed,Monomials,suffDeg,Automatic,RelGName,NumSubgps,GStem,Resl,firstOdd,DG,Dickson,alpha, Dict):
        """
        Set the state of ``self``.

        INPUT:

        A list of length 35, as provided by the __getstate__() method of a cohomology ring.

        NOTE:

        In order to save time, not all data are fully reconstructed. For instance,
        the data concerning maximal elementary abelian subgroups are only fully
        reconstructed if it is really necessary for further computation.

        NOTE:

        Pickles did change (previously, __getstate__() returned a list of length 34),
        but old pickles can still be processed.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cohomology import COHO
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

        Now, we initialize a cohomology ring "without properties"::

            sage: K = COHO()
            sage: print(K.knownDeg)
            None

        We change ``K`` into the same state as ``H``, making ``K`` a copy of ``H``::

            sage: K.__setstate__(H.__getstate__())
            sage: print(K)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        However, not all attributes are present at that point. For example,
        the attribute 'subgps' does not exist, yet::

            sage: 'subgps' in K.__dict__
            False

        Nevertheless, it is no problem to call the 'subgps' attribute. The technical
        details:

        - Initially, from the point of view of Python, 'subgps' is not an attribute.
        - Hence, H.subgps results in calling ``H.__getattr__('subgps')``
        - We implemented the __getattr__() method such that a call for 'subgps'
          will reconstruct and return the subgroup data.
        - Hence, eventually, 'subgps' will be known to Python as an attribute.

        The following lines should explain these technical details::

            sage: 'subgps' in K.__dict__
            False
            sage: CohomologyRing.global_options('debug')
            sage: sorted(K.subgps.items())
            H^*(D8; GF(2)):
                Inserting SmallGroup(4,2) as a subgroup
            _get_p_group_from_cache_or_db:
                Got H^*(SmallGroup(4,2); GF(2)) from cache
            H^*(D8; GF(2)):
                Inserting SmallGroup(2,1) as a subgroup
            _get_p_group_from_cache_or_db:
                Got H^*(SmallGroup(2,1); GF(2)) from cache
            H^*(D8; GF(2)):
                Reconstructing subgroup data
            [((2, 1), H^*(SmallGroup(2,1); GF(2))), ((4, 2), H^*(SmallGroup(4,2); GF(2)))]
            sage: 'subgps' in K.__dict__
            True

        """
        if len(s)==34:
            RestrMaps,degvec,CElPos,CenterRk,gps_folder,Rel,res_folder,subgps,dat_folder,Triangular,inc_folder,lastRel,MaxelPos,MaxelRk,pRank,knownDeg,RelG,Gen,StdMon,NilBasis,SingularTime,completed,Monomials,suffDeg,Automatic,RelGName,NumSubgps,GStem,Resl,firstOdd,DG,Dickson,alpha, Dict = s
            cache = []
        elif len(s)==35:
            RestrMaps,degvec,CElPos,CenterRk,gps_folder,Rel,res_folder,subgps,dat_folder,Triangular,inc_folder,lastRel,MaxelPos,MaxelRk,pRank,knownDeg,RelG,Gen,StdMon,NilBasis,SingularTime,completed,Monomials,suffDeg,Automatic,RelGName,NumSubgps,GStem,Resl,firstOdd,DG,Dickson,alpha, Dict, cache = s
        else:
            raise ValueError("wrong number of arguments")
        opts = dict(coho_options)
        coho_options['autolift']=False
        coho_options['save']=False
        coho_options['reload']=True
        cdef int p
        # In contrast to the data files, our folders are not supposed to be symlinks
        # Hence, here it is realpath
        res_folder = os.path.realpath(res_folder)
        gps_folder = os.path.realpath(gps_folder)
        dat_folder = os.path.realpath(dat_folder)
        inc_folder = os.path.realpath(inc_folder)
        gps_folder = os.path.split(gps_folder)[1]
        res_folder = os.path.join(gps_folder, os.path.split(res_folder)[1])
        dat_folder = os.path.join(gps_folder, os.path.split(dat_folder)[1])
        inc_folder = os.path.join(gps_folder, os.path.split(inc_folder)[1])

        try:
            ## First, the "Additional Properties" are reconstructed
            for X,Y in unpickle_gap_data(Dict):
                self._property_dict[X]=Y
            self._decorator_cache = tmp_dict = dict()
            for k,v in cache:
                try:
                    tmp_dict[unpickle_gap_data(k)] = unpickle_gap_data(v)
                except Exception:
                    coho_logger.error("Unable to reconstruct some data in GAP", None, exc_info=1)

            ##########
            ## Try to find the folder in which the cohomology data are rooted.
            ## We have special places for workspace and local sources
            root = self.root
            if root == '@user_db@':
                root = COHO.workspace
            elif root == '@public_db@':
                root = COHO.local_sources
            oldroot = None

            if (newroot is not None) and (root!=newroot):
                oldroot = root
                root = newroot
            self.setprop('root', root)

            self.degvec = degvec
            self.CElPos = CElPos
            self.CenterRk = CenterRk
            self.gps_folder = os.path.join(root,gps_folder)
            self.Rel = Rel
            self.res_folder = os.path.join(root,res_folder)
            self.dat_folder = os.path.join(root,dat_folder)
            self.inc_folder = os.path.join(root,inc_folder)
            self.lastRel = lastRel
            self.MaxelPos = MaxelPos
            self.MaxelRk = MaxelRk
            self.pRank = pRank
            self.knownDeg = knownDeg
            self.RelG = RelG
            self.completed = completed
            self.suffDeg = suffDeg
            self.RelGName = RelGName
            self.NumSubgps = NumSubgps
            self.GStem = GStem
            self.Dickson = Dickson
            self.alpha = alpha

            if isinstance(Resl, (str, unicode)):
                Resl = str(Resl)
                if (oldroot is not None):
                    coho_options['@oldroot@'] = oldroot
                coho_options['@newroot@'] = root
                try:
                    if Resl.endswith('.sobj'):
                        self.Resl = load(os.path.join(root,Resl))  # realpath here?
                    else:
                        self.Resl = load(os.path.join(root,Resl+'.sobj'))  # realpath here?
                except (OSError, IOError, RuntimeError):
                    raise IOError("Unable to read resolution saved at "+os.path.join(root,Resl))
                try:
                    del coho_options['@newroot@']
                except KeyError:
                    pass
                ## The resolution is in a readable file.
                ## We don't need to relocate the data right now.
                if '@oldroot@' in coho_options:
                    del coho_options['@oldroot@']
            else:
                MaxDeg = max([0]+[X[0] for X in Gen])
                self.Resl = None
                try:
                    for K in Resl[4].keys():
                        self.Resl = (K[1]).resolution()
                        break
                except:
                    print(Resl)
                    print(Resl[4])
                    print(type(Resl[4]))
                    raise
            (<RESL>self.Resl).G_Alg.groupname = self.printed_group_name()
            Ring.__init__(self,GF(self.Resl.coef()))

            self.firstOdd = firstOdd
            n = self.knownDeg
            #########
            ## The following data need special treatment:
            ## Subgroups: Quick-Loading --- they will be fully reconstructed later!
            if subgps:
                if (oldroot is not None):
                    oldroot = '@'+oldroot
                    for i in range(len(subgps)):
                        subgps[i]=(subgps[i][0],('@'+subgps[i][1]).replace(oldroot,newroot))
                self.setprop('SUBGPS',subgps)

            ## Cochains:
            self.Gen = [COCH(self,X[0],X[1],X[2],rdeg=X[3],ydeg=X[4], is_polyrep=True) for X in Gen]
            self.Triangular = {}
            for i,Tr in Triangular:
                self.Triangular[i] = [COCH(self,X[0],X[1],X[2], is_polyrep=True) for X in Tr]
            self.NilBasis = NilBasis
            if isinstance(Monomials, (str, unicode)):
                self.Monomials = {'bla':1}
                self.importMonomials()
            else:
                self.Monomials = {}
                for i,Mo in Monomials:
                    self.Monomials[i] = COCH(self,Mo[0],Mo[1],Mo[2], is_polyrep=True)

            ## Chain maps: Quick-Loading --- they will be fully reconstructed later!
            if subgps:
                self.setprop('RESTRMAPS', RestrMaps)

            ###
            ## The key for uniqueness of parent structures
            if self._key is not None: # we will explicitly provide the second half of the key (file location),
                                      # but will try to re-use the first half (group description)
                # Problem: It could be that the old key was not created properly, e.g.,
                # by referring to a GAP session. If this is the case, we need to reset it.
                try:
                    h = hash(self._key[0])
                    self.setprop('_key', (self._key[0], os.path.join(root,dat_folder,'State')))
                except Exception as msg:
                    coho_logger.error("Stored cache key was not readable", None, exc_info=1)
                    coho_logger.warning("> Will try to reconstruct it from the group identifier %r", None, GStem)
                    self.delprop('_key')
            if self._key is None:
                try:
                    q,n = [Integer(nb) for nb in GStem.split('gp')]
                    self.setprop('_key', ((q,n),os.path.join(self.dat_folder,'State')))
                except (TypeError, ValueError):
                    print('WARNING: No good group key found')
                    print('Please choose a string ``s`` that provides a')
                    print('definition of a finite p-Group in Gap and do')
                    print("    sage: H.setprop('_key',(s,%s))"%(os.path.join(self.dat_folder,'State')))
                    print('where ``H`` denotes the name of this cohomology ring.')
                    self.setprop('_key', ((GStem,),os.path.join(dat_folder,'State')))
            # use the updated _key for inserting self into the cache
            from pGroupCohomology import CohomologyRing
            _cache = CohomologyRing._cache
            if not ((self._key is None) or self._key in _cache):
                _cache[self._key] = self

            ################
            # Finally, we reconstruct the attributes in Singular:
            # GenS, StdMon; a ring and the relation ideal in singular.
            p = self.Resl.coef()
            if p!=2:
                singular.LIB("ncall.lib")
            singular.LIB('general.lib')
            singular.LIB('poly.lib')
            singular.LIB('dickson.lib')
            if singular.eval('defined(i)')=='0':
                singular.eval('int i')
            else:
                if singular.eval('typeof(i)')!='int':
                    coho_options.clear()
                    coho_options.update(opts)
                    raise RuntimeError("Singular has defined that i is not an integer - but we need i as integer!")
            if Gen:
                if self._property_dict.get('use_dp'):
                    if len(self.degvec)==1:
                        singular.eval('ring tmp = %d,(%s),%s'%(p, ','.join([x.name() for x in self.Gen]), '(a(%d),dp)'%(self.degvec[0])))
                    else:
                        singular.eval('ring tmp = %d,(%s),%s'%(p, ','.join([x.name() for x in self.Gen]), '(wp%s)'%(str(tuple(self.degvec)))))
                else:
                    self._makeOrderMatrix_()
                    singular.eval('ring tmp = %d,(%s),M(%sM)'%(p, ','.join([x.name() for x in self.Gen]), self.prefix))
                if self.Resl.coef()!=2:   # non-commutative case
                    singular.eval('degBound = 0')
                    singular.eval('def %sr(%d) = superCommutative(%d,%d)'%(self.prefix,n,self.firstOdd+1, len(self.Gen)))
                else:
                    singular.eval('def %sr(%d) = tmp'%(self.prefix,n))
                singular.eval('setring %sr(%d)'%(self.prefix,n))
                singular.eval('kill tmp')
                self.GenS = singular('%sr(%d)'%(self.prefix,n))
                if self.RelG:
                    singular.eval('ideal %sI = %s'%(self.prefix,','.join(self.RelG)))
                else:
                    if self.Rel:
                        singular.eval('ideal %sI = %s'%(self.prefix,','.join(self.Rel)))
                        self.delprop('completeGroebner')
                    else:
                        singular.eval('ideal %sI'%(self.prefix))
                singular.eval(('ideal %sDG = '%self.prefix)+','.join(DG))

            self.StdMon = {0:{'1':singular('1')}}
            for nkey,StdMonN in StdMon: # There will only be a standard monomial, if
                                        # there are generators. Hence, IF we are defining
                                        # an ideal below, it is granted that the basering
                                        # is defined.
                self.StdMon[nkey]={}
                for monkey,STD in StdMonN:
                    if monkey!='1':
                        self.StdMon[nkey][monkey] = singular.ideal(STD)
                    else:
                        self.StdMon[nkey][monkey] = singular('1')
        finally:
            coho_options.clear()
            coho_options.update(opts)

    def autosave_name(self):
        """
        Return the name of the file under which ``self`` is automatically saved.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: K = load(H.autosave_name())
            sage: print(K)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        """
        return os.path.join(self.gps_folder,'H'+self.GStem+'.sobj')

####################################

    def exportMonomials(self):
        """
        Save previously computed standard monomials in a standard location.

        NOTE:

        This method is used when saving a cohomology ring. The saved standard
        monomials can be reloaded with :meth:`importMonomials`, but this requires
        that the dictionary ``self.Monomials`` has the key ``'bla'``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: L1 = list(H.Monomials.items())
            sage: L1.sort()
            sage: L1
            [('b_1_0', b_1_0: 1-Cocycle in H^*(D8; GF(2))),
             ('b_1_0b_1_0', (b_1_0)*(b_1_0): 2-Cocycle in H^*(D8; GF(2))),
             ('b_1_0b_1_1', (b_1_0)*(b_1_1): 2-Cocycle in H^*(D8; GF(2))),
             ('b_1_1', b_1_1: 1-Cocycle in H^*(D8; GF(2))),
             ('b_1_1b_1_1', (b_1_1)*(b_1_1): 2-Cocycle in H^*(D8; GF(2))),
             ('c_2_2', c_2_2: 2-Cocycle in H^*(D8; GF(2)))]
            sage: H.exportMonomials()
            sage: H.Monomials={'bla':1}
            sage: H.importMonomials()
            sage: L2 = list(H.Monomials.items())
            sage: L2.sort()
            sage: L1 == L2
            True

        """
        cdef COCH X
        if not 'bla' in self.Monomials:
            safe_save([[i,[X.Deg,X.Name,X.Data]] for i,X in self.Monomials.items()], os.path.join(self.dat_folder,'M%s.sobj'%self.GStem))

    def importMonomials(self):
        """
        Reload previously exported standard monomials.

        NOTE:

        This method is used when reloading a cohomology ring. There
        is no need to ever call this method explicitly, so, the
        following is not a use case.

        The method requires that the dictionary self.Monomials has the
        key ``'bla'``.  Otherwise, the monomials, that are stored in
        some standard location, will not be reloaded.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: L1 = list(H.Monomials.items())
            sage: L1.sort()
            sage: L1
            [('b_1_0', b_1_0: 1-Cocycle in H^*(D8; GF(2))),
             ('b_1_0b_1_0', (b_1_0)*(b_1_0): 2-Cocycle in H^*(D8; GF(2))),
             ('b_1_0b_1_1', (b_1_0)*(b_1_1): 2-Cocycle in H^*(D8; GF(2))),
             ('b_1_1', b_1_1: 1-Cocycle in H^*(D8; GF(2))),
             ('b_1_1b_1_1', (b_1_1)*(b_1_1): 2-Cocycle in H^*(D8; GF(2))),
             ('c_2_2', c_2_2: 2-Cocycle in H^*(D8; GF(2)))]
            sage: H.Monomials={'bla':1}

        Since, by default, the cohomology ring was automatically saved, the monomials
        are available in some file. So, we can import them::

            sage: H.importMonomials()
            sage: L2 = list(H.Monomials.items())
            sage: L2.sort()
            sage: L2 == L1
            True

        """
        cdef dict D = {}
        if 'bla' in self.Monomials:
            coho_logger.info('Import monomials',self)
            Monomials = load(os.path.join(self.dat_folder,'M'+self.GStem+'.sobj'))  # realpath here?
            for i,Mo in Monomials:
                D[i] = COCH(self,Mo[0],Mo[1],Mo[2], is_polyrep=True)
            self.Monomials = D


    def decomposable_classes(self, int n, forced=False):
        """
        Return a basis for the degree `n` cohomology, expressed by monomials.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.decomposable_classes(3)
            [(b_1_0)*((b_1_0)*(b_1_0)): 3-Cocycle in H^*(D8; GF(2)),
             (b_1_1)*((b_1_1)*(b_1_1)): 3-Cocycle in H^*(D8; GF(2)),
             (b_1_0)*(c_2_2): 3-Cocycle in H^*(D8; GF(2)),
             (b_1_1)*(c_2_2): 3-Cocycle in H^*(D8; GF(2))]

        """
        cdef list DecGen = self.Triangular.get(n)
        if (DecGen is not None) and not forced:
            return DecGen
        cdef RESL R
        R = self.Resl
        DecGen=[]  # will be a triangular basis of the sub space of decomposables of H^n
        cdef list VSGen=self.Resl.rank(n)*[1]
        cdef list pivot=[]
        cdef COCH Cand # will be the 'next candidate' for a decomposable generator or a relation

        cdef list MonExp,lastPiv, ComL
        cdef int i,k,m,j
        cdef FEL f, f2
        FfSetField(self.base_ring().order())
        cdef int lenMonExp, lAn, lenDecGen
        if self.Gen!=[]:  # there can only be decomposables if there are generators, yet
            ####################################
            # We must lift self.RelG to the new degree.
            # First, switch to the previous ring
            self.set_ring()
            singular.eval('ideal %sDGtmp'%self.prefix)
            sizeG = int(singular.eval('ncols(%sI)'%(self.prefix)))

            #######################################
            # Get standard monomials:
            self._makeStdMon(n,"Mon")
            if singular.eval('Mon[1]')!='0':
                # get list of exponent vectors of the standard monomials
                MonExp = [[int(y.strip()) for y in x.split(',')] for x in \
                          [s.strip() for s in (singular.eval('for (i=1;i<=ncols(Mon);i++) { print(leadexp(Mon[i]));print(\";\");}')+'\n').split(';')] if x]
                lenMonExp = len(MonExp)

                #######################################
                # Perform the products
                for i from 0<= i < lenMonExp:
                    Cand = self.MonToProd(MonExp[i])
                    FfSetNoc(Cand.Data.Data.Noc)
                    j = FfFindPivot(Cand.Data.Data.Data, &f)
                    IsMonomial = True
                    lenDecGen = len(DecGen)
                    if j>=0:
                        Cand = copy(Cand)
                        Cand.set_mtx_globals()
                        for k from 0 <= k < lenDecGen:
                            if (j <= pivot[k]):
                                f2 = FfExtract(Cand.Data.Data.Data, pivot[k])
                                if f2 != FF_ZERO:
                                    Cand.isubmul(DecGen[k], f2)
                                    j = FfFindPivot(Cand.Data.Data.Data, &f)
                                    IsMonomial = False
                                    if j<0:
                                        break
                    if j>=0: # We found a decomposable generator of H^n
                        DecGen.append(Cand/f)
                        if len(DecGen[-1].name()) < 850:
                            singular.eval(('%sDGtmp[%d]='%(self.prefix,len(DecGen)))+DecGen[-1].name())
                        else:
                            ComL = Cand.name().split('-(')
                            DGstr = '%sDGtmp[%d]'%(self.prefix,len(DecGen))
                            singular.eval(DGstr+'='+ComL[0])
                            DGstr = DGstr + '=' + DGstr + '-('
                            for trm in ComL[1:]:
                                try:
                                    singular.eval(DGstr+trm)
                                except:
                                    print(ComL)
                                    print(Cand.name())
                                    raise
                            singular.eval('%sDGtmp[%d]=%sDGtmp[%d]/%d'%(self.prefix,len(DecGen),self.prefix,len(DecGen),f))
                        if not IsMonomial:
                            DecGen[-1].setname(singular.eval('%sDGtmp[%d]'%(self.prefix,len(DecGen))))
                        pivot.append(j)
                        VSGen[j]=0
                    else: ## We found a relation in degree n -- this must not happen,
                          ## since we assume that the ring structure is known out to degree at least n
                        raise RuntimeError("We found an unexpected relation %s for %r"%(Cand.Name, self))
        singular.eval('kill %sDGtmp'%self.prefix)
        self.Triangular[n] = DecGen
        return DecGen

    def reconstructSubgroups(self):
        """
        When loading a cohomology ring, the subgroups are not reconstructed immediately. This is done here.

        NOTE:

        It is not necessary to call this function manually. It is
        done automaticall as soon as the subgroups are requested.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H=CohomologyRing(8,3)

        In this example, we do not want that the cohomology rings are cached.
        Hence, we destroy cache::

            sage: CohomologyRing._cache.clear()
            sage: K = loads(dumps(H))
            sage: K is H
            False

        The point is that ``subgps`` is an attribute that is not immediately
        created when a cohomology ring is loaded. So, although ``H`` has this
        attribute, ``K`` hasn't::

            sage: 'subgps' in H.__dict__
            True
            sage: 'subgps' in K.__dict__
            False

        It is created using this method::

            sage: K.reconstructSubgroups()
            sage: 'subgps' in K.__dict__
            True

        The method is automatically called when trying to access the ``subgps``
        attribute::

            sage: for k,v in list(CohomologyRing._cache.items()):
            ....:     if v is K:
            ....:         del CohomologyRing._cache[k]
            sage: L = loads(dumps(K))
            sage: 'subgps' in L.__dict__
            False
            sage: CohomologyRing.global_options('info')
            sage: sorted(L.subgps.items())
            H^*(D8; GF(2)):
                Inserting SmallGroup(4,2) as a subgroup
                Inserting SmallGroup(2,1) as a subgroup
                Reconstructing subgroup data
            [((2, 1), H^*(SmallGroup(2,1); GF(2))), ((4, 2), H^*(SmallGroup(4,2); GF(2)))]

        """
        from pGroupCohomology import CohomologyRing
        if not self.SUBGPS:
            return
        self.subgps = {}
        root = self.root
        saveopts = dict(coho_options)
        for i,L in self.SUBGPS:
            coho_logger.info("Inserting SmallGroup(%d,%d) as a subgroup", self, i[0],i[1])
            self.subgps[i] = CohomologyRing(i[0],i[1], websource=False)
            self.subgps[i].make()
            if not (self.sgpDickson or self.useElimination):
                self.dickson_in_subgroup(i)
        coho_options.clear()
        coho_options.update(saveopts)
        if self.degvec:
            n=max(self.degvec)
            for sgp in self.subgps.values():
                while (sgp.knownDeg < n):
                    sgp.next(Forced=True,KeepDecomposables=True)
        if self.sgpDickson:
            self.subgpDickson = {}
            coho_logger.info("Reconstructing subgroup data",self)
            for i, DicksonList in self.sgpDickson:
                self.subgpDickson[i] = [COCH(self.subgps[i],X[0],X[1],X[2], is_polyrep=True) for X in DicksonList]
        ## Chain maps:
        self.RestrMaps = {}
        for i,Restr in self.RESTRMAPS:
            self.RestrMaps[i]=[Restr[0], self.hom(Restr[1][0],self.subgps[Restr[0]],Restr[1][1][0], 0)]
            self.RestrMaps[i][1][1]=Restr[1][1][1:]    # This inserts the list of lifts;
        del self._property_dict['RESTRMAPS']
        if coho_options['sparse']:
            for i,X in self.RestrMaps.items():
                X[1].exportData(os.path.join(self.inc_folder,self.GStem+'sg'+str(i)+'_'))
        del self._property_dict['SUBGPS']
        if self.sgpDickson:
            del self._property_dict['sgpDickson']

    def __richcmp__(self, other, op):
        """
        ``self`` and ``other`` are considered equal, if their unique keys
        describe the *same* group (not just isomorphic groups), and if
        the generators and relations match.

        NOTE:

        Usually, one would create a cohomology ring using
        :func:`~pGroupCohomology.CohomologyRing`. Then, the resulting
        cohomology rings are cached, so that two cohomology rings of
        the *same* group with data stored in the *same* location are
        not only equal but identical.

        TESTS::

            sage: from pGroupCohomology.cohomology import COHO
            sage: tmp_root1 = tmp_dir()
            sage: tmp_root2 = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.reset()
            sage: H1 = COHO(8,3,root=tmp_root1)
            sage: H2 = COHO(8,3,root=tmp_root2)
            sage: H1.make()
            sage: H2.make()
            sage: H1 == H2      # indirect doctest
            True
            sage: H1 is H2
            False
            sage: H3 = COHO(8,2,root=tmp_root1)
            sage: H3.make()
            sage: H1 == H3
            False
            sage: H1 < H3
            True

        """
        if not isinstance(other,COHO):
            return op in [op_LT, op_NE, op_GT]
        if self._key[0] != other._key[0]:
            return richcmp(self.group(), other.group(), op)
        if [g.name() for g in self.Gen] != [g.name() for g in other.Gen]:
            return richcmp([g.name() for g in self.Gen],
                           [g.name() for g in other.Gen],
                           op)
        return richcmp(self.Rel, other.Rel, op)

    ######################################
    ### String representations and other information

    def _repr_(self):
        """
        Return a brief desctiption of the cohomology ring.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: H = CohomologyRing(8,3)
            sage: H      # indirect doctest
            H^*(D8; GF(2))

        """
        return "H^*({}; GF({}))".format(self.printed_group_name(), self.Resl.coef())

    def printed_group_name(self):
        """
        Group identifier used for printing.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.reset()
            sage: CohomologyRing(8,3).printed_group_name()
            'D8'
            sage: CohomologyRing(64,167).printed_group_name()
            'SmallGroup(64,167)'

        """
        if self.GroupName:
            return self.GroupName
        if self._key:
            GroupKey = self._key[0]
            if len(GroupKey)==1:
                if len(GroupKey[0])<20:
                    return GroupKey[0]
            else:
                if GroupKey[1]>0:
                    return 'SmallGroup(%d,%d)'%GroupKey
        return self.GStem


    def label(self):
        """
        Provide a short description of this cohomology ring.

        NOTE:

        In some cases, this is equal to the string representation.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.label()
            'H^*(8gp3; GF(2))'
            sage: H
            H^*(D8; GF(2))
            sage: H = CohomologyRing(64,167)
            sage: H
            H^*(SmallGroup(64,167); GF(2))
            sage: H.label()
            'H^*(64gp167; GF(2))'

        """
        return "H^*(%s; GF(%d))"%(self.GStem, self.Resl.coef())

    def _html_(self):
        """
        Return a brief html desctiption of the cohomology ring.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H._html_()
            'H<sup>*</sup>(D8; GF(2))'

        """
        if self.GroupName:
            GStem = self.GroupName
        else:
            GroupKey = self._key[0]
            if len(GroupKey)==1:
                if len(GroupKey[0])<20:
                    GStem = GroupKey[0]
                else:
                    GStem = self.GStem
            else:
                if GroupKey[1]>0:
                    GStem = 'SmallGroup(%d,%d)'%GroupKey
                else:
                    GStem = self.GStem
        return "H<sup>*</sup>(%s; GF(%d))"%(GStem, self.Resl.coef())

    def __str__(self):
        """
        Return detailed information on the cohomology ring.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: print(H)       # indirect doctest
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        """
        if self.GroupDescr:
            GStem = self.GroupDescr
        elif self.GroupName:
            GStem = self.GroupName
        else:
            GroupKey = self._key[0]
            if len(GroupKey)==1:
                GStem = GroupKey[0]
            else:
                if GroupKey[1]>0:
                    GStem = 'SmallGroup(%d,%d)'%GroupKey
                else:
                    GStem = self.GStem
        if self.completed:
            return """
Cohomology ring of %s with coefficients in GF(%d)

Computation complete
Minimal list of generators:
%s
Minimal list of algebraic relations:
%s
            """%(GStem, self.Resl.coef(), '['+',\n '.join([X.__repr__() for X in self.Gen])+']', '['+',\n '.join([X for X in self.Rel])+']')
        else:
            return """
Cohomology ring of %s with coefficients in GF(%d)

Computed up to degree %d
Minimal list of generators:
%s
Minimal list of algebraic relations:
%s
            """%(GStem, self.Resl.coef(), self.knownDeg, '['+',\n '.join([X.__repr__() for X in self.Gen])+']', '['+',\n '.join([X for X in self.Rel])+']')

    def _latex_(self):
        r"""
        LaTeX representation of ``self``.

        NOTE:

        Using the attribute ``GroupLatexName``, the type
        setting of the group can be influenced.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,5)
            sage: latex(H)      # indirect doctest
            H^\ast(SmallGroup(8,5); \mathbb F_2)
            sage: H.group().IsElementaryAbelian()
            true
            sage: H.setprop('GroupLatexName',r'C_2\times C_2\times C_2')
            sage: latex(H)
            H^\ast(C_2\times C_2\times C_2; \mathbb F_2)

        """
        if self.GroupLatexName:
            GStem = self.GroupLatexName
        elif self.GroupName:
            GStem = self.GroupName
        else:
            GroupKey = self._key[0]
            if len(GroupKey)==1:
                GStem = GroupKey[0]
            else:
                if GroupKey[1]>0:
                    GStem = 'SmallGroup(%d,%d)'%GroupKey
                else:
                    GStem = self.GStem
        return r"H^\ast(%s; \mathbb F_%d)"%(GStem, self.Resl.coef())

    def group(self):
        """
        Return the group over which ``self`` is defined, as a permutation group.

        OUTPUT:

        Let `G` be the group for which self is defined. Recall that in
        the case of prime power groups it is assumed that the first,
        say `n`, generators of `G` form a minimal generating
        set. Then, the output of :meth:`group` is a permutation group
        `G_P`, defined in the libgap interface, with precisely `n`
        generators, so that mapping generator `i` of `G` to generator
        `i` of `G_P`, for `i=1,...,n`, results in a group isomorphism-

        NOTE:

        ``CohomologyRing(self.group())`` is always equal to
        ``self``. It is often even identical with ``self``,
        namely if the Small Groups address can be determined, as
        in the following example.


        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: G = H.group()
            sage: G
            Group([ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ])
            sage: H1 = CohomologyRing(G, GroupName='NewD8')
            sage: H is H1
            True

        """
        if self._gap_group is not None:
#~                 self._gap_group._check_valid()
            return self._gap_group
        from pGroupCohomology.auxiliaries import gap, _gap_reset_random_seed
        _gap_reset_random_seed()
        if isinstance(self._key[0], basestring):
#~             self._gap_group = gap.eval(self._key[0])
            # self._key[0] may be too long for libgap to evaluate. So, we split it into chewable pieces.
            self._gap_group = _gap_eval_string(self._key[0]).asPermgroup()
        elif len(self._key[0])==1:
            self._gap_group = _gap_eval_string(self._key[0][0]).asPermgroup()
#~                 self._gap_group = gap.eval('Group(verifiedMinGens(regularPermutationAction(%s: forceDefiningGenerators)))'%(self._gap_group.name()))
        else:
            self._gap_group = gap.SmallGroup(self._key[0][0],self._key[0][1]).asPermgroup()
        return self._gap_group

    @permanent_result
    def group_is_abelian(self):
        """
        Tell whether the associated group is abelian.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: CohomologyRing(8,3).group_is_abelian()
            False
            sage: CohomologyRing(8,2).group_is_abelian()
            True

        """
        return bool(self.group().IsAbelian())

###################
## Methods for setting/getting additional properties of the group
    def setprop(self,key, value):
        """
        Define a property of ``self``.

        INPUT:

        - ``key``, a string
        - ``value``, any object

        OUTPUT:

        ``value`` is now available as an attribute ``key`` of self.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: print(H.foobar)
            None
            sage: print(H._foobar)
            None
            sage: print(H.foobar_)
            None

        Note that if an attribute hasn't been defined, ``None`` is returned.
        The only exceptions are undefined attributes that start and end with
        an underscore::

            sage: H._foobar_
            Traceback (most recent call last):
            ...
            AttributeError: 'COHO' object has no attribute '_foobar_'

        Now, we provide ``_foobar_`` with a meaning, and then it works::

            sage: H.setprop('_foobar_', 'It works!')
            sage: print(H._foobar_)
            It works!

        """
        self._property_dict[key] = value

    def __dir__(self):
        """
        Implementing introspection.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: [a for a in dir(H) if a.startswith('f')]    #indirect doctest
            ['filter_degree_type',
             'filter_regular_gready_parameters',
             'filter_regular_parameters',
             'find_dickson',
             'find_dickson_in_subgroup',
             'find_small_last_parameter',
             'firstOdd',
             'fraction_field',
             'from_base_ring']
            sage: H.setprop('foo',1)
            sage: [a for a in dir(H) if a.startswith('f')]
            ['filter_degree_type',
             'filter_regular_gready_parameters',
             'filter_regular_parameters',
             'find_dickson',
             'find_dickson_in_subgroup',
             'find_small_last_parameter',
             'firstOdd',
             'foo',
             'fraction_field',
             'from_base_ring']
            sage: H.foo_bar = 1
            sage: [a for a in dir(H) if a.startswith('f')]
            ['filter_degree_type',
             'filter_regular_gready_parameters',
             'filter_regular_parameters',
             'find_dickson',
             'find_dickson_in_subgroup',
             'find_small_last_parameter',
             'firstOdd',
             'foo',
             'foo_bar',
             'fraction_field',
             'from_base_ring']

        """
        return dir(self.__class__) + list(self.__dict__.keys()) + list(self._property_dict.keys())

    def trait_names(self):
        """
        Implement tab completion.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: import sage.interfaces.tab_completion as tc
            sage: tc.completions('H.f',globals())  # indirect doctest
            ['H.filter_degree_type',
             'H.filter_regular_gready_parameters',
             'H.filter_regular_parameters',
             'H.find_dickson',
             'H.find_dickson_in_subgroup',
             'H.find_small_last_parameter',
             'H.firstOdd',
             'H.fraction_field',
             'H.from_base_ring']

        """
        return dir(self)

    @property
    def _default_filename(self):
        try:
            return self.__default_filename
        except AttributeError:
            default_filename_error_message.cls = type(self)
            raise AttributeError(default_filename_error_message)

    @_default_filename.deleter
    def _default_filename(self):
        try:
            del self.__default_filename
        except AttributeError:
            default_filename_error_message.cls = type(self)
            raise AttributeError(default_filename_error_message)

    @_default_filename.setter
    def _default_filename(self, defaultname):
        try:
            if self._property_dict.get('_need_new_root'):
                coho_logger.warning("The data for the cohomology ring at <%x> have apparently been moved.", "Unpickling a cohomology ring", id(self))
                if isinstance(self._property_dict['_need_new_root'], (str, unicode)):
                    newroot = str(self._property_dict['_need_new_root'])
                    default_name = str(os.path.join(newroot,self.GStem,'H'+self.GStem+'.sobj'))
                else:
                    # try to infer the new location from the file this ring was loaded from
                    newroot = os.path.split(os.path.split(defaultname)[0])[0]
                    default_name = defaultname
                try:
                    ST = load(os.path.join(os.path.split(defaultname)[0],'dat','State.sobj'))  # realpath here?
                except (OSError, IOError):
                    try:
                        newroot = os.path.split(os.path.split(defaultname)[0])[0]
                        default_name = defaultname
                        ST = load(os.path.join(os.path.split(defaultname)[0],'dat','State.sobj'))
                    except (OSError, IOError):
                        coho_logger.critical("The new location of data for the cohomology ring at <%x> can't be reconstructed.", "Unpickling a cohomology ring", id(self))
                        coho_logger.critical("Please try to assign the correct value of `_default_filename` to it.", "Unpickling a cohomology ring")
                        return
                self.delprop('_need_new_root')
                self.__setstate__(ST, newroot=newroot)
                self.setprop('_dont_save_the_State', True)
                try:
                    coho_logger.warning("Try to update cohomology data on disk", self)
                    safe_save(self, self.autosave_name())
                    coho_logger.warning( "> successful",self)
                except (OSError, IOError, RuntimeError):
                    self.delprop('_dont_save_the_State')
                    coho_logger.critical( "CRITICAL: No write permission", self)
        finally:
            self.__default_filename = defaultname

    def __getattr__(self,key):
        """
        H.foo:  return the value of attribute/property 'foo' (None, if undefined).

        NOTE:

        There will only be an attribute error if foo is not an attribute and
        starts and ends with an underscore. Tab completion and introspection
        are implemented in Python-2, but not in Python-3 yet.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: print(H.foobar)      # indirect doctest
            None
            sage: print(H._foobar)
            None
            sage: print(H.foobar_)
            None
            sage: '_foobar_' in dir(H)
            False
            sage: 'foobar' in dir(H)
            False
            sage: import sage.interfaces.tab_completion as tc
            sage: tc.completions('H.f',globals())
            ['H.filter_degree_type',
             'H.filter_regular_gready_parameters',
             'H.filter_regular_parameters',
             'H.find_dickson',
             'H.find_dickson_in_subgroup',
             'H.find_small_last_parameter',
             'H.firstOdd',
             'H.fraction_field',
             'H.from_base_ring']

        Note that if an attribute hasn't been defined, ``None`` is returned.
        The only exception are undefined attributes that start and end with
        an underscore, or if it starts with "_cached"::

            sage: H._foobar_
            Traceback (most recent call last):
            ...
            AttributeError: 'COHO' object has no attribute '_foobar_'
            sage: H._cached_foo
            Traceback (most recent call last):
            ...
            AttributeError: 'COHO' object has no attribute '_cached_foo'

        Now, we provide ``_foobar_`` with a meaning, and then it works::

            sage: H.setprop('_foobar_', 'It works!')
            sage: print(H._foobar_)
            It works!
            sage: '_foobar_' in dir(H)
            True
            sage: 'H._foobar_' in tc.completions('H._f',globals())
            True
            sage: H.delprop('_foobar_')
            sage: '_foobar_' in dir(H)
            False
            sage: 'H._foobar_' in tc.completions('H._f',globals())
            False

        """
        # If a cohomology ring is loaded from a file which was moved *together with
        # all the ring data* (!!) to a new location then an uninitialized ring is
        # returned. Hence, when working with it, very soon this __getattr__ method
        # will be called. At this point, _default_filename might tell us where the
        # file and hence the ring data are located!
        import os
        if key == '_default_filename': # This ought to be a *proper* attribute, no fake attribute!
            raise AttributeError("'pGroupCohomology.cohomology.COHO' object has no attribute '_default_filename'")
        if key == '__members__':
            return self._property_dict.keys()

        # After quickloading, the attributes "subgps" and "RestrMaps" are not defined.
        # Hence, if these attributes are required in that case, __getattr__ is called,
        # and we reconstruct the subgroups first before returning the required data.
        if (key=="subgps") and ('SUBGPS' in self._property_dict):
            self.reconstructSubgroups()
            return self.subgps
        if (key=="RestrMaps"):
            if  ('SUBGPS' in self._property_dict or 'RESTRMAPS' in self._property_dict):
                self.reconstructSubgroups()
            else:
                self.RestrMaps = {}
            return self.RestrMaps
        try:
            return self._property_dict[key]
        except KeyError:
            if key[0]==key[-1]=='_':
                raise AttributeError("'COHO' object has no attribute '%s'"%(key))
            if key.startswith('_cached'):
                raise AttributeError("'COHO' object has no attribute '%s'"%(key))
            return None

    def delprop(self,key):
        """
        Delete a property of ``self``.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.setprop('_foobar_', 'It works!')
            sage: print(H._foobar_)
            It works!
            sage: H.delprop('_foobar_')
            sage: H._foobar_
            Traceback (most recent call last):
            ...
            AttributeError: 'COHO' object has no attribute '_foobar_'

        """
        self._property_dict.pop(key,None)

    def properties(self):
        """
        List the names of the custom attributes set with :meth:`setprop`.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: sorted(H.properties())
            ['DicksonExp',
             'GroupDescr',
             'GroupName',
             'KeepBases',
             '_key',
             'auto',
             'root',
             'sgpDickson',
             'useElimination',
             'useFactorization']

        During the computation, more properties are added::

            sage: H.make()
            sage: sorted(H.properties())
            ['DicksonExp',
             'GroupDescr',
             'GroupName',
             'KeepBases',
             '_SymondsTestdata',
             '_key',
             '_max_module_deg',
             '_method',
             '_parameters_for_criterion',
             'auto',
             'completeGroebner',
             'root',
             'sgpDickson',
             'useElimination',
             'useFactorization']

        """
        return self._property_dict.keys()

    # The following is important for coercion!
    def _an_element_(self):
        """
        Return an element.

        NOTE:

        This method is important for making coercion work, since
        actions on a cohomology ring are obtained by inspecting
        the ``_lmul_`` method of elements.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)

        If there are no generators computed yet, a cohomology class
        of degree zero is returned::

            sage: H.an_element()   # indirect doctest
            1: 0-Cocycle in H^*(D8; GF(2))

        Otherwise, a generator in positive degree is returned.
        Since the result of ``an_element`` (which used ``_an_element_``)
        is cached, we empty the cache first::

            sage: try:
            ....:     del H._cache_an_element
            ....: except AttributeError:
            ....:     del H.__an_element
            sage: H.make()
            sage: H.an_element()
            b_1_0: 1-Cocycle in H^*(D8; GF(2))

        """
        if not self.Gen:
            return self.from_base_ring(1)
        return self.Gen[0]

    def gen(self,i):
        """
        Return generators of ``self``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()

        Generator number zero is 1 in the base ring of ``H``::

            sage: H.0
            1
            sage: H.1     # indirect doctest
            c_2_2: 2-Cocycle in H^*(D8; GF(2))
            sage: H.2
            b_1_0: 1-Cocycle in H^*(D8; GF(2))
            sage: print(H.1*H.2)
            3-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 0 1 0]

        """
        if i:
            return self.Gen[i-1]
        else:
            return self.base_ring()(1)

    def ngens(self):
        """
        Return the number of generators of ``self``.

        NOTE:

        We consider the scalar ``1`` as a generator.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.ngens()
            4
            sage: len(H.gens())
            4

        """
        return len(self.Gen)+1

    def gens(self):
        """
        Return the list of generators of ``self``.

        NOTE:

        We consider the scalar ``1`` as a generator. The
        list of generators may change if an incomplete
        cohomology computation is continued.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make(1)
            sage: H.gens()
            [1, b_1_0: 1-Cocycle in H^*(D8; GF(2)), b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            sage: H.make()
            sage: H.gens()
            [1,
             c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]

        """
        return [self.base_ring()(1)]+self.Gen

    def rel(self,i):
        """
        Return a relation of ``self``, represented by a string.

        NOTE:

        For `p>2`, any generator `x` of odd degree of the modular cohomology
        ring of a finite `p`-group gives rise to the relation `x^2=0`. We
        refer to such relation as *obvious*. In the current version of our
        package, we list only the non-obvious relations, but this might change
        in future versions.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,3)
            sage: H.make()
            sage: H.rels()
            ['a_1_0^2', 'a_1_0*b_1_1', 'b_2_1*a_1_0', 'b_2_1^2+c_2_2*b_1_1^2']
            sage: H.rel(0)
            'a_1_0^2'
            sage: H.rel(2)
            'b_2_1*a_1_0'

        """
        return self.Rel[i]

    def rels(self):
        """
        Return the list of minimal relations of ``self``, represented by strings.

        NOTE:

        The list of relations may change if an incomplete
        cohomology computation is continued.

        For `p>2`, any generator `x` of odd degree of the modular cohomology
        ring of a finite `p`-group gives rise to the relation `x^2=0`. We
        refer to such relation as *obvious*. In the current version of our
        package, we list only the non-obvious relations, but this might change
        in future versions.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,3, from_scratch=True)
            sage: H.make(2)
            sage: H.rels()
            ['a_1_0^2', 'a_1_0*b_1_1']
            sage: H.make()
            sage: H.rels()
            ['a_1_0^2', 'a_1_0*b_1_1', 'b_2_1*a_1_0', 'b_2_1^2+c_2_2*b_1_1^2']

        """
        return self.Rel

    def nrels(self):
        """
        Return the minimal number of relations of ``self``.

        NOTE:

        The list of relations may change if an incomplete
        cohomology computation is continued.

        For `p>2`, any generator `x` of odd degree of the modular cohomology
        ring of a finite `p`-group gives rise to the relation `x^2=0`. We
        refer to such relation as *obvious*. In the current version of our
        package, we count only the non-obvious relations, but this might change
        in future versions.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,3, from_scratch=True)
            sage: H.make(2)
            sage: H.nrels()
            2
            sage: H.make()
            sage: H.nrels()
            4
            sage: len(H.rels())
            4

        """
        return len(self.Rel)

    def relation_ideal(self):
        """
        Return the relation ideal for the current ring approximation.

        OUTPUT:

        An ideal in the Singular interface. It is a Groebner basis at least
        out to the known degree of the ring approximation.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(192,1493,prime=2, from_scratch=True)
            sage: H.make(4)
            sage: H.set_ring()
            sage: H.relation_ideal()
            b_1_0*b_3_0+b_2_1^2+b_2_0*b_2_2,
            b_1_0*b_3_2,
            b_1_0*b_3_5,
            b_1_0*b_3_6
            sage: H.make()
            sage: H.set_ring()
            sage: H.relation_ideal()
            b_1_0*b_3_0+b_2_1^2+b_2_0*b_2_2,
            b_1_0*b_3_2,
            b_1_0*b_3_5,
            b_1_0*b_3_6,
            b_2_0*b_3_6+b_2_0*b_3_5,
            b_2_1*b_3_2+b_2_0*b_3_5,
            b_2_1*b_3_5+b_2_0*b_3_5,
            b_2_1*b_3_6+b_2_0*b_3_5,
            b_2_2*b_3_2+b_2_0*b_3_5,
            b_2_2*b_3_5+b_2_0*b_3_5,
            b_3_0^2+b_2_1^2*b_2_2+b_2_1^3+b_2_0*b_2_1*b_2_2+b_2_0*b_2_1^2+c_4_10*b_1_0^2,
            b_3_0*b_3_2,
            b_3_0*b_3_5,
            b_3_0*b_3_6,
            b_3_2*b_3_6+b_3_2*b_3_5,
            b_3_5^2+b_3_2*b_3_5,
            b_3_5*b_3_6+b_3_2*b_3_5,
            b_2_1^2*b_3_0+b_2_1^2*b_2_2*b_1_0+b_2_1^3*b_1_0+b_2_0*b_2_2*b_3_0+b_2_0*b_2_1*b_2_2*b_1_0+b_2_0*b_2_1^2*b_1_0+c_4_10*b_1_0^3,
            b_2_1^2*b_2_2*b_1_0^2+b_2_1^3*b_1_0^2+b_2_1^4+b_2_0*b_2_1*b_2_2*b_1_0^2+b_2_0*b_2_1^2*b_1_0^2+b_2_0^2*b_2_2^2+c_4_10*b_1_0^4

        """
        try:
            br = singular('basering')
        except TypeError:
            br = None
        try:
            self.set_ring()
            I = singular(self.prefix+'I')
            if self.completed:
                singular.eval('attrib(%s,"isSB",1)'%I.name())
        finally:
            try:
                br.set_ring()
            except:
                pass
        return I

    def last_interesting_degree(self):
        """
        Presentation degree of the current ring approximation.

        OUTPUT:

        The highest degree of a generator or relation in the current
        ring approximation.

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace

        In our example, we compute the mod-2 cohomology of the
        Mathieu group `M_{11}`.
        ::

            sage: G = libgap.MathieuGroup(11)
            sage: H = CohomologyRing(G,prime=2,GroupName='M11', from_scratch=True)

        The smallest generator is in degree three, so, we have::

            sage: H.make(2)
            sage: H.last_interesting_degree()
            0

        The generator of highest degree is in degree 5, and there
        is no relation before degree 10. Hence, we obtain::

            sage: H.make(9)
            sage: H.last_interesting_degree()
            5

        We now finish the cohomology computation.
        ::

            sage: H.make()
            sage: H.last_interesting_degree()
            10
            sage: print(H)
            Cohomology ring of M11 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_4_0: 4-Cocycle in H^*(M11; GF(2)),
             b_3_0: 3-Cocycle in H^*(M11; GF(2)),
             b_5_0: 5-Cocycle in H^*(M11; GF(2))]
            Minimal list of algebraic relations:
            [b_5_0^2+c_4_0*b_3_0^2]

        """
        return max([self.lastRel or 0]+[t.deg() for t in self.Gen])

    @temporary_result
    def order_matrix(self):
        """
        Return an integer matrix that defines the term order of ``self``.

        Even if the order is `dp`, a matrix is returned.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(32,6, from_scratch=True)
            sage: H.make(2)
            sage: H.order_matrix()
            [ 2  2  2  1  1]
            [ 0  0  0 -1  0]
            [-1  0  0  0  0]
            [ 0 -1  0  0  0]
            [ 0  0 -1  0  0]
            sage: H.make()
            sage: H.order_matrix()
            [ 2  2  2  4  1  1  3  3]
            [ 0  0  0 -1  0  0  0  0]
            [ 0  0  0  0 -1  0  0  0]
            [-1  0  0  0  0  0  0  0]
            [ 0 -1  0  0  0  0  0  0]
            [ 0  0 -1  0  0  0  0  0]
            [ 0  0  0  0  0 -1  0  0]
            [ 0  0  0  0  0  0 -1  0]
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_workspace(tmp)
            sage: H = CohomologyRing(32,6, from_scratch=True)
            sage: H.setprop('use_dp',True)
            sage: H.make(2)
            sage: H.order_matrix()
            [ 2  2  2  1  1]
            [ 0  0  0  0 -1]
            [ 0  0  0 -1  0]
            [ 0  0 -1  0  0]
            [ 0 -1  0  0  0]
            sage: H.make()
            sage: H.order_matrix()
            [ 2  2  2  4  1  1  3  3]
            [ 0  0  0  0  0  0  0 -1]
            [ 0  0  0  0  0  0 -1  0]
            [ 0  0  0  0  0 -1  0  0]
            [ 0  0  0  0 -1  0  0  0]
            [ 0  0  0 -1  0  0  0  0]
            [ 0  0 -1  0  0  0  0  0]
            [ 0 -1  0  0  0  0  0  0]

        """
        if not self.use_dp:
            self._makeOrderMatrix_()
            return singular('%sM'%self.prefix).sage()
        from sage.all import Matrix,ZZ
        M = Matrix(ZZ,len(self.Gen))
        M[0] = self.degvec
        for i in range(1,len(self.Gen)):
            M[i,-i] = -1
        return M

    ########
    ## The essential ideal

    @permanent_result
    def essential_ideal(self,Subgroups=None):
        """
        Return the essential ideal, given by a Groebner basis.

        INPUT:

        ``Subgroups`` -- optional list or set of subgroups of ``self.group()``

        OUTPUT:

        The ideal of all elements of ``singular(self)`` that restrict
        to zero on all maximal subgroups of ``self.group()`` (resp.
        on the subgroups in the list ``Subgroups``). The generators
        of this ideal form a Groebner basis.

        If the optional argument is not provided, then the essential
        ideal with respect to all maximal subgroups is returned, and
        theoretical results are used that in some cases assert that
        there are no essential classes.

        THEORY:

        The essential ideal is formed by those elements
        of the cohomology ring whose restriction to any
        proper subgroup vanishes. We compute it by intersecting
        the kernels of the restriction maps to all maximal
        subgroups.

        It is known that the essential ideal can only
        be non-zero if the group is of prime power order
        and if the depth does not exceed the Duflot bound.

        EXAMPLES:

        We compute the cohomology rings for the dihedral group
        of order 8, the quaternion group of order 8, the
        semi-dihedral group of order 16, and some group which
        is not of prime power order::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: D = CohomologyRing(8,3, from_scratch=True)
            sage: D.make()
            sage: Q = CohomologyRing(8,4, from_scratch=True)
            sage: Q.make()
            sage: SD = CohomologyRing(16,8, from_scratch=True)
            sage: SD.make()
            sage: S6 = CohomologyRing(720,763,prime=2, from_scratch=True)
            sage: S6.make()

        The quaternion group is the smallest group that has
        a non-vanishing essential ideal::

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
                Compute depth
                Computation of depth interruptible with Ctrl-c
                Compute filter_regular_parameters
                Compute raw_filter_degree_type
                  Test filter regularity
                Filter degree type: [-1, -2, -2]
                The depth exceeds the Duflot bound -- there is no essential ideal
            0

        Of course, if one provides the set of maximal subgroups
        as optional parameter, then the result is the same, but
        it makes no use of the theoretical result::

            sage: D.essential_ideal(D.group().MaximalSubgroups())
                Compute essential_ideal
                > computing kernel of an induced map
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                lift in the source resolution
                lift in the target resolution to degree 1
                lift in the source resolution
                lift in the target resolution to degree 2
            H^*(SmallGroup(4,2); GF(2)):
                Compute order_matrix
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                Compute preimages by elimination
            H^*(D8; GF(2)):
                > intersecting two ideals
                > computing kernel of an induced map
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                lift in the source resolution
                lift in the target resolution to degree 1
                lift in the source resolution
                lift in the target resolution to degree 2
                Compute preimages by elimination
            H^*(D8; GF(2)):
                > intersecting two ideals
                > preparing output
            0
            sage: CohomologyRing.global_options('warn')
            sage: S6.essential_ideal(S6.group().MaximalSubgroups())
            0

        The depths of ``SD`` coincides with the Duflot bound. However,
        it has no essential classes::

            sage: SD.essential_ideal()
            0

        There are, of course, elements that are essential with respect
        to only a subset of all subgroups::

            sage: SD.essential_ideal([SD.group().Centre(),SD.group().CommutatorSubgroup(SD.group())])
            a_1_0,
            b_1_1,
            b_3_1

        We now consider a more difficult example: The Sylow 2-subgroup
        of `U_3(4)`, which is of order 64 and is thus contained in
        the local sources.
        ::

            sage: H = CohomologyRing(64,245)
            sage: H
            H^*(Syl2(U3(4)); GF(2))
            sage: I = H.essential_ideal()    #long time

        It turns out that there is exactly one essential class that decomposes
        into a product of other essential classes.  Note that this cohomology
        ring is one of only two known examples in which the square of the
        essential ideal does not vanish. In previous Sage versions, there has
        been a bug in Singular's ``interred`` command, so that a second
        element is printed that apparently is a multiple of the first. But now
        it is fine::

            sage: (I*I).NF('std(0)').interred()  #long time
            a_4_8*a_6_8*a_1_0^3*a_1_3
            sage: singular(H).set_ring()
            sage: singular('NF((a_4_8*a_6_8*a_1_0^3*a_1_3)^2, std(0))')
            0

        The second example was discovered using this package. It is the direct
        product of the cyclic group of order two and ``SmallGroup(64,245)``. Again,
        there is precisely one essential class that can be written as a product
        of other essential classes.

        """
        if not self.completed:
            raise RuntimeError("The ring structure may be incomplete")
        selfS = singular(self)
        selfS.set_ring()
        gap = self.group().parent()
        _gap_reset_random_seed()
        # prepare the key for caching:
        if Subgroups is not None:
            Subgroups = gap.Set(list(Subgroups))

        # We came to this point, so the result is not known
        # or Singular crashed. If we are lucky, the result
        # is cached as a string -- which can happen if we
        # have old pickles (created before having the decorator)
        if self._EssentialIdealStr is not None:
            key = repr(Subgroups)
            OutStr = self._EssentialIdealStr.get(key)
            if OutStr is not None:
                # OK, lucky, it was in some old cache.
                # But we now migrate to a different caching scheme.
                Out = singular.ideal(OutStr)
                del self._EssentialIdealStr[key]
                if not self._EssentialIdealStr:
                    self.delprop('_EssentialIdealStr')
                return Out

        if Subgroups is None: # try theoretical results
            if not Integer(self._Order or self.Resl.G_ALG().order()).is_prime_power():
                coho_logger.info("The group is not of prime power order -- there is no essential ideal",self)
                return singular.ideal(0)
            if self._lower_bound_depth()>self.CenterRk:
                coho_logger.info("The depth exceeds the Duflot bound -- there is no essential ideal",self)
                return singular.ideal(0)
        # Alas, this can be a long computation...
        if Subgroups is None:
            Mraw = [G for G in self.group().MaximalSubgroups()]
        else:
            Mraw = list(Subgroups)
        from pGroupCohomology import CohomologyRing
        dgb = singular.eval('degBound')
        singular.eval('degBound=0')
        Out = singular.ideal(1)
        option_bak = singular.option('get')
        singular.option('redSB')
        singular.option('returnSB')
        for i in range(len(Mraw)):
            if Out.size() == 0:
                break
            G = Mraw[i]
            try:
                GId = G.IdGroup()
                Gsm = gap.SmallGroup(GId)
                phiG = Gsm.IsomorphismGroups(G)
                G = gap.Group([phiG.Image(g) for g in Gsm.GeneratorsOfGroup()])
                GCo = CohomologyRing(*(GId.sage()), prime=self._prime)
                if G.canonicalIsomorphism(GCo.group()) == Failure:
                    phiG = GCo.group().IsomorphismGroups(G)
                    G = gap.Group([phiG.Image(g) for g in GCo.group().GeneratorsOfGroup()])
            except RuntimeError as msg:
                coho_logger.critical("WARNING: %s", self, msg)
                G = G.MinimalGeneratingSet().Group()
                GCo = CohomologyRing(G,prime=self._prime,GroupName = 'MaximalSubgroup(%s,%d)'%(self.GStem,i))
            GCo.make()
            phi = G.GroupHomomorphismByImages(self.group(),G.GeneratorsOfGroup(),G.GeneratorsOfGroup())
            phiCo = self.hom(phi,GCo)
            GS = singular(GCo)

            coho_logger.info('> computing kernel of an induced map',self)
            selfS.set_ring()
            K = phiCo.preimage()
            coho_logger.info('> intersecting two ideals',self)
            singular.eval('%s=intersect(%s,%s)'%(Out.name(),Out.name(),K.name()))
        # Unfortunately, Singular doesn't properly do tail reduction
        # in the quotient ring. So, once again we have to work around.
        self.set_ring()
        brself = singular('basering')
        coho_logger.info('> preparing output',self)
        Out2 = selfS.imap(Out).NF(self.relation_ideal()).interred()
        selfS.set_ring()
        Out = brself.imap(Out2)

        singular.eval('degBound='+dgb)
        singular.option('set',option_bak)
        return Out

    # The computations in GAP might be expensive, so, we do
    # caching in addition to what is done in essential_ideal
    @permanent_result
    def depth_essential_ideal(self, r):
        r"""
        Compute the `r`-th depth essential ideal.

        INPUT:

        ``r`` -- an integer, ``self.CenterRk \le r \le self.dimension()``.

        OUTPUT:

        The ideal formed by all elements of ``self`` that restrict to
        zero on the centralisers of all `p`-elementary abelian subgroups
        of rank ``r`` (it suffices to consider those that are contained
        in a Sylow `p`-subgroup `S` and contain the greatest central
        elementary abelian subgroup of `S`.

        THEORY:

        If ``r`` is at most the depth of ``self``, then the result is zero. It
        is conjectured by J. Carlson that it is non-zero whenever ``r``
        exceeds the depth.

        EXAMPLE:

        We choose a group of order 64 (that is contained in the local sources
        shipped with this package), and verify Carlson's conjecture::

            sage: from pGroupCohomology import CohomologyRing
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

        """
        G = self.group()
        Elabs = G.ElabsWithRank(self._prime or self.Resl.coef(),r)
#~         return self.essential_ideal(Elabs.List('g->Centralizer(%s,g)'%G.name()).Set())
        return self.essential_ideal(G.parent()([G.Centralizer(g) for g in Elabs]))

    def subgroups(self):
        """
        Return the subgroup dictionary of ``self``.

        OUTPUT:

        A dictionary of cohomology rings of elementary abelian groups
        that occur as maximal elementary abelian subgroups or as the
        greatest central elementary abelian subgroup of the group over
        which self is defined. The dictionary is indexed by addresses
        for the SmallGroups libarary.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,3)
            sage: sorted(H.subgroups().items())
            [((4, 2), H^*(SmallGroup(4,2); GF(2))), ((8, 5), H^*(SmallGroup(8,5); GF(2)))]

        """
        return self.subgps

    def restriction_maps(self):
        """
        Return the dictionary of restriction maps of ``self``.

        OUTPUT:

        A dictionary of induced homomorphisms, namely the restriction
        maps of self to conjugacy classes of maximal elementary abelian
        subgroups or to the greatest central elementary abelian subgroup.
        The greatest central elementary abelian subgroup is available
        with the index ``1``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,3)
            sage: sorted(H.restriction_maps().items())
            [(1,
              [(4, 2),
               Induced homomorphism of degree 0 from H^*(SmallGroup(16,3); GF(2)) to H^*(SmallGroup(4,2); GF(2))]),
             (2,
              [(8, 5),
               Induced homomorphism of degree 0 from H^*(SmallGroup(16,3); GF(2)) to H^*(SmallGroup(8,5); GF(2))])]

        """
        return self.RestrMaps

    def resolution(self):
        """
        Return the underlying resolution of ``self``.

        Of course, when computing the cohomology ring in increasing
        degree, more and more terms of the resolution will be computed.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(16,5, from_scratch=True)
            sage: H
            H^*(SmallGroup(16,5); GF(2))
            sage: print(H.resolution())
            Resolution:
            0 <- GF(2) <- GF(2)[SmallGroup(16,5)]
            sage: H.make()
            sage: print(H.resolution())
            Resolution:
            0 <- GF(2) <- GF(2)[SmallGroup(16,5)] <- rank 2 <- rank 3 <- rank 4

        """
        return self.Resl

##########################
###   HTML             ###
##########################
    def item2html(self,x):
        """
        Return a string that provides HTML code for the input.

        INPUT:

        Any object; but its intended use is for cohomology elements or
        for strings defining a polynomial.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.item2html(H.1)
            '<nobr>c_2_2</nobr>, a Duflot element of degree 2'
            sage: H.item2html(H.2*H.1^2)
            '<nobr>c_2_2<sup>2</sup>&middot;b_1_0</nobr>, an element of degree 5'
            sage: H.item2html(H.poincare_series())
            '<nobr>1/(t<sup>2 </sup>&thinsp;&#8722;&thinsp; 2&middot;t &thinsp;+&thinsp; 1)</nobr>'

        """
        cdef list L
        if isinstance(x,int) or isinstance(x,Integer):
            return str(x%self.Resl.coef())
        self.set_ring() # singular.eval("setring %sr(%d)"%(self.prefix,self.knownDeg))
        from pGroupCohomology.cochain import MODCOCH
        if isinstance(x,COCH) or isinstance(x,MODCOCH):
            if not (x.parent() is self):
                raise ValueError("The cocycle belongs to a different cohomology ring")
            L=[str2html(str(singular.eval(x.name())))]
            if x.rdeg():
                L.append(', a Duflot ')
            elif x.ydeg():
                L.append(', a nilpotent ')
            else:
                L.append(', an ')
            L.append('element of degree %d'%(x.deg()))
            return ''.join(L)
        if isinstance(x, (str, unicode)):
            return str2html(str(singular.eval(x)))
        return str2html(str(x))

    def htmlpage(self, user=None):
        """
        Create a html page describing ``self``

        OUTPUT:

        A html file describing the cohomology ring ``H`` is written
        to ``os.path.join(H.root,repr(H.group().Order()),'web',H.GStem+'.html')``

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: H.htmlpage()
            sage: import os
            sage: print(open(os.path.join(H.root,'%dweb'%H.group().Order(),H.GStem+'.html')).read())
            <html>
            <head>
            <title>Cohomology of Group number 3 of Order 8
            </title>
                <!--#config timefmt="%d.%m.%Y" -->
            </head>
            <body>
            <BLANKLINE>
              <a name = "general"></a><h2>
              Cohomology of group number 3 of order 8
            </h2>
            <p>
            <table border="1">
              <tr>
                <td><a href="#general">About the group</a></td>
                <td><a href="#generators">Ring generators</a></td>
                <td><a href="#relations">Ring relations</a></td>
                <td><a href="#completion">Completion information</a></td>
                <td><a href="#restrict">Restriction maps</a></td>
              </tr>
            </table>
            <BLANKLINE>
            <p><hr></p>
            <h3>
              General information on the group
            </h3>
            <p><ul>
              <li> The group is also known as D8, the Dihedral group of order 8.
              </li>
              <li>The group has 2 minimal generators and exponent 4.
              </li>
              <li> It is non-abelian.
              </li>
              <li> It has p-Rank 2.
              </li>
              <li> Its centre has rank 1.
              </li>
              <li> It has 2 conjugacy classes of maximal elementary abelian subgroups, which are all of rank 2.
              </li>
            </ul></p>
            <p><hr></p>
            <h3>
              Structure of the cohomology ring
            </h3>
            <h4>
              General information
            </h4>
            <p><ul>
              <li> The cohomology ring is of dimension 2 and depth 2.
              </li>
              <li> The depth exceeds the Duflot bound, which is 1.
              </li>
              <li> The Poincar&eacute; series is    <table style="color:black"><tr><td align="center"><nobr>1</nobr></td></tr>      <tr><td><hr style="color:black"></td></tr><tr><td align="center"><nobr>(&thinsp;&#8722;&thinsp;1 &thinsp;+&thinsp; t)<sup>2</sup></nobr></td></tr>
                </table>
              </li>  <li> The a-invariants are -&infin;,-&infin;,-2.  They were obtained using the filter regular HSOP of the <a href="#completion">Symonds test</a>.
              </li>
              <li> The filter degree type of any filter regular HSOP is [-1, -2, -2].
              </li>
            </ul></p>
            <BLANKLINE>
            <BLANKLINE>
              <a name = "generators"></a>
              <p>
            <table border="1">
              <tr>
                <td><a href="#general">About the group</a></td>
                <td><a href="#generators">Ring generators</a></td>
                <td><a href="#relations">Ring relations</a></td>
                <td><a href="#completion">Completion information</a></td>
                <td><a href="#restrict">Restriction maps</a></td>
              </tr>
            </table></p>
            <BLANKLINE>
            <h4>
              Ring generators
            </h4>
             <p>The cohomology ring has 3 minimal generators of maximal degree 2:
            </p>
            <ol>
              <li> <nobr>b_1_1</nobr>, an element of degree 1
              </li>
              <li> <nobr>b_1_0</nobr>, an element of degree 1
              </li>
              <li> <nobr>c_2_2</nobr>, a Duflot element of degree 2
              </li>
            </ol>
            <BLANKLINE>
            <a name = "relations"></a>
              <p>
            <table border="1">
              <tr>
                <td><a href="#general">About the group</a></td>
                <td><a href="#generators">Ring generators</a></td>
                <td><a href="#relations">Ring relations</a></td>
                <td><a href="#completion">Completion information</a></td>
                <td><a href="#restrict">Restriction maps</a></td>
              </tr>
            </table></p>
            <BLANKLINE>
            <h4>
              Ring relations
            </h4>
            <p>There is one minimal relation of degree 2:
            <ol>
              <li> <nobr>b_1_0&middot;b_1_1</nobr>
              </li>
            </ol></p>
            <BLANKLINE>
            <a name = "completion"><p><hr></p></a>
              <p>
            <table border="1">
              <tr>
                <td><a href="#general">About the group</a></td>
                <td><a href="#generators">Ring generators</a></td>
                <td><a href="#relations">Ring relations</a></td>
                <td><a href="#completion">Completion information</a></td>
                <td><a href="#restrict">Restriction maps</a></td>
              </tr>
            </table></p>
            <BLANKLINE>
            <h3>
              Data used for the Symonds test
            </h3>
            <p>
              <ul>
                <li> We proved completion in degree 2 using the Symonds criterion.
                </li>
                <li> The completion test was perfect: It applied in the last degree in which a generator or relation was found.
                </li>
                <li> The following is a filter regular homogeneous system of parameters:
                <ol>
                  <li><nobr>c_2_2</nobr>, an element of degree 2
                  </li>
                  <li><nobr>b_1_1&thinsp;+&thinsp;b_1_0</nobr>, an element of degree 1
                  </li>
                </ol>
                </li>    <li> A Duflot regular sequence is given by <nobr>c_2_2</nobr>.
                </li>
                <li> The Raw Filter Degree Type of the filter regular HSOP is [-1, -1, 1].
                </li>
                <li> We used the following parameters for the Symonds criterion:
                </li>
                <ol>
                  <li><nobr>b_1_0</nobr>, an element of degree 1
                  </li>
                  <li><nobr>b_1_1</nobr>, an element of degree 1
                  </li>
                  <li><nobr>c_2_2</nobr>, an element of degree 2
                  </li>
                </ol>
                </li>    <li> As a module over these parameters, the cohomology is generated in degree at most 0.
                </li>
              </ul></p>
            <p><a name="restrict"><hr></a></p>
            <p>
            <table border="1">
              <tr>
                <td><a href="#general">About the group</a></td>
                <td><a href="#generators">Ring generators</a></td>
                <td><a href="#relations">Ring relations</a></td>
                <td><a href="#completion">Completion information</a></td>
                <td><a href="#restrict">Restriction maps</a></td>
              </tr>
            </table></p>
            <BLANKLINE>
            <h3>
              Restriction maps
            </h3>
              <h4>
                Restriction map to the greatest central el. ab. subgp., which is of rank 1
              </h4>
                <ol>
                  <li> <nobr>b_1_1</nobr> &rarr; <nobr>0</nobr>, an element of degree 1
                  </li>
                  <li> <nobr>b_1_0</nobr> &rarr; <nobr>0</nobr>, an element of degree 1
                  </li>
                  <li> <nobr>c_2_2</nobr> &rarr; <nobr>c_1_0<sup>2</sup></nobr>, an element of degree 2
                  </li>
                </ol>
            <BLANKLINE>
              <h4>
                Restriction map to a maximal el. ab. subgp. of rank 2
              </h4>
                <ol>
                  <li> <nobr>b_1_1</nobr> &rarr; <nobr>c_1_1</nobr>, an element of degree 1
                  </li>
                  <li> <nobr>b_1_0</nobr> &rarr; <nobr>0</nobr>, an element of degree 1
                  </li>
                  <li> <nobr>c_2_2</nobr> &rarr; <nobr>c_1_0&middot;c_1_1&thinsp;+&thinsp;c_1_0<sup>2</sup></nobr>, an element of degree 2
                  </li>
                </ol>
            <BLANKLINE>
              <h4>
                Restriction map to a maximal el. ab. subgp. of rank 2
              </h4>
                <ol>
                  <li> <nobr>b_1_1</nobr> &rarr; <nobr>0</nobr>, an element of degree 1
                  </li>
                  <li> <nobr>b_1_0</nobr> &rarr; <nobr>c_1_1</nobr>, an element of degree 1
                  </li>
                  <li> <nobr>c_2_2</nobr> &rarr; <nobr>c_1_0&middot;c_1_1&thinsp;+&thinsp;c_1_0<sup>2</sup></nobr>, an element of degree 2
                  </li>
                </ol>
            <BLANKLINE>
            <p><hr></p>
            <p>
            <table border="1">
              <tr>
                <td><a href="#general">About the group</a></td>
                <td><a href="#generators">Ring generators</a></td>
                <td><a href="#relations">Ring relations</a></td>
                <td><a href="#completion">Completion information</a></td>
                <td><a href="#restrict">Restriction maps</a></td>
              </tr>
            </table></p>
            <BLANKLINE>
            <BLANKLINE>
                          <br clear="all">
                          <P>
                          <HR WIDTH="100%">
                          <HR WIDTH="100%"></P>
                          Created with the <a href="http://www.sagemath.org/" style="font-variant:small-caps">Sage</a>
                          <a href="https://users.fmi.uni-jena.de/cohomology/documentation/">cohomology package</a>
                          written by <a href="https://users.fmi.uni-jena.de/~king/">Simon King</a>
                          and <a href="https://users.fmi.uni-jena.de/~green/">David Green</a>
                          <P>
                          <HR WIDTH="100%">
                          <HR WIDTH="100%"></P>
                  <p>
                  <i>Last change: <!--#echo var="LAST_MODIFIED" --></i>
                  <hr>
            <BLANKLINE>
                    </BODY>
                    </HTML>
            <BLANKLINE>

        """
        if self.CenterRk is None: # i.e., it is an abelian p-group
            if self.knownDeg>1:
                self.completed=True
        cdef int p = self.Resl.coef()
        self.reconstructSubgroups()
        from sage.all import Integer
        q = Integer(self._Order or self.Resl.G_ALG().order())
        if len(self._key[0])==2:
            n=self._key[0][1]
        else:
            n=None
        root = self.root or self.workspace

        quaternion_case = q.is_prime_power() and self.pRank==1
        abelian_case = self.group_is_abelian()
        from pGroupCohomology.modular_cohomology import MODCOHO
        if self._method:
            _method = self._method
        else:
            if isinstance(self,MODCOHO):
                if len(self._PtoPcapCPdirect):
                    _method = 'Benson' # will never occur...
                else:
                    _method = self._HP._method or 'Benson'
            else:
                _method = self._method or 'Benson'


        #############
        ## Create web folder, if it doesn't exist yet
        try:
            os.mkdir(os.path.join(root,'%dweb'%(q)))
        except OSError:
            pass
        if isinstance(self, MODCOHO):
            L = open(os.path.join(root,'%dweb'%q,'%smod%d.html'%(self.GStem,self._prime)),'w')
        else:
            L = open(os.path.join(root,'%dweb'%q,'%s.html'%(self.GStem)),'w')
        L.write('<html>\n<head>\n')
        if n:
            L.write('<title>%sCohomology of Group number %d of Order %d\n</title>\n'%('' if q.is_prime_power() else 'Mod-%d-'%self._prime, n,q))
        else:
            if self.GroupName:
                L.write('<title>%sCohomology of %s (Group of Order %d)\n</title>\n'%('' if q.is_prime_power() else 'Mod-%d-'%self._prime, self.GroupName,q))
            else:
                L.write('<title>Cohomology of %s (Group of Order %d)\n</title>\n'%(self.GStem,q))
        if user=="SimonKing":
            L.write('   <link rel="shortcut icon" type="image/x-icon" href="/~king/favicon.ico" />\n')
            L.write('\n    <link rel="stylesheet" href="/~king/design.css" type="text/css">\n')
        L.write(r'    <!--#config timefmt="%d.%m.%Y" -->')
        L.write('\n</head>\n')
        if user=="SimonKing":
            ## General layout
            L.write('<body>\n  <table CELLPADDING="10" CELLSPACING="0" BORDER="0" HEIGHT="100%" WIDTH="100%">\n')
            L.write('''<TR>
    <td valign="top" id="navi">
      <!--#include virtual="/~king/navigation.txt" -->
    </td>

    <TD VALIGN="top" WIDTH="100%" id="main">

      <P>
        <HR WIDTH="100%">
        <HR WIDTH="100%">
      </P>\n''')
        else:
            L.write('<body>\n')

    ###################
    ### The Main Data:
        L.write('\n  <a name = "general"></a>')
        if self.completed:
            L.write('<h2>\n  %sCohomology of '%('' if q.is_prime_power() else 'Mod-%d-'%self._prime))
        else:
            L.write('<h2>\n  %sCohomology approximation of '%('' if q.is_prime_power() else 'Mod-%d-'%self._prime) )
        if n:
            L.write('group number %d of order %d\n</h2>\n'%(n,q))
        else:
            if self.GroupName:
                L.write('%s, a group of order %d\n</h2>\n'%(self.GroupName,q))
            else:
                L.write('%s, a group of order %d\n</h2>\n'%(self.GStem,q))
        if not self.completed:
            L.write('<h3>\n  Based on a computation out to degree %d\n</h3>\n'%(self.knownDeg))
        #########
        ## General information on the group
        L.write('<p>\n<table border="1">\n  <tr>\n')
        L.write('    <td><a href="#general">About the group</a></td>\n')
        L.write('    <td><a href="#generators">Ring generators</a></td>\n')
        L.write('    <td><a href="#relations">Ring relations</a></td>\n')
        if not (abelian_case or quaternion_case):
            L.write('    <td><a href="#completion">Completion information</a></td>\n')
        if (self.CenterRk is not None):
            L.write('    <td><a href="#restrict">Restriction maps</a></td>\n')
        #if user == "SimonKing":
        #    L.write('    <td><a href="index.html">Back to groups of order %d</a></td>\n'%(q))
        L.write('  </tr>\n</table>\n\n')

        L.write('<p><hr></p>\n<h3>\n  General information on the group\n</h3>\n<p><ul>\n')
        if n: # another group name / description might be available
            if ((None!=self.GroupName!='SmallGroup(%d,%d)'%(q,n)) or self.GroupDescr):
                L.write('  <li> The group is ')
                if self.GroupName and (self.GroupName!='SmallGroup(%d,%d)'%(q,n)):
                    if n:
                        L.write('also ')
                    L.write('known as '+str(self.GroupName))
                    if self.GroupDescr and (self.GroupDescr!=self.GroupName):
                        L.write(', ')
                if self.GroupDescr:
                    L.write('the '+str(self.GroupDescr)+'.\n  </li>\n')
                else:
                    L.write('.\n  </li>\n')
        else: # group should have a group name:
            if self.GroupName:
                L.write('  <li>%s'%self.GroupName)
                if self.GroupDescr:
                    L.write(', the %s,'%self.GroupDescr)
            elif self.GroupDescr:
                L.write('The %s'%self.GroupDescr)
            L.write(' is a group of order %d.\n  </li>\n'%q)
        if not q.is_prime_power():
            from sage.all import factor
            L.write('  <li>The group order factors as %s.\n  </li>'%str2html(repr(factor(q))))
        if n is None:
            L.write('  <li>The group is defined by %s.\n  </li>\n'%(self._key[0][0]))
        if q.is_prime_power():
            L.write('  <li>The group has {} minimal generators and exponent {}.\n  </li>\n'.format(self.group().RankPGroup(), self.group().Exponent()))
            if abelian_case:
                L.write('  <li> It is abelian, isomorphic to')
                L.write('&times;'.join('C<sub>%d</sub>'%dd for dd in self.group().AbelianInvariants()))
                L.write('.\n  </li>\n')
            else:
                if quaternion_case:
                    L.write('  <li> It is a (generalized) quaternion group, hence, is of p-Rank 1.\n  </li>\n')
                else:
                    L.write('  <li> It is non-abelian.\n  </li>\n')
                    L.write('  <li> It has p-Rank %d.\n  </li>\n'%(self.pRank))
                    if self.CenterRk: # it is a non-abelian p-group
                        L.write('  <li> Its centre has rank %d.\n  </li>\n'%(self.CenterRk))
                if len(self.MaxelRk)==1:
                    L.write('  <li> It has a unique conjugacy class of maximal elementary abelian subgroups, which is of rank %d.\n  </li>\n'%(self.MaxelRk[0]))
                else:
                    L.write('  <li> It has %d conjugacy class%s of maximal elementary abelian subgroups, which are '%(len(self.MaxelRk),'' if len(self.MaxelRk)==1 else 'es'))
                    if len(set(self.MaxelRk))==1:
                        L.write('all of rank %d.\n  </li>\n'%(self.MaxelRk[0]))
                    else:
                        L.write('of rank %s and %d, respectively.\n  </li>\n'%(str(self.MaxelRk[:-1])[1:-1],self.MaxelRk[-1]))
        else: # it is a non-prime-power group
            if abelian_case:
                L.write('  <li> It is abelian, isomorphic to')
                L.write('&times;'.join('C<sub>%d</sub>'%dd for dd in self.group().AbelianInvariants()))
                L.write('.\n  </li>\n')
            else:
                L.write('  <li> It is non-abelian.\n  </li>\n')
                L.write('  <li> It has %d-Rank %d.\n  </li>\n'%(self._prime,self.pRank))
                L.write('  <li> The centre of a Sylow %d-subgroup has rank %d.\n  </li>\n'%(self._prime,self.PCenterRk or self.pRank))
            if len(self.MaxelRk)==1:
                L.write('  <li> Its Sylow %d-subgroup has a unique conjugacy class of maximal elementary abelian subgroups, which is of rank %d.\n  </li>\n'%(self._prime,self.MaxelRk[0]))
            else:
                L.write('  <li> Its Sylow %d-subgroup has %d conjugacy class%s of maximal elementary abelian subgroups, which are '%(self._prime, len(self.MaxelRk),'' if len(self.MaxelRk)==1 else 'es'))
                if len(set(self.MaxelRk))==1:
                    L.write('all of rank %d.\n  </li>\n'%(self.MaxelRk[0]))
                else:
                    L.write('of rank %s and %d, respectively.\n  </li>\n'%(str(self.MaxelRk[:-1])[1:-1],self.MaxelRk[-1]))
        L.write('</ul></p>\n')

        #########
        ## Cohomology ring structure
        if self.completed:
            L.write('<p><hr></p>\n<h3>\n  Structure of the cohomology ring\n</h3>\n')
        else:
            L.write('<p><hr></p>\n<h3>\n  Appoximate structure of the cohomology ring\n</h3>\n')
        if not q.is_prime_power():
            if len(self._PtoPcapCPdirectSing):
                if self._HP is self._HSyl:
                    L.write('The computation was based on %d stability condition%s for <a href="https://users.fmi.uni-jena.de/cohomology/%dweb/%s.html">%s</a>.\n'%(len(self._PtoPcapCPdirectSing),('' if len(self._PtoPcapCPdirectSing)==1 else 's'), self._HSyl.Resl.G_ALG().order(),self._HSyl.GStem,self._HP._html_()))
                else:
                    L.write('The computation was based on %d stability condition%s for <a href="%smod%d.html">%s</a>.\n'%(len(self._PtoPcapCPdirectSing),('' if len(self._PtoPcapCPdirectSing)==1 else 's'), self._HP.GStem,self._prime,self._HP._html_()))
            else:
                if self._HP is self._HSyl:
                    L.write('This cohomology ring is isomorphic to the cohomology ring of a subgroup, namely <a href="https://users.fmi.uni-jena.de/cohomology/%dweb/%s.html">%s</a>.\n'%(self._HSyl.Resl.G_ALG().order(),self._HSyl.GStem,self._HP._html_()))
                else:
                    L.write('This cohomology ring is isomorphic to the cohomology ring of a subgroup, namely <a href="%smod%d.html">%s</a>.\n'%(self._HP.GStem,self._prime,self._HP._html_()))
        if self.completed:
            L.write('<h4>\n  General information\n</h4>\n')
            L.write('<p><ul>\n')
            if self.pRank:
                try:
                    depth = self.depth()
                except KeyboardInterrupt:
                    depth = [self._lower_bound_depth(), self.dimension()]
                if isinstance(depth,list):
                    L.write('  <li> We were not able to compute the depth. The depth is between %d and %d.\n  </li>\n'%(depth[0], depth[1]))
                    L.write('  <li> The cohomology ring is of dimension %d.\n  </li>\n'%(self.dimension()))
                else:
                    L.write('  <li> The cohomology ring is of dimension %d and depth %d.\n  </li>\n'%(self.dimension(),depth))
                    if (depth==self.CenterRk) or (self.CenterRk==0 and depth==(self.PCenterRk or self.pRank)):
                        L.write('  <li> The depth coincides with the Duflot bound.\n  </li>\n')
                    else:
                        L.write('  <li> The depth exceeds the Duflot bound, which is %d.\n  </li>\n'%(self.CenterRk or self.PCenterRk or self.pRank))
            else:
                MinimalGenerators = self.group().RankPGroup().sage()
                L.write('  <li> The cohomology ring is of dimension %d and depth %d.\n  </li>\n'%(MinimalGenerators,MinimalGenerators))
            PS = self.poincare_series()
            P1,P2 = PS.numerator(),PS.denominator()
            from sage.all import PowerSeriesRing, QQ
            PowSR = PowerSeriesRing(QQ,'t')
            L.write('  <li> The Poincar&eacute; series is')
            F1 = P1.factor()
            if F1.unit()==1:
                L.write('    <table style="color:black"><tr><td align="center">%s</td></tr>'%(str2html(str(F1.__class__([(PowSR(a),b) for a,b in F1])),linelength=0)))
            else:
                L.write('    <table style="color:black"><tr><td align="center">%s</td></tr>'%(str2html(('(%d)&middot;('%F1.unit())+str(F1.__class__([(PowSR(a),b) for a,b in F1]))+')',linelength=0)))
            F2 = P2.factor()
            if F2.unit()==1:
                L.write('      <tr><td><hr style="color:black"></td></tr><tr><td align="center">%s</td></tr>\n    </table>\n  </li>'%(str2html(str(F2.__class__([(PowSR(a),b) for a,b in F2])),linelength=0)))
            else:
                L.write('      <tr><td><hr style="color:black"></td></tr><tr><td align="center">%s</td></tr>\n    </table>\n  </li>'%(str2html(('(%d)&middot;('%F2.unit())+str(F2.__class__([(PowSR(a),b) for a,b in F2]))+')',linelength=0)))
            A_INV = self.a_invariants()
            if A_INV is None:
                L.write('  <li> We were unable to compute the a-invariants.\n  </li>\n')
            else:
                L.write('  <li> The a-invariants are %s. '%(','.join([str(X) for X in A_INV]).replace('Infinity','&infin;')))
                if self.CenterRk is not None:
                    if self.A_INV_Expos.count(1)==len(self.A_INV_Expos):
                        L.write(' They were obtained using the filter regular HSOP of the <a href="#completion">%s test</a>.'%(_method))
                    else:
                        XList = [' They were obtained using ']
                        for X in range(len(self.A_INV_Expos)):
                            if X == len(self.A_INV_Expos)-1:
                                XList.append('and ')
                            if self.A_INV_Expos[X]==1:
                                XList.append('the '+Integer(X+1).ordinal_str())
                            elif self.A_INV_Expos[X]==2:
                                XList.append('the second power of the '+Integer(X+1).ordinal_str())
                            elif self.A_INV_Expos[X]==3:
                                XList.append('the third power of the '+Integer(X+1).ordinal_str())
                            else:
                                XList.append('the {} power of the '.format(self.A_INV_Expos[X])+Integer(X+1).ordinal_str())
                            if X < len(self.A_INV_Expos)-1:
                                XList.append(', ')
                            else:
                                XList.append(' filter regular parameter of the <a href="#completion">%s test</a>.'%(_method))
                        L.write(''.join(XList))
            FDT = self.filter_degree_type()
            if FDT is None:
                L.write('\n  </li>\n  <li> We were unable to compute the filter degree type.')
            else:
                L.write('\n  </li>\n  <li> The filter degree type of any filter regular HSOP is %s.'%(str(FDT)))
            L.write('\n  </li>\n</ul></p>\n\n')
        #########
        ## Generators
        L.write('\n  <a name = "generators"></a>')
        L.write('\n  <p>\n<table border="1">\n  <tr>\n')
        L.write('    <td><a href="#general">About the group</a></td>\n')
        L.write('    <td><a href="#generators">Ring generators</a></td>\n')
        L.write('    <td><a href="#relations">Ring relations</a></td>\n')
        if not (abelian_case or quaternion_case):#(self.CenterRk is not None) and (self.pRank!=1):
            L.write('    <td><a href="#completion">Completion information</a></td>\n')
        if (self.CenterRk is not None):
            L.write('    <td><a href="#restrict">Restriction maps</a></td>\n')
#        if user == "SimonKing":
#            L.write('    <td><a href="index.html">Back to groups of order %d</a></td>\n'%(q))
        L.write('  </tr>\n</table></p>\n\n')
        L.write('<h4>\n  Ring generators\n</h4>\n')
        if self.completed or self.all_generators_found:
            L.write(' <p>The cohomology ring has %d minimal generators of maximal degree %d:\n</p>\n'%(len(self.Gen),max(self.degvec)))
        else:
            if (len(self.duflot_regular_sequence())<(self.CenterRk or (self.CenterRk==0 and self.PCenterRk))):
                L.write('  <p> There will be more Duflot generators.\n<br>    Out to degree %d, the cohomology ring has %d minimal generators of maximal degree %d:\n  </p>\n'%(self.knownDeg,len(self.Gen),max(self.degvec)))
            else:
                L.write(' <p>Out to degree %d, the cohomology ring has %d minimal generators of maximal degree %d:\n</p>\n'%(self.knownDeg,len(self.Gen),max(self.degvec)))
        L.write('<ol>\n')
        GenL = copy(self.Gen)
        GenL.sort()
        if self.CenterRk is not None: # i.e., the group is not and abelian p-group
            for X in GenL:
                L.write('  <li> '+self.item2html(X)+'\n  </li>\n')
        else:
            for X in GenL:
                L.write('  <li> '+self.item2html(X.name())+', an element of degree %d\n  </li>\n'%(X.deg()))
        L.write('</ol>\n\n')
        if not self.completed:
            if self.all_generators_found:
                L.write('<p> We can show that there will be no further generators.\n</p>\n')
            elif self.degbound_for_gens:
                L.write('<p> We can show that there will be no further generators above degree.\n</p>\n'%self.degbound_for_gens)

        #########
        ## Relations
        L.write('<a name = "relations"></a>')
        L.write('\n  <p>\n<table border="1">\n  <tr>\n')
        L.write('    <td><a href="#general">About the group</a></td>\n')
        L.write('    <td><a href="#generators">Ring generators</a></td>\n')
        L.write('    <td><a href="#relations">Ring relations</a></td>\n')
        if not (abelian_case or quaternion_case):#(self.CenterRk is not None) and (self.pRank!=1):
            L.write('    <td><a href="#completion">Completion information</a></td>\n')
        if self.CenterRk is not None:
            L.write('    <td><a href="#restrict">Restriction maps</a></td>\n')
#        if user == "SimonKing":
#            L.write('    <td><a href="index.html">Back to groups of order %d</a></td>\n'%(q))
        L.write('  </tr>\n</table></p>\n\n')
        if self.completed:
            L.write('<h4>\n  Ring relations\n</h4>\n')
        else:
            L.write('<h4>\n  Ring relations out to degree %d\n</h4>\n'%(self.knownDeg))
        cdef int i
        cdef int lenGen = len(self.Gen)
        if (p%2) and (self.firstOdd<lenGen):
            if lenGen-self.firstOdd == 1:
                L.write('<p> There is one "obvious" relation:<br>\n  &nbsp;&nbsp;&nbsp;')
            else:
                L.write('<p> There are %d "obvious" relations:<br>\n  &nbsp;&nbsp;&nbsp;'%(lenGen-self.firstOdd))
            for i from self.firstOdd <= i < lenGen-1:
                L.write(self.item2html(self.Gen[i].name())+'<sup>2</sup>, ')
            L.write(self.item2html(self.Gen[-1].name())+'<sup>2</sup>\n</p>\n<p>Apart from that, t')
        else:
            L.write('<p>T')
        if len(self.Rel):
            if len(self.Rel)==1:
                L.write('here is one minimal relation of degree %d:\n<ol>\n'%(self.lastRel))
            else:
                L.write('here are %d minimal relations of maximal degree %d:\n<ol>\n'%(len(self.Rel),self.lastRel))
            for X in self.Rel:
                L.write('  <li> '+self.item2html(X)+'\n  </li>\n')
            L.write('</ol></p>\n\n')
        else:
            L.write('here are no relations.\n</p>\n')
        if not self.completed:
            if (self.expect_last_relation()>self.knownDeg):
                if (q%2):
                    L.write('  <p>\n  Note that we expect further "non-obvious" relations at least out to degree %d\n  </p>\n'%(self.expect_last_relation()))
                else:
                    L.write('  <p>\n  Note that we expect further relations at least out to degree %d\n  </p>\n'%(self.expect_last_relation()))
            else:
                L.write('  <p>\n  It seems possible that there will be no further relations\n  </p>\n')
        ##########
        ## Completion information
        if not (abelian_case or quaternion_case):#(self.CenterRk is not None) and (self.pRank!=1):
            L.write('<a name = "completion"><p><hr></p></a>\n')
            L.write('  <p>\n<table border="1">\n  <tr>\n')
            L.write('    <td><a href="#general">About the group</a></td>\n')
            L.write('    <td><a href="#generators">Ring generators</a></td>\n')
            L.write('    <td><a href="#relations">Ring relations</a></td>\n')
            L.write('    <td><a href="#completion">Completion information</a></td>\n')
            L.write('    <td><a href="#restrict">Restriction maps</a></td>\n')
#            if user == "SimonKing":
#                L.write('    <td><a href="index.html">Back to groups of order %d</a></td>\n'%(q))
            L.write('  </tr>\n</table></p>\n\n')
            if self.completed:
                L.write('<h3>\n  Data used for the %s test\n</h3>\n<p>\n  <ul>\n'%(_method))
            else:
                L.write('<h3>\n  Parameters\n</h3>\n<p>\n  <ul>\n')
            if self.completed:
                L.write('    <li> We proved completion in degree %d using the %s criterion.\n    </li>\n'%(max(self.suffDeg,self.lastRel,max(self.degvec)),_method))
            else:
                L.write('    <li> The computation is incomplete, none of our completeness criteria applied up to degree %d.\n    </li>\n'%(self.knownDeg))
            if self.completed:
                if (self.suffDeg <= self.lastRel) or (self.suffDeg <= max(self.degvec)):
                    L.write('    <li> The completion test was perfect: It applied in the last degree in which a generator or relation was found.\n    </li>\n')
                else:
                    L.write('    <li> However, the last relation was already found in degree %d and the last generator in degree %d.\n    </li>\n'%(self.lastRel,max(self.degvec)))
                L.write('    <li> The following is a filter regular homogeneous system of parameters:\n    <ol>\n')
                for X in self.filter_regular_parameters():
                    if X!=None:
                        L.write('      <li>'+self.item2html(X)+', an element of degree %d\n      </li>\n'%(Integer(singular.eval('deg('+X+')'))))
                L.write('    </ol>\n    </li>')
            else:
                if (self.Dickson.count(None)):
                    L.write('    <li> We need to lift more Dickson invariants.\n    </li>\n')
                if (len(self.duflot_regular_sequence())<(self.CenterRk or (self.CenterRk==0 and self.PCenterRk))):
                    L.write('    <li> We need to find more Duflot generators.\n    </li>\n')
            if (len(self.duflot_regular_sequence())<(self.CenterRk or (self.CenterRk==0 and self.PCenterRk))):
                L.write('    <li> There is a Duflot regular sequence starting with %s.\n    </li>\n'%(', '.join([self.item2html(tmp) for tmp in self.duflot_regular_sequence()])))
            else:
                if self.duflot_regular_sequence()!=self.filter_regular_parameters():
                    L.write('    <li> A Duflot regular sequence is given by %s.\n    </li>\n'%(', '.join([self.item2html(tmp) for tmp in self.duflot_regular_sequence()])))
                else:
                    L.write('    <li> The above filter regular HSOP forms a Duflot regular sequence.\n    </li>\n')
            if self.completed:
                rfdt,HV,DV = (self._decorator_cache or {}).get(('raw_filter_degree_type',tuple(self.filter_regular_parameters())),[[None,None,None],0])[0]
                if rfdt:
                    L.write('    <li> The Raw Filter Degree Type of the filter regular HSOP is %s.\n    </li>\n'%(str(rfdt)))
                if self.WhatFRS:
                    if isinstance(self.WhatFRS[0],list):
                        if self.WhatFRS[0]!=self.Dickson:
                            if len(self.WhatFRS[0])==1:
                                L.write('    <li> We found that there exists some filter regular HSOP over a finite extension field, formed by %s, together with %d element%s of degree %d.\n    </li>\n'%(self.item2html(self.WhatFRS[0][0]),self.pRank-len(self.WhatFRS[0]),"s" if self.pRank-len(self.WhatFRS[0])!=1 else "", self.WhatFRS[1]))
                            else:
                                L.write('    <li> We found that there exists some filter regular HSOP over a finite extension field, formed by %s, and %s, together with %d elements of degree %d.\n    </li>\n'%(', '.join([self.item2html(tmp) for tmp in self.WhatFRS[0][:-1]]), self.item2html(self.WhatFRS[0][-1]),self.pRank-len(self.WhatFRS[0]),self.WhatFRS[1]))
                    else:
                        if self.pRank-self.WhatFRS[0] == 1:
                            L.write('    <li> We found that there exists some filter regular HSOP over a finite extension field, formed by the first term of the above HSOP, together with %d elements of degree %d.\n    </li>\n'%(self.WhatFRS[0],self.WhatFRS[1]))
                        else:
                            L.write('    <li> We found that there exists some filter regular HSOP over a finite extension field, formed by the first %d terms of the above HSOP, together with %d elements of degree %d.\n    </li>\n'%(self.pRank-self.WhatFRS[0],self.WhatFRS[0],self.WhatFRS[1]))
                if _method=='Symonds' or _method=='Hilbert-Poincar&eacute;':
                    Pars = self._parameters_for_criterion or self.parameters()
                    if Pars!=self.filter_regular_parameters():
                        L.write('    <li> We used the following parameters for the %s criterion:\n    </li>\n    <ol>\n'%_method)
                        for X in Pars:
                            if X!=None:
                                L.write('      <li>'+self.item2html(X)+', an element of degree %d\n      </li>\n'%(Integer(singular.eval('deg('+X+')'))))
                        L.write('    </ol>\n    </li>')
                    if _method=='Symonds':
                        if self._max_module_deg is not None:
                            L.write('    <li> As a module over these parameters, the cohomology is generated in degree at most %d.\n    </li>\n'%self._max_module_deg)
                        else:
                            L.write('    <li> As a module over these parameters, the cohomology is generated in degree at most %d.\n    </li>\n'%self._HP._max_module_deg)
                    else:
                        if self.WhatHSOP:
                            L.write('    <li> We found that there exists some HSOP over a finite extension field, in degrees %s.\n    </li>\n'%(','.join(self.WhatHSOP)))
            L.write('  </ul></p>\n')
            ##############
            ## Restriction Maps
        if self.CenterRk is not None:
            L.write('<p><a name="restrict"><hr></a></p>\n<p>\n<table border="1">\n  <tr>\n')
            L.write('    <td><a href="#general">About the group</a></td>\n')
            L.write('    <td><a href="#generators">Ring generators</a></td>\n')
            L.write('    <td><a href="#relations">Ring relations</a></td>\n')
            if not (abelian_case or quaternion_case):#(self.CenterRk is not None) and (self.pRank!=1):
                L.write('    <td><a href="#completion">Completion information</a></td>\n')
            L.write('    <td><a href="#restrict">Restriction maps</a></td>\n')
#            if user == "SimonKing":
#                L.write('    <td><a href="index.html">Back to groups of order %d</a></td>\n'%(q))
            L.write('  </tr>\n</table></p>\n\n')
            L.write('<h3>\n  Restriction maps\n</h3>\n')
            if self._HP:
                if self._HP is self._HSyl:
                    L.write('  <h4>\n    Expressing the generators as elements of <a href="https://users.fmi.uni-jena.de/cohomology/%dweb/%s.html">%s</a>  </h4>\n'%(self._HSyl.Resl.G_ALG().order(),self._HSyl.GStem,self._HSyl._html_()))
                else:
                    L.write('  <h4>\n    Expressing the generators as elements of <a href="%smod%d.html">%s</a>  </h4>\n'%(self._HP.GStem,self._prime,self._HP._html_()))
                L.write('    <ol>\n')
                PairL = [[X,X.val_str()] for X in self.Gen]
                PairL.sort()
                for X in PairL:
                    L.write('      <li> '+self.item2html(X[0].name())+' &rarr; ')
                    L.write(self._HP.item2html(X[1]))
                    L.write('\n      </li>\n')
                L.write('    </ol>\n\n')
            for i from 1 <= i <= len(self.RestrMaps):
                if i==1:
                    if self.CenterRk!=0:
                        L.write('  <h4>\n    Restriction map to the greatest central el. ab. subgp., which is of rank %d\n  </h4>\n'%(self.CenterRk or self.PCenterRk or self.pRank))
                    else:
                        L.write('  <h4>\n    Restriction map to the greatest el. ab. subgp. in the centre of a Sylow subgroup, which is of rank %d\n  </h4>\n'%(self.CenterRk or self.PCenterRk or self.pRank))
                else:
                    if self.CenterRk!=0:
                        L.write('  <h4>\n    Restriction map to a maximal el. ab. subgp. of rank %d\n  </h4>\n'%(self.MaxelRk[i-2]))
                    else:
                        L.write('  <h4>\n    Restriction map to a maximal el. ab. subgp. of rank %d in a Sylow subgroup\n  </h4>\n'%(self.MaxelRk[i-2]))
                RestL = self.restrict_to_subgroup(i)
                PairL = [[self.Gen[j],RestL[j]] for j in xrange(len(self.Gen))]
                PairL.sort()
                L.write('    <ol>\n')
                for X in PairL:
                    L.write('      <li> '+self.item2html(X[0].name())+' &rarr; ')
                    L.write(self.subgps[self.RestrMaps[i][0]].item2html(X[1]))
                    L.write('\n      </li>\n')
                L.write('    </ol>\n\n')
        ###########
        ## "Signature" of this package
        L.write('<p><hr></p>\n<p>\n<table border="1">\n  <tr>\n')
        L.write('    <td><a href="#general">About the group</a></td>\n')
        L.write('    <td><a href="#generators">Ring generators</a></td>\n')
        L.write('    <td><a href="#relations">Ring relations</a></td>\n')
        if not (abelian_case or quaternion_case):#(self.CenterRk is not None) and (self.pRank!=1):
            L.write('    <td><a href="#completion">Completion information</a></td>\n')
        if self.CenterRk is not None:
            L.write('    <td><a href="#restrict">Restriction maps</a></td>\n')
#        if user == "SimonKing":
#            L.write('    <td><a href="index.html">Back to groups of order %d</a></td>\n'%(q))
        L.write('  </tr>\n</table></p>\n\n')
        if user=="SimonKing":
            L.write(r'''
              <br clear="all">

              <!--#include virtual="/~king/address.txt" -->
              <P>
              <HR WIDTH="100%">
              <HR WIDTH="100%"></P>
              </TD>
            </TR>
          </TABLE>

      <p>
      <i>Last change: <!--#echo var="LAST_MODIFIED" --></i>
      <hr>

        </BODY>
        </HTML>
        ''')
        else:
            L.write(r'''
              <br clear="all">
              <P>
              <HR WIDTH="100%">
              <HR WIDTH="100%"></P>
              Created with the <a href="http://www.sagemath.org/" style="font-variant:small-caps">Sage</a>
              <a href="https://users.fmi.uni-jena.de/cohomology/documentation/">cohomology package</a>
              written by <a href="https://users.fmi.uni-jena.de/~king/">Simon King</a>
              and <a href="https://users.fmi.uni-jena.de/~green/">David Green</a>
              <P>
              <HR WIDTH="100%">
              <HR WIDTH="100%"></P>
      <p>
      <i>Last change: <!--#echo var="LAST_MODIFIED" --></i>
      <hr>

        </BODY>
        </HTML>
        ''')
        L.close()
        if self._HP is not self._HSyl:
            self._HP.htmlpage(user=user)

###################
## Auxiliary methods
    ####################
    ## What groebner basis command to use?
    def _gb_command(self):
        r"""
        Return the name of the command that is to be used
        for Gröbner basis computations in this cohomology ring.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,1)
            sage: H._gb_command()
            'groebner'
            sage: CohomologyRing.doctest_setup()       # create a new workspace, so that we create a new cohomology ring
            sage: H = CohomologyRing(8,2, useSlimgb=True, from_scrach=True)
            sage: H._gb_command()
            'slimgb'

        """
        if self.useSlimgb:
            return "slimgb"
        elif self.useStd:
            return "std"
        else:
            return "groebner"

    ####################
    ## Transform Singular-Monomials into products of cochains
    ## Use result of sub-monomials that are stored in self.Monomials
    def MonToProd(self, expV):
        """
        Return the element corresponding to a list of exponents.

        INPUT:

        ``expV``: a list of non-negative integers (exponents of a list of monomials)

        OUTPUT:

        An element of ``self`` (:class:`~pGroupCohomology.cochain.COCH`), given by
        a power product of generators.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make()
            sage: H.MonToProd([0,2,1])
            (b_1_0)*((b_1_0)*(b_1_1)): 3-Cocycle in H^*(D8; GF(2))

        """
        # Assume: All lifts have been performed before
        cdef int lenoldV = len(expV)
        cdef int i, s_o, s_e, sml
        newKey = ''.join([expV[i]*(self.Gen[i].name()) for i in range(lenoldV)])
        if newKey in self.Monomials:
            return self.Monomials[newKey]
        cdef list oldV = list(tuple(expV))# copy the list
        # find the factor of smallest even/odd degree
        for i from 0 <= i < self.firstOdd:
            if oldV[i]:
                break
        if (i<lenoldV) and oldV[i]:
            s_e=i
        else:
            s_e=-1

        for i from self.firstOdd <= i < lenoldV:
            if oldV[i]:
                break
        if (i<lenoldV) and oldV[i]:
            s_o=i
        else:
            s_o=-1

        # Which one has lower degree?
        if s_o==-1:
            sml = s_e
        elif s_e==-1:
            sml = s_o
        else:
            if self.degvec[s_o]<self.degvec[s_e]:
                sml = s_o
            else:
                sml = s_e

        # Compute the product Gen[sml]*(the rest)
        oldV[sml]-=1
        cdef COCH Coch
        cdef RESL R
        R=self.Resl
        if max(oldV)==0: # the monomial is a single variable
            return self.Gen[sml]
        Coch = self.Gen[sml]*self.MonToProd(oldV)
        self.Monomials[newKey] = Coch
        self.Resl.setLift(Coch, Coch.deg()+self.degvec[sml])
        return Coch

    #####################
    ## Compute the standard monomials in degree n and store them in Singular under
    ## the name s
    ## WARNING: There might be miscomputations if the ring order is changed so that
    ##          some of the variable x is of degree zero, and x>1
    def _makeStdMon(self,n,s):
        """
        Compute the standard monomials in a given degree.

        INPUT:

        - ``n`` (integer): The degree of the requested standard monomials
        - ``s`` (string): Name of an ideal in the Singular interface into which the monomials are stored

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make(2)
            sage: H._makeStdMon(3,'M')
            sage: singular('M')
            b_1_0^3,
            b_1_1^3,
            c_2_2*b_1_0,
            c_2_2*b_1_1

        """
        if not (isinstance(n, int) or isinstance(n,Integer)):
            raise TypeError("degree (first argument) must be an integer")
        if not (isinstance(s, (str, unicode))):
            raise TypeError("second argument must be a string")
        s = str(s)
        coho_logger.info( "Determine degree %d standard monomials",self, n)
        try:
            self.StdMon[0]['1']._check_valid()
        except ValueError:
            self.reconstruct_singular()
        if singular.eval('defined(%s)'%s)=='1':
            singular.eval('kill %s'%s)
        if not self.Gen:
            singular.eval('ideal %s'%(s))
            return
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self.set_ring()
        if n==0:
            singular.eval('ideal %s'%(s))
            self.StdMon[n] = {'1':singular.ideal(1)}
            if br is not None:
                br.set_ring()
            return
        cdef list Degrees = [X.deg() for X in self.Gen]
        for i in range(n):
            if n-i in Degrees:
                if not i in self.StdMon:
                    self._makeStdMon(i,s)
        # In order to make addition of ideals more efficient,
        # estimate the length of StdMon
        MaxLength = max(sum([[Integer(singular.eval('ncols(%s)'%(X.name()))) for X in self.StdMon[i].values()] for i in xrange(1,n) if n-i in Degrees], [1]))
        self.StdMon[n]={}
        singular.eval('ideal '+s)
        singular.eval('%s[%d] = 0'%(s,MaxLength*len(self.Gen)))
        sCount=0
        singular.eval('ideal LeadGB = lead(%sI)'%(self.prefix))
        cdef list Vars = list(singular.maxideal(1).sort()[1])
        for x in Vars:
            if int(singular.eval('deg(%s)'%x.name()))>n:
                continue
            self.StdMon[n][str(x)]=singular.ideal(0)
            singular.eval('%s[%d]=0'%(self.StdMon[n][str(x)].name(),MaxLength*len(self.Gen)))
            MonCount = 0
            for I in self.StdMon[Integer(n-int(singular.eval('deg(%s)'%x.name())))].items():
                if singular.eval(I[0]+'<=%s'%(x._name))=='1':
                    if singular.eval('typeof(%s)'%(I[1].name()))=='int':
                        tmp = 0
                    else:
                        tmp = Integer(I[1].ncols())
                    if tmp > 1:
                        # working around a bug in non-commutative Singular (Normalize is defined in dickson.lib)
                        singular.eval('%s[%d..%d] = Normalize(ideal(%s*%s),LeadGB)'%(self.StdMon[n][str(x)].name(),MonCount+1,MonCount+tmp,I[1].name(),str(x)))
                    elif tmp == 1:
                        singular.eval('%s[%d] = normalize(NF(%s[1]*%s,LeadGB))'%(self.StdMon[n][str(x)].name(),MonCount+1,I[1].name(),str(x)))
                    else:
                        tmp = 1
                        singular.eval('%s[%d] = normalize(NF(%s*%s,LeadGB))'%(self.StdMon[n][str(x)].name(),MonCount+1,I[1].name(),str(x)))
                    MonCount=MonCount+tmp
            tmp = Integer(self.StdMon[n][str(x)].ncols())
            singular.eval('%s[%d..%d] = %s[1..%d]'%(s,sCount+1,sCount+tmp,self.StdMon[n][str(x)].name(),tmp))
            sCount = sCount + tmp
        ## cleanup
        for I in list(self.StdMon[n].items()):
            singular.eval('%s = simplify(%s,6)'%(I[1].name(),I[1].name()))
            if I[1].size()==0:
                del self.StdMon[n][I[0]]
        singular.eval('%s = simplify(%s,6)'%(s,s))
        singular.eval('kill LeadGB')
        if br is not None:
            br.set_ring()

    #####################
    ## Source of vector space bases for H^n
    def standardCochain(self, n, i, rdeg=None,ydeg=None,name='c'):
        """
        Standard cochain of ``self``.

        INPUT:

        - ``n``: degree (integer) of a cochain
        - ``i``: integer
        - ``rdeg``, ``ydeg``: (optional) integers or ``None`` (default ``None``).
        - ``name``: (optional) string used to give the cochain a name (default ``'c'``)

        OUTPUT:

        A `n`-cochain represented by ``[0,...,0,1,0,...0]`` with 1 at position `i`
        (counting from zero) and name ``'c_%d_%d'%(n,i)``. The letter ``'c'`` in
        the name can be changed with the optional parameter 'name'.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: c=H.standardCochain(3,2,rdeg=1,ydeg=0,name='X')
            sage: c
            X_3_2: 3-Cocycle in H^*(D8; GF(2))
            sage: print(c)
            3-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 0 1 0]
            rdeg = 1
            ydeg = 0

        """
        if not ((isinstance(n, int) or isinstance(n,Integer)) and\
                (isinstance(i, int) or isinstance(i,Integer))):
            raise TypeError("integers expected")
        if (n<0) or (n>self.Resl.deg()):
            raise IndexError("resolution only known up to degree {}".format(self.Resl.deg()))
        if (i<0) or (i>self.Resl.rank(n)):
            raise IndexError("The {} term of the resolution is of rank {}".format(Integer(n).ordinal_str(), self.Resl.rank(n)))
        return COCH(self, n, name+'_%d_%d'%(n,i), i*[0]+[1]+(self.Resl.rank(n)-i-1)*[0], rdeg=rdeg, ydeg=ydeg)

    #####################
    ## Return list of standard monomials in a given degree,
    ## as a list of strings
    ## we could use @permanent_result, but for sake of memory
    ## usage, it seems better to do a separate way of caching.
    def standard_monomials(self, n):
        """
        Standard monomials of a prescribed degree.

        INPUT:

        `n`: An integer, so that ``self`` is known at least out
        to degree `n`.

        OUTPUT:

        A list of strings, providing the degree-`n` standard monomials,
        sorted in descending order.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,4, from_scratch=True)
            sage: H.make(2)
            sage: H.standard_monomials(2)
            ['a_1_0*a_1_1', 'a_1_0^2']
            sage: H.standard_monomials(3)
            Traceback (most recent call last):
            ...
            ValueError: The cohomology ring is not known out to degree 3
            sage: H.make()

        We now know the cohomology ring entirely, although the explicit
        computation only went out to degree 4. But since we know all
        of the ring, we can now get the degree-`5` standard monomials::

            sage: H.knownDeg
            4
            sage: H.standard_monomials(5)
            ['c_4_0*a_1_1', 'c_4_0*a_1_0']

        """
        if n==0:
            return ['1']
        if (n>self.knownDeg) and not self.completed:
            raise ValueError("The cohomology ring is not known out to degree %d"%n)
        if not self.Gen:
            return []
        self.set_ring()
        self._makeStdMon(n,"%sMon"%self.prefix)
        cdef list Monomials = [t.strip() for t in singular.eval("print(sort(%sMon)[1])"%self.prefix).split(',')]
        if Monomials == ['0']:
            Monomials = []
        singular.eval('kill %sMon'%self.prefix)
        # Protect against spoiled data
        from pGroupCohomology.modular_cohomology import MODCOHO
        if not isinstance(self,MODCOHO):
            if not Monomials:
                self.StdMon = {0:{'1':singular('1')}}
                self._makeStdMon(n,"%sMon"%self.prefix)
                Monomials = [t.strip() for t in singular.eval("print(sort(%sMon)[1])"%self.prefix).split(',')]
                if Monomials == ['0']:
                    Monomials = []
                if not Monomials:
                    raise RuntimeError("The cohomology of a prime power group must have standard monomials in degree %d, but there were none found"%n)
        Monomials.reverse()
        return Monomials

    #####################
    ## Express a cochain (type COCH) as polynomial in the cohomology ring generators
    def element_as_polynomial(self, c):
        """
        Express a cochain as polynomial in the generators of ``self``.

        INPUT:

        ``C``: an element of self

        OUTPUT:

        ``C`` is changed in-place and then returned, so that its
        name represents ``C`` as a polynomial in the ring generators.

        NOTE:

        If needed, all decomposable classes in the degree of ``C``
        will be computed and then kept in memory. The decomposable
        classes need to be obtained anyway when computing the ring
        structure. By default, for saving resources, the memory is
        cleared (except for elementary abelian groups). If the
        optional parameter ``KeepBases`` is ``True``  when
        creating the cohomology ring, the memory is not cleared.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: c=H.standardCochain(3,3)
            sage: c
            c_3_3: 3-Cocycle in H^*(D8; GF(2))
            sage: c is H.element_as_polynomial(c)
            True
            sage: c
            c_2_2*b_1_1: 3-Cocycle in H^*(D8; GF(2))
            sage: H('c_2_2*b_1_1')==c
            True

        """
        from pGroupCohomology.cochain import MODCOCH
        if isinstance(c,MODCOCH):
            if c.parent() is not self:
                raise ValueError("The given cochain does not belong to "+repr(self))
            ## the group is a p-group, hence, c._Svalue belongs to singular(self)
            c._NF_()
            c.setname(c.val_str(), is_polyrep=True)
            return c
        FfSetField(self.base_ring().order())
        cdef COCH C = self(c)
        n = C.deg()
        if n==0:
            return C
        coho_logger.debug("Express cochain of degree %d as polynomial", self, n)
        try:
            br = singular('basering')
        except TypeError:
            br = None
        cdef list DecGen = self.decomposable_classes(n) # triangular basis of the sub space of decomposables of H^n
        cdef list VSGen=self.Resl.rank(n)*[1]
        cdef list pivot=[]
        cdef COCH Cand # will be the 'next candidate' for a decomposable generator in Triang, if it needs to be constructed
        cdef RESL R
        R=self.Resl
        cdef int j,k
        cdef FEL f, f2
        cdef MTX DecGenM
        cdef int lenDecGen=len(DecGen)
        for k from 0 <= k < lenDecGen:
            DecGenM = DecGen[k].MTX()
            FfSetNoc(DecGenM.Data.Noc)
            j = FfFindPivot(DecGenM.Data.Data, &f)
            if j>=0:
                pivot.append(j)
            else:
                raise ArithmeticError("One of the basis elements is zero")
        Cand = -C          # Cand is the negative of C...
        Cand.setname('0')  # ... and has the name '0'. We will subtract decomposable generators until
                           # the value of Cand is zero -- and then, its name is a polynomial expression
                           # for C and will be assigned to C's name.
        FfSetField(Cand.Data.Data.Field)
        FfSetNoc(Cand.Data.Data.Noc)
        j = FfFindPivot(Cand.Data.Data.Data, &f)
        if j>=0:
            Cand.set_mtx_globals()
            for k from 0 <= k < lenDecGen:
                if (j <= pivot[k]):
                    f2 = FfExtract(Cand.Data.Data.Data, pivot[k])
                    if f2!=FF_ZERO:
                        Cand.isubmul(DecGen[k], f2)
                        j = FfFindPivot(Cand.Data.Data.Data, &f)
                        if j<0:
                            break
        if j>=0:
            raise ArithmeticError("The set of generators of %s in degree %d is incomplete"%(repr(self), n))
        try:
            self.set_ring()
            C.setname(singular.eval(Cand.name()), is_polyrep=True)
            return C
        finally:
            try:
                br.set_ring()
            except:
                pass

    ##################
    ## Manage restrictions
    def InsertSubgroup(self, q,nr, n):
        """
        Initialize the restriction map to some subgroup.

        INPUT:

        - ``q`` - the order of the subgroup
        - ``nr`` - the position of this group in the Small Group Library
        - ``n`` - the subgroup is addressed as subgroup number ``n``

        NOTE:

        * This method will normally be of internal use only. It is invoked by
          the method :meth:`InitSubgroups`
        * It reads the data for the inclusion map from a file whose name is
          determined by ``self.GStem`` and ``n``. The necessary files are
          created by :func:`~pGroupCohomology.resolution.makeGroupData` or
          or :func:`~pGroupCohomology.resolution.makeSpecialGroupData` during
          iniitialisation of the cohomology ring.
        * Normally, we only consider elementary abelian subgroups. This
          method probably also allows for insertion of other interesting
          subgroups, provided a file with data for the inclusion map exists.
          However, **PLEASE DO NOT INSERT SUBGROUPS MANUALLY!**
          The computations crucially depend on the restrictions to certain
          elementary abelian subgroups, and it is essential that *only*
          elementary abelian abelian subgroups are inserted, including the
          greatest central elementary abelian (this *must* be subgroup number
          one) and one representative for each conjugacy class of maximal
          elementary abelian subgroups.
        * The method will try to read a file in a specific location (see
          example below). This file should provide a MeatAxe matrix that
          describes the inclusion map of the algebra of the subgroup into
          the algebra of the ambient group.
        * When a cohomology ring is initialized, the greatest central
          elementary abelian subgroup will be inserted as special subgroup
          number 1. Moreover, representatives for the conjugacy classes
          of maximal elementary subgroups will be inserted.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: sorted(H.subgroups().items())
            [((2, 1), H^*(SmallGroup(2,1); GF(2))), ((4, 2), H^*(SmallGroup(4,2); GF(2)))]
            sage: sorted(H.restriction_maps().items())
            [(1,
              [(2, 1),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(2,1); GF(2))]),
             (2,
              [(4, 2),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))]),
             (3,
              [(4, 2),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))])]

        Hence, there are 3 special subgroups, that are of two different
        isomorphism types. We now destroy them on purpose::

            sage: H.RestrMaps={}
            sage: H.subgps={}

        Next, we put them back manually. Note that it is attempted
        to reload the subgroups from cache or from disk::

            sage: H.InsertSubgroup(2,1,1)
            sage: H.InsertSubgroup(4,2,2)

        The third subgroup has the same automorphism type as the second, so,
        there is no need to reload it, but it doesn't hurt either::

            sage: H.InsertSubgroup(4,2,3)
            sage: sorted(H.subgroups().items())
            [((2, 1), H^*(SmallGroup(2,1); GF(2))), ((4, 2), H^*(SmallGroup(4,2); GF(2)))]
            sage: sorted(H.restriction_maps().items())
            [(1,
              [(2, 1),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(2,1); GF(2))]),
             (2,
              [(4, 2),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))]),
             (3,
              [(4, 2),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))])]

        Next, we show where to find the files defining the inclusion
        of the second and third subgroup. Although they are isomorphic,
        the inclusions are, of course, different::

            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: print(MTX.from_filename(os.path.join(H.inc_folder,H.GStem+'sg2.ima')))
            [1 0 0 0 0 0 0 0]
            [0 0 0 1 1 1 1 1]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 1 1]
            sage: print(MTX.from_filename(os.path.join(H.inc_folder,H.GStem+'sg3.ima')))
            [1 0 0 0 0 0 0 0]
            [0 0 0 1 1 1 1 1]
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 1 0 1]

        Finally, we demonstrate how to continue the computation.
        After re-inserting the special subgroups, it is necessary
        to re-compute the Dickson classes in the special subgroups
        (using the method dickson_in_subgroup), or to use the
        elimination method. We chose the second way::

            sage: H.setprop('useElimination',True)
            sage: CohomologyRing.global_options('warn')
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

        """
        from pGroupCohomology import CohomologyRing
        if not ((isinstance(q,int) or isinstance(q,Integer)) and (isinstance(nr,int) or isinstance(nr,Integer)) and (isinstance(n,int) or isinstance(n,Integer))):
            raise TypeError("Subgroup and imbedding have to be defined by three integers")
        if (q,nr) in self.subgps: # that isomorphism type is known
            M = MTX.from_filename(os.path.join(self.inc_folder,self.GStem+'sg'+str(n)+'.ima'))
            ch = self.hom(M, self.subgps[(q,nr)])
        else:
            saveopts = dict(coho_options)
            coho_logger.info("Inserting SmallGroup(%d,%d) as a subgroup", self, q,nr)
            # we take the group from the workspace, since there might
            # be problems with write permission, and not from any remote source, since
            # that really doesn't make much sense for abelian groups
            h = CohomologyRing(q,nr, Subgroups= False, websource = False)
            h.make()
            coho_options.clear()
            coho_options.update(saveopts)
            M = MTX.from_filename(os.path.join(self.inc_folder,self.GStem+'sg'+str(n)+'.ima'))
            ch = self.hom(M,h)
            CurrDeg = self.Resl.deg()
            while h.knownDeg < CurrDeg:
                h.next(Forced=True,KeepDecomposables=True)
            self.subgps[(q,nr)] = h
        # in either case, the new restriction map must be stored.
        self.RestrMaps[n] = [(q,nr),ch]

    def InitSubgroups(self):
        """
        Initialise maximal elementary abelian subgroups.

        If self is the cohomology ring of a non-abelian `p`-group
        then ``InitSubgroups`` initialises various group theoretic
        data, such as the `p`-rank or the rank of the center; it
        also creates or reloads the cohomology rings of the greatest
        central and the maximal elementary abelian subgroups, and,
        if applicable, computes the Dickson classes of the maximal
        elementary abelian subgroups.

        NOTE:

        This function should only be of internal use and will be
        invoked when initializing a cohomology ring. It requires
        the presence of a certain GAP-readable file that is
        created during initialisation of the cohomology ring.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)

        Now we destroy and reconstruct the subgroups and the respective
        restriction maps::

            sage: H.subgps={}
            sage: H.RestrMaps={}
            sage: H.InitSubgroups()
            sage: sorted(H.subgroups().items())
            [((2, 1), H^*(SmallGroup(2,1); GF(2))), ((4, 2), H^*(SmallGroup(4,2); GF(2)))]
            sage: sorted(H.restriction_maps().items())
            [(1,
              [(2, 1),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(2,1); GF(2))]),
             (2,
              [(4, 2),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))]),
             (3,
              [(4, 2),
               Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2))])]
            sage: H.subgpDickson
            {(4, 2): [c_1_1: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))]}

        Finally, we show location and content of the GAP-readable
        file that defines the subgroup structure::

            sage: print(open(os.path.join(H.inc_folder,H.GStem+'.sgs')).read())
            # Subgroup information for 8gp3
            local numSpecialSubgps, specialSubgpId, CrankPos, numMaxels,
              maxelRankPos, numBoltons, Bolton;
            numSpecialSubgps := 3;
            specialSubgpId := [ [ 2, 1 ], [ 4, 2 ], [ 4, 2 ] ];
            CrankPos := [ 1, 1 ];
            numMaxels := 2;
            maxelRankPos := [ [ 2, 2 ], [ 2, 3 ] ];
            numBoltons := 0;
            Bolton := [];
            return [numSpecialSubgps, specialSubgpId, CrankPos,
              numMaxels, maxelRankPos, numBoltons, Bolton];

        """
        coho_logger.info("Initialising maximal p-elementary abelian subgroups",self)
        ## Get information from the gap-readable sgs-file
        from pGroupCohomology.auxiliaries import gap
        try:
            f = gap.ReadAsFunction(os.path.join(self.inc_folder,self.GStem+'.sgs'))
            if f == Failure:
                return
            L = f()
        except TypeError:  # can't be loaded
            return
        cdef int i
        NumSubgps = L[0].sage()
        self.CElPos = L[2][1].sage()
        self.CenterRk = L[2][0].sage()
        self.MaxelPos = [x[1].sage() for x in L[4]]
        self.MaxelRk  = [x[0].sage() for x in L[4]]
        self.pRank = max(self.MaxelRk)
        self.Dickson = (self.pRank-self.CenterRk)*[None]
        cdef int p = self.Resl.coef()
        ## insert the special subgroups
#~         for i in xrange(1,NumSubgps+1):
#~             self.InsertSubgroup(Integer(L[2][i][1]),Integer(L[2][i][2]),i)
        for i,x in enumerate(L[1]):
            self.InsertSubgroup(x[0].sage(), x[1].sage(), i+1)
        if self.useElimination is None: # determine it by a heuristic
            if Integer(p)**(self.pRank-self.CenterRk)*(1+ (p%2)) > 18:
                coho_logger.info("The degree of Dickson invariants is too high.",self)
                coho_logger.info("We will use elimination to find Dickson invariants",self)
                self.setprop('useElimination',True)
            else:
                self.setprop('useElimination',False)
        self.subgpDickson = {}
        for Id,G in self.subgps.items():
            while G.knownDeg < 2:
                G.next(Forced=True,KeepDecomposables=True)
            if not self.useElimination:
                self.dickson_in_subgroup(Id)

    def restrict_to_subgroup (self, n):
        """
        Returns the restriction of the cohomology ring generators to the `n`-th subgroup.

        SEE ALSO:

        - :meth:`restrictions_as_string`

        INPUT:

        - ``n``: an integer indicating a special subgroup

          * ``n=1`` refers to the greatest central elementary abelian subgroup
          * ``n>1`` refers to a representative of conjugacy classes of maximal
            elementary abelian subgroups

        OUTPUT:

        A list of cochains of the specified subgroup, obtained by restricting
        the generators of self

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()

        H has two isomorphism types of special subgroups, but
        3 conjugacy classes::

            sage: len(H.subgroups())
            2
            sage: len(H.restriction_maps())
            3

        We show the restriction to the three conjugacy classes.
        First, the greatest central elementary abelian subgroup::

            sage: H.restrict_to_subgroup(1)
            [c_1_0^2: 2-Cocycle in H^*(SmallGroup(2,1); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(2,1); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(2,1); GF(2))]

        Now the restrictions to the maximal elementary abelian
        subgroups::

            sage: H.restrict_to_subgroup(2)
            [c_1_0*c_1_1+c_1_0^2: 2-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))]
            sage: H.restrict_to_subgroup(3)
            [c_1_0*c_1_1+c_1_0^2: 2-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             0: 1-Cocycle in H^*(SmallGroup(4,2); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(4,2); GF(2))]

        """
        h = self.subgps[self.RestrMaps[n][0]]
        ch = self.RestrMaps[n][1]
        return [h.element_as_polynomial(ch*G) for G in self.Gen]

    def restrictions_as_string (self,n):
        """
        Restriction of the cohomology ring generators to the `n`-th subgroup as list of strings.

        SEE ALSO:

        - :meth:`restrict_to_subgroup`

        INPUT:

        - ``n``: an integer indicating a special subgroup

          * ``n=1`` refers to the greatest central elementary abelian subgroup
          * ``n>1`` refers to a representative of conjugacy classes of maximal
            elementary abelian subgroups

        OUTPUT:

        A list of strings, representing a polynomial in the generators of the
        cohomology of the specified subgroup, yielding the restriction
        of the generators of self to that subgroup

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()

        ``H`` has two isomorphism types of special subgroups, but 3
        conjugacy classes::

            sage: len(H.subgroups())
            2
            sage: len(H.restriction_maps())
            3

        We show the restriction to the three conjugacy classes.
        First, the greatest central elementary abelian subgroup::

            sage: H.restrictions_as_string(1)
            ['c_1_0^2', '0', '0']

        Now the restrictions to the maximal elementary abelian subgroups::

            sage: H.restrictions_as_string(2)
            ['c_1_0*c_1_1+c_1_0^2', 'c_1_1', '0']
            sage: H.restrictions_as_string(3)
            ['c_1_0*c_1_1+c_1_0^2', '0', 'c_1_1']

        """
        #cdef COCH X
        L = self._property_dict.get('Restriction_%d'%(n),None)
        if (L is None) or (len(L)<len(self.Gen)):
            L = [X.name() for X in self.restrict_to_subgroup(n)]
            self._property_dict['Restriction_%d'%(n)] = L
        return L

    @temporary_result
    def nil_preimage(self,n):
        """
        Preimage of the nil-radical of the `n`-th special subgroup.

        INPUT:

        - ``n``: an integer indicating a special subgroup

          * ``n=1`` refers to the greatest central elementary abelian subgroup
          * ``n>1`` refers to a representative of conjugacy classes of maximal
            elementary abelian subgroups

        OUTPUT:

        An ideal in the Singular interface. It corresponds to the
        preimage of the nil radical of the cohomology of the `n`-th
        special subgroup.

        EXAMPLES:

        We need to choose a `p`-group with `p>2`, since we would
        like to have an example where the cohomology of elementary
        abelian groups has non-trivial nil radical.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: H.nil_preimage(2)
            a_1_0,
            a_1_1,
            b_2_0,
            b_2_1,
            b_2_2,
            a_3_4,
            a_3_5
            sage: _.parent()
            Singular
            sage: H.nil_preimage(3)
            a_1_0,
            a_1_1,
            b_2_1,
            b_2_2,
            b_2_3,
            a_3_4,
            a_3_5
            sage: H.nil_preimage(4)
            a_1_0,
            a_1_1,
            b_2_1-b_2_0,
            b_2_2,
            b_2_3-b_2_0,
            a_3_4,
            a_3_5
            sage: H.nil_preimage(5)
            a_1_0,
            a_1_1,
            b_2_1+b_2_0,
            b_2_2+b_2_0,
            b_2_3+b_2_0,
            a_3_4,
            a_3_5

        A cohomology class is nilpotent if and only if its
        restriction to all maximal elementary abelian subgroups
        is nilpotent. Hence, the nil radical of ``H`` is the
        intersection of the above ideals, namely::

            sage: H.nil_preimage(2).intersect(H.nil_preimage(3)).intersect(H.nil_preimage(4)).intersect(H.nil_preimage(5)).groebner()
            a_1_0,
            a_1_1,
            a_3_4,
            a_3_5

        """
        cdef RESL Resl = self.Resl
        coho_logger.info("Lift nil radical of the %s special subgroup", self, Integer(n).ordinal_str())
        G = self.subgps[self.RestrMaps[n][0]]
        r = self.RestrMaps[n][1]
        N = [t.name() for t in G.Gen if t.ydeg()]
        if not N:
            singular(self).set_ring()
            return r.preimage()
        singular(G).set_ring()
        NI = singular.ideal(N)
        singular(self).set_ring()
        return r.preimage(Id=NI)

    @permanent_result
    def nil_radical(self):
        """
        Compute the nil radical of ``self``.

        OUTPUT:

        An ideal (Groebner basis) defined in the singular interface,
        representing the ideal of nilpotent elements of self.

        THEORY:

        An element of a cohomology ring is nilpotent if and only if
        its restriction to all maximal elementary abelian subgroups
        is nilpotent. Hence, we compute the intersection
        of the preimages of the nil radicals of the cohomology rings
        of the maximal elementary abelian subgroups. The ideal
        belongs to ``singular(self)``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: N = H.nil_radical()
            sage: singular(H).set_ring()
            sage: N
            a_1_0,
            a_1_1,
            a_3_4,
            a_3_5

        It is not always the case that the nil radical is generated
        by nilpotent generators. Here is an example of order 64,
        that is part of the data base in this package. We verify
        that the generators of the nil radical are indeed non-zero
        and nilpotent::

            sage: H = CohomologyRing(64,242)
            sage: H.make()
            sage: H.nil_radical()
            b_1_0*b_1_2+b_1_0^2,
            b_1_0*b_1_3+b_1_0*b_1_1+b_1_0^2
            sage: print(H('b_1_0*b_1_2+b_1_0^2'))
            2-Cocycle in H^*(Syl2(L3(4)); GF(2)),
            represented by
            [1 0 1 0 0 0 0 0]
            sage: print(H('b_1_0*b_1_3+b_1_0*b_1_1+b_1_0^2'))
            2-Cocycle in H^*(Syl2(L3(4)); GF(2)),
            represented by
            [1 1 0 1 0 0 0 0]
            sage: print(H('b_1_0*b_1_2+b_1_0^2')^2)
            4-Cocycle in H^*(Syl2(L3(4)); GF(2)),
            represented by
            [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
            sage: print(H('b_1_0*b_1_3+b_1_0*b_1_1+b_1_0^2')^2)
            4-Cocycle in H^*(Syl2(L3(4)); GF(2)),
            represented by
            [0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]

        In a previous version, the nil radical of the cohomology ring of an
        abelian group was incorrectly computed. Let us test that it is fixed::

            sage: H = CohomologyRing(16,2)
            sage: H.make()
            sage: H.nil_radical()
            c_1_0,
            c_1_1
            sage: print(H)
            <BLANKLINE>
            Cohomology ring of Small Group number 2 of order 16 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_1: 2-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_2_2: 2-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_1_0: 1-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_1_1: 1-Cocycle in H^*(SmallGroup(16,2); GF(2))]
            Minimal list of algebraic relations:
            [c_1_0^2,
             c_1_1^2]

        """
        if not self.completed:
            raise ValueError("The cohomology computation is not complete, yet")
        singular(self).set_ring()
        if self.NILRADICAL:
            OUT = singular.ideal(self.NILRADICAL)
            self.delprop('NILRADICAL')
            return OUT
        if not self.MaxelPos: # i.e., we have an abelian group!
            NILS = [x.name() for x in self.Gen if (x**2).is_zero()]
            if NILS:
                return singular('std(ideal(%s))'%','.join(NILS))
            return singular.ideal(0)
        NILS = [self.nil_preimage(n) for n in self.MaxelPos]
        return singular('groebner(intersect(%s))'%','.join([N.name() for N in NILS]))

    def nilspace(self, d):
        r"""
        Return a basis of the space of nilpotent elements in degree `d`.

        INPUT:

        - `d`, the degree (integer)

        OUTPUT:

        - A list of elements of ``self`` forming a basis of the degree `d`
          nilpotent elements.

        NOTE:

        The method :meth:`nil_radical` returns the ideal formed by all
        nilpotent elements, which probably is more useful in practical
        applications. However, it may happen that the nil radical can not
        easily be computed, and then it may be helpful to compute it degree by
        degree.

        .. WARNING::

            This method is only implemented in characteristic 2!

        ALGORITHM:

        An element of a mod-`2` cohomology ring of a finite group `G` is
        nilpotent if and only if the restrictions to all maximal
        `2`-elementary abelian subgroups of `G` is zero.

        .. SEEALSO::

            :meth:`nil_radical`

        EXAMPLES:

        The following three cohomology rings have the same generator degrees
        and Poincaré series::

            sage: from pGroupCohomology import CohomologyRing
            sage: H1 = CohomologyRing(64, 18)
            sage: H2 = CohomologyRing(64, 19)
            sage: H3 = CohomologyRing(64, 25)
            sage: H1.poincare_series() == H2.poincare_series() == H3.poincare_series()
            True
            sage: H1.degvec == H2.degvec == H3.degvec
            True

        However, the cohomology rings are not isomorphic, which is shown by
        the Poincaré series of their nil radicals. We compute the difference
        with the Poincaré series of the cohomology ring, since this tells the
        dimension of the nil radical in each degree::

            sage: p1 = H1.poincare_series() - H1._poincare_series_of_ideal_(H1.nil_radical())
            sage: p2 = H2.poincare_series() - H2._poincare_series_of_ideal_(H2.nil_radical())
            sage: p3 = H3.poincare_series() - H3._poincare_series_of_ideal_(H3.nil_radical())
            sage: p1!=p2!=p3!=p1
            True
            sage: P.<t> = PowerSeriesRing(QQ)
            sage: P(p1.numerator())/p1.denominator()
            2*t + 2*t^2 + 4*t^3 + 4*t^4 + 6*t^5 + 8*t^6 + 9*t^7 + 10*t^8 + 13*t^9 + 14*t^10 + 17*t^11 + 18*t^12 + 21*t^13 + 24*t^14 + 26*t^15 + 28*t^16 + 32*t^17 + 34*t^18 + 38*t^19 + 40*t^20 + O(t^21)
            sage: P(p2.numerator())/p2.denominator()
            2*t + 2*t^2 + 4*t^3 + 4*t^4 + 4*t^5 + 6*t^6 + 7*t^7 + 8*t^8 + 11*t^9 + 12*t^10 + 15*t^11 + 16*t^12 + 17*t^13 + 20*t^14 + 22*t^15 + 24*t^16 + 28*t^17 + 30*t^18 + 34*t^19 + 36*t^20 + O(t^21)
            sage: P(p3.numerator())/p3.denominator()
            2*t + 2*t^2 + 4*t^3 + 4*t^4 + 5*t^5 + 7*t^6 + 8*t^7 + 9*t^8 + 12*t^9 + 13*t^10 + 16*t^11 + 17*t^12 + 19*t^13 + 22*t^14 + 24*t^15 + 26*t^16 + 30*t^17 + 32*t^18 + 36*t^19 + 38*t^20 + O(t^21)

        Hence, we expect to see different dimensions of the nil radical
        starting in degree 5. Let is compare with the results of a degree-wise
        computation::

            sage: [len(H1.nilspace(d)) for d in range(10)]
            [0, 2, 2, 4, 4, 6, 8, 9, 10, 13]
            sage: [len(H2.nilspace(d)) for d in range(10)]
            [0, 2, 2, 4, 4, 4, 6, 7, 8, 11]
            sage: [len(H3.nilspace(d)) for d in range(10)]
            [0, 2, 2, 4, 4, 5, 7, 8, 9, 12]

        Here are explicit bases in degree 5::

            sage: H1.nilspace(5)
            [a_5_8: 5-Cocycle in H^*(SmallGroup(64,18); GF(2)),
             a_5_5: 5-Cocycle in H^*(SmallGroup(64,18); GF(2)),
             ((b_2_3)**2)*(a_1_1): 5-Cocycle in H^*(SmallGroup(64,18); GF(2)),
             ((b_2_2)**2)*(a_1_0): 5-Cocycle in H^*(SmallGroup(64,18); GF(2)),
             (a_2_0)*(b_3_5): 5-Cocycle in H^*(SmallGroup(64,18); GF(2)),
             (a_2_0)*(b_3_4): 5-Cocycle in H^*(SmallGroup(64,18); GF(2))]
            sage: H2.nilspace(5)
            [((b_2_2)**2)*(a_1_1): 5-Cocycle in H^*(SmallGroup(64,19); GF(2)),
             (a_2_1)*(b_3_5): 5-Cocycle in H^*(SmallGroup(64,19); GF(2)),
             (a_2_0)*(b_3_5): 5-Cocycle in H^*(SmallGroup(64,19); GF(2)),
             (a_2_0)*(b_3_4): 5-Cocycle in H^*(SmallGroup(64,19); GF(2))]
            sage: H3.nilspace(5)
            [a_5_4: 5-Cocycle in H^*(SmallGroup(64,25); GF(2)),
             ((b_2_2)**2)*(a_1_1): 5-Cocycle in H^*(SmallGroup(64,25); GF(2)),
             ((b_2_2)**2)*(a_1_0): 5-Cocycle in H^*(SmallGroup(64,25); GF(2)),
             (a_2_1)*(b_3_5): 5-Cocycle in H^*(SmallGroup(64,25); GF(2)),
             (a_2_0)*(b_3_5): 5-Cocycle in H^*(SmallGroup(64,25); GF(2))]

        """
        if self.base_ring().characteristic()%2:
            raise NotImplementedError("A degree-wise computation of nilspaces is only implemented in characteristic 2")
        D = {}
        origS = self.standard_monomials(d)
        S = [self(s) for s in origS]
        MList = []
        lenS = len(S)
        for i,x in enumerate(S):
            row = []
            for pos in self.MaxelPos:
                phi = self.restriction_maps()[pos][1]
                row.extend(phi(x).MTX()._rowlist_(0))
            row.extend([0]*i+[1]+[0]*(lenS-i-1))
            MList.append(row)
        M = Matrix(self.base_ring(), MList)
        M.echelonize()
        out = []
        for i,p in enumerate(M.pivots()):
            if M.ncols()-p<=lenS:
                out.append(None)
                for j in range(1,lenS+1):
                    if M[i,-j]:
                        if out[-1] is None:
                            out[-1]=M[i,-j]*S[-j]
                        else:
                            out[-1]+=M[i,-j]*S[-j]
        return out

    def _makeOrderMatrix_(self):
        """
        Create an integer matrix in Singular, defining David Green's matrix order for ``self``.

        OUTPUT:

        The matrix is defined in the Singular interface under the
        name ``self.prefix+'M'``.

        EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: H._makeOrderMatrix_()
        sage: singular('%sM'%(H.prefix))
             2     1     1
            -1     0     0
             0    -1     0

        """
        # The following is the raw data that we want to turn into something that Singular can understand
        if singular.eval('defined(%sM)'%(self.prefix))=='1':
            singular.eval('kill %sM'%(self.prefix))
        cdef list RawList = [self.degvec]
        cdef int rk = 1
        cdef int rk_tmp = Matrix(ZZ, RawList+[[-(X.rdeg() or 0) for X in self.Gen]]).rank()
        if rk_tmp > rk:
            RawList = RawList+[[-(X.rdeg() or 0) for X in self.Gen]]
            rk = rk_tmp
        rk_tmp = Matrix(ZZ, RawList+[[-(X.ydeg() or 0) for X in self.Gen]]).rank()
        if rk_tmp > rk:
            RawList = RawList+[[-(X.ydeg() or 0) for X in self.Gen]]
            rk = rk_tmp
        # First, we send these lines to Singular, creating the first lines of the matrix
        singular.eval('intmat %sM[%d][%d] = '%(self.prefix,len(self.Gen),len(self.Gen)) + ','.join([str(x) for x in add(RawList,[])]))
        M = Matrix(ZZ,RawList).transpose()
        # The rest of the order matrix should provide a reverse lexicographic order
        # idea:
        #     add colums (starting at the last one). If the rank increases then
        #     that place is irrelevant for (rev)lex order
        # Hence, we test, for what N.nrows()>i>=0, M[i:].rank() increases. For these i,
        # we don't need another entry.
        critrows = len(self.degvec)*[1] # will add a row with -1 at position i if critrows[i]==1
        rk_tmp = 0
        cdef int i,j
        cdef int Mnrows = M.nrows()
        for i from Mnrows > i >= 0:
            if M[i:Mnrows].rank() > rk_tmp:
                rk_tmp+=1
                critrows[i]=0
            if rk_tmp==M.ncols():
                break
        j = len(RawList) # Row number j of the Singular matrix is already ok
        for i from 0 <= i < len(critrows):
            if critrows[i]:
                j=j+1
                singular.eval('%sM[%d,%d] = -1'%(self.prefix,j,i+1))

    def PrescribedRestrictions(self, L):
        """
        Try to construct a cochain of ``self`` that has given restrictions to the elementary abelian subgroups.

        INPUT:

        - ``L``: a list of elements of the form ``[i,C]``, where

          * ``i``: the identifier (integer) of a special subgroup
          * ``C``: an element of the ``i``-th special subgroup

        OUTPUT:

        A cochain that has restrictions prescribed in ``L``,
        or ``None``, if such cochain doesn't exist.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()

        To simplify notation, we give names to the two isomorphism
        types of special subgroups::

            sage: Z = H.subgps[(2,1)]
            sage: M = H.subgps[(4,2)]

        We define cochains in ``Z`` and in ``M``, and try to find
        common lifts in ``H``. Note that ``M`` corresponds to two
        pairwise non-conjugate maximal elementary abelian
        subgroups of the dihedral group, while ``Z`` corresponds
        to the greatest central elementary abelian subgroup.
        ::

            sage: c = Z.standardCochain(2,0)
            sage: m1 = M.standardCochain(2,0)
            sage: m2 = M.standardCochain(2,1)
            sage: m3 = M.standardCochain(2,2)
            sage: print(H.PrescribedRestrictions([[1,c],[2,m2]]))
            None
            sage: print(H.PrescribedRestrictions([[1,c],[2,m1+m2]]))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 0 1]

        Note that the lift is not unique. If we also prescribe a
        cochain in the third pecial subgroup, we still get a lift
        of ``[1,c]`` and ``[2,m1+m2]``, but a different
        lift::

            sage: print(H.PrescribedRestrictions([[1,c],[2,m1+m2],[3,m1+m2+m3]]))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 1 1]

        Finally, we test whether we really have the restrictions
        that we want::

            sage: L = H.PrescribedRestrictions([[1,c],[2,m1+m2],[3,m1+m2+m3]])
            sage: H.restriction_maps()[1][1](L) == c
            True
            sage: H.restriction_maps()[2][1](L) == m1+m2
            True
            sage: H.restriction_maps()[3][1](L) == m1+m2+m3
            True

        """
        cdef int i,j,k
        cdef int p = self.Resl.coef()
        cdef MTX tmpM
        if not (isinstance(L,list) or isinstance(L,tuple)):
            raise TypeError("list or tuple expected")
        d = L[0][1].deg()
        for X in L:
            if not ((isinstance(X, list) or isinstance(X,tuple)) and (len(X)==2)):
                raise TypeError("argument must be a list/tuple of lists/tuple of length 2")
            if not ((isinstance(X[0],int) or isinstance(X[0],Integer)) and (isinstance(X[1],COCH))):
                raise TypeError("Pairs (integer, COCH) expected")
            if not (X[1].deg()==d):
                raise TypeError("Cochains must all have the same degree")
            if not (self.RestrMaps[X[0]][1].src() is X[1].resolution()):
                raise TypeError("Cochain (2nd list element) must belong to the specified subgroup (1st list element)")
        coho_logger.info("Simultaneously lifting subgroup cochains of degree %d", self, d)
        cdef int RK = self.Resl.rank(d)
        for X in L:
            coho_logger.debug("> Restriction to %s subgroup (order %s)", self, Integer(X[0]).ordinal_str(),self.RestrMaps[X[0]][0][0])
            while (self.RestrMaps[X[0]][1].knownDeg()<d):
                self.RestrMaps[X[0]][1].lift()
        self.Resl.free_ugb()
        coho_logger.debug("> Evaluating restrictions of ring generators", self)
        cdef int sum_rk = add([self.RestrMaps[X[0]][1].src().rank(d) for X in L])
        cdef int src_rk
        cdef list ttmpL
        cdef list tmpL
        cdef Matrix_t *tmpMTX
        if coho_options['useMTX']:
            coho_logger.debug("> > Construct MTX matrix for elimination", self)
            tmpL = []
            for i from 0 <= i < RK:
                ttmpL = []
                for X in L:
                    tmpM = self.RestrMaps[X[0]][1][d]
                    src_rk = self.RestrMaps[X[0]][1].src().rank(d)
                    for j from 0 <= j < src_rk:
                        ttmpL.append(tmpM[j*RK+i,0])
                tmpL.append(ttmpL + i*[0]+[1]+(RK-i-1)*[0])
            tmpMTX = rawMatrix(p, tmpL)
            M = new_mtx(tmpMTX, None)
        else:
            coho_logger.debug("> Construct matrix for elimination", self)
            M = Matrix(GF(p), RK, sum_rk+RK, 0)
            for i from 0 <= i < RK:
                M[i] = add([(self.RestrMaps[X[0]][1]*self.standardCochain(d,i)).MTX()._rowlist_(0) for X in L], []) + i*[0]+[1]+(RK-i-1)*[0]
        coho_logger.debug("> > Compute echelon form of %dx%d matrix"%(M.nrows(),M.ncols()), self)
        M.echelonize()
        coho_logger.debug("> > echelon is computed", self)
        cdef tuple Piv = M.pivots()
        cdef list RestL = add([X[1].MTX()._rowlist_(0) for X in L],[])
        cdef MTX RestM = new_mtx(MatAlloc(p, 1, sum_rk), M)
        Lift = new_mtx(MatAlloc(p, 1, RK), M)
        cdef int lenPiv = len(Piv)
        cdef list RowL
        cdef Matrix_t *delM
        for i from 0 <= i < lenPiv:
            if (Piv[i]<sum_rk) and RestL[Piv[i]]:
                if coho_options['useMTX']:
                    RowL = M._rowlist_(i)
                    delM = rawMatrix(p,[RowL[sum_rk:]])
                    MatAddMul(Lift.Data, delM, <FEL>(RestL[Piv[i]]))
                    MatFree(delM)
                    delM = rawMatrix(p,[RowL[:sum_rk]])
                    MatAddMul(RestM.Data, delM, RestL[Piv[i]])
                    MatFree(delM)
                else:
                    delM = rawMatrix(p,[M[i].list()[sum_rk:]])
                    MatAddMul(Lift.Data, delM, RestL[Piv[i]])
                    MatFree(delM)
                    delM = rawMatrix(p,[M[i].list()[:sum_rk]])
                    MatAddMul(RestM.Data, delM, RestL[Piv[i]])
                    MatFree(delM)

        if RestM._rowlist_(0) == RestL:
            Lift.set_immutable()
            coho_logger.info("Simultaneous lift was successful!", self)
            return COCH(self, d,'Lift',Lift)
        coho_logger.info("There was no simultaneous lift", self)
        return None

###################################################
## Auxiliary methods for Benson's test
## -- new version: work with cochains.
    def dickson_in_subgroup(self,ID):#r,z):
        """
        Compute Dickson classes for an elementary abelian group, considered as subgroup of the group of  `self``.

        INPUT:

        - ``ID``: the small groups address (pair of integers) of
          some elementary abelian subgroup of ``self``.

        OUTPUT:

        Let `G` be the finite `p`-group whose cohomology ring ``self``
        represents. The attribute ``subgbDickson`` of self is changed
        and contains elements of degree `p^{r-z}-p^{r-z-i}` of the
        cohomology ring of the elementary abelian group `V` described
        by ``ID``, where `r` is the `p`-rank of `G`, `z` is the rank
        of the centre of `G`, and `i = 1,...,r-z`.  These elements are
        constructed using Dickson invariants in the polynomial part of
        the cohomology of `V`, vanishing on the first `z`
        generators. Note that in some cases a trivial element results,
        but it still has the stated degree.

        NOTE:

        For applying Benson's or Symonds' completeness criterion, one
        has to find Dickson classes in the ambient group that
        simultaneously restrict to (powers of) the classes in the
        special subgroups found with dickson_in_subgroup. However, if
        `p^{r-z}-p^{r-z-i}` is too large, one should use
        :meth:`find_dickson`, that avoids the construction of elements
        of high degrees.

        EXAMPLES:

        We choose a group that has two different isomorphism classes
        of maximal elementary abelian subgroups::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(32,27, from_scratch=True)

        The Dickson invariants for the maximal elementary abelian
        subgroups were already computed when creating ``H``. We
        destroy them on purpose and reconstruct them::

            sage: H.subgpDickson = {}
            sage: H.dickson_in_subgroup((8,5))
            sage: sorted(H.subgpDickson.items())
            [((8, 5),
              [(c_1_2)**2: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
               0: 3-Cocycle in H^*(SmallGroup(8,5); GF(2))])]
            sage: H.dickson_in_subgroup((16,14))
            sage: sorted(H.subgpDickson.items())
            [((8, 5),
              [(c_1_2)**2: 2-Cocycle in H^*(SmallGroup(8,5); GF(2)),
               0: 3-Cocycle in H^*(SmallGroup(8,5); GF(2))]),
             ((16, 14),
              [(c_1_2)*(c_1_2)+(c_1_2)*(c_1_3)+(c_1_3)*(c_1_3): 2-Cocycle in H^*(SmallGroup(16,14); GF(2)),
               (c_1_2)*((c_1_2)*(c_1_3))+(c_1_2)*((c_1_3)*(c_1_3)): 3-Cocycle in H^*(SmallGroup(16,14); GF(2))])]

        """
        if self.subgps[ID].knownDeg<2:
            self.subgps[ID].make() #raise RuntimeError, "we need to know the cohomology ring up to degree 2"
        if self.subgpDickson is None:
            self.subgpDickson = {}
        D = DICKSON(self.Resl.coef())
        r = self.pRank
        z = self.CenterRk
        if self.Resl.coef()==2:
            t = len(self.subgps[ID].Gen) - z
        else:
            t = len(self.subgps[ID].Gen)/2 - z
        if t<0:
            raise RuntimeError("The p-rank of the center must not exceed the rank of a maximal elementary abelian subgroup")
        if t==0:
            return
        coho_logger.info("Computing Dickson invariants in elementary abelian subgroup of rank %d", self, t+z)
        cdef list DicksonList = []
        cdef int j,i,k
        p = self.Resl.coef()
        cdef int m = r-z
        for j from 1<=j<=m:
            if r == z+t:
                DicksonList.append(D(t,t-j))
            elif (j>t):
                DicksonList.append(0)
            else:
                DicksonList.append(D(t,t-j)**(p**(m-t)))
        ## DicksonList contains polynomial descriptions of cochains.
        ## Next, we want to turn them into cohomology classes.
        cdef list NewDicksonList = []
        for k from 0<=k<m:
            if DicksonList[k]==0: # have to append 0-cochain. self.Gen[0]**(p**(r-z)-p**(r-z-k-1)) always is of the right degree
                NewDicksonList.append(0*self.subgps[ID].Gen[0]**(p**(m)-p**(m-k-1)))
            else:
                L=DicksonList[k].exponents()
                C=DicksonList[k].coefficients()
                if t>1:
                    NewDicksonList.append(add([ Mul(add([ [self.subgps[ID].Gen[z+j]]*(L[i][j]) for j in xrange(t)],[]),int(C[i])) for i in xrange(1,len(L))], Mul(add([ [self.subgps[ID].Gen[z+j]]*(L[0][j]) for j in xrange(t)],[]),int(C[0])) )) # Mul (in contrast to mul) collects the product from right to left
                else:
                    NewDicksonList.append(add([(self.subgps[ID].Gen[z]**(L[i]))*int(C[i]) for i in xrange(1,len(L))], (self.subgps[ID].Gen[z]**(L[0]))*int(C[0])))
        self.subgpDickson[ID] = NewDicksonList

    def lift_dickson(self,i,j):
        """
        Try to lift some power of some Dickson class.

        INPUT:

        - `i = 0, 1, 2, ...` - indicates which Dickson class of the
          maximal elementary abelian subgroups ought to be lifted.
        - `j = 0, 1, 2, ...` - indicates which power of that Dickson
          class ought to be lifted.

        OUTPUT:

        If the underlying group is a finite `p`-group then let `n=p^j`,
        otherwise let `n=j`. If it is possible to find a cochain of
        self that simultaneously restricts to the `n`-th power of the
        `i`-th Dickson classes of all maximal elementary abelian
        subgroups, potentially modified by nilpotent classes, then
        this cochain is returned.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: print(H.lift_dickson(0,0))
            1-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1]
            sage: print(H.lift_dickson(0,1))
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [1 1 0]

        Indeed, the restrictions of these classes to the two
        maximal elementary abelian subgroups coincides with
        their Dickson classes, respectively the square of the
        Dickson classes::

            sage: H.subgpDickson[4,2][0] == H.restriction_maps()[2][1](H.lift_dickson(0,0))
            True
            sage: H.subgpDickson[4,2][0] == H.restriction_maps()[3][1](H.lift_dickson(0,0))
            True
            sage: H.subgpDickson[4,2][0]**2 == H.restriction_maps()[2][1](H.lift_dickson(0,1))
            True
            sage: H.subgpDickson[4,2][0]**2 == H.restriction_maps()[3][1](H.lift_dickson(0,1))
            True

        """
        if self.CenterRk == 0: # not a prime-power group
            n = j
            coho_logger.info("Try to lift %s power of %s Dickson invariant", self, Integer(n).ordinal_str(), Integer(i).ordinal_str())
            L=[[X[0],(self.subgpDickson[X[1][0]][i])**n] for X in self.RestrMaps.items() if X[0] in self.MaxelPos] # here, we don't restrict to zero on the center.
        else:
            n = self.Resl.coef()**j
            coho_logger.info("Try to lift %s power of %s Dickson invariant", self, Integer(n).ordinal_str(), Integer(i).ordinal_str())
            L=[[X[0],(self.subgpDickson[X[1][0]][i])**n] for X in self.RestrMaps.items() if X[0]!=1]
        return self.PrescribedRestrictions(L)


###################################################
## Auxiliary methods for Benson's test
##  -- find lifted Dickson invariants based on elimination
    @temporary_result
    def find_dickson(self):
        """
        Find classes of self that simultaneously restrict to the Dickson classes for special subgroups.

        NOTE:

        The method first checks if the current ring approximation
        contains parameters. If this is not the case (e.g., if
        a maximal Duflot regular sequence can not be found yet)
        then nothing is done. If Dickson invariants have been
        previously constructed (perhaps by a different method)
        then nothing is done as well.

        OUTPUT:

        The attribute ``Dickson`` (a list) is changed. The entries
        corresponding to factors of successfully lifted Dickson
        classes are strings that define a polynomial in the generators
        of self yielding the lift.

        If the group is not of prime power order, the restrictions of
        the parameters constructed by this method to any maximal
        elementary abelian subgroup in a Sylow subgroup are Dickson
        invariants.

        If the group is a `p`-group, the restrictions *to a complement
        of the greatest central elementary abelian subgroup* in any
        maximal elementary abelian subgroup are Dickson invariants.

        EXAMPLES:

        We use the option ``useElimination``, in order to avoid that the
        Dickson classes will be lifted by a different method.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,33, useElimination=True, from_scratch=True)

        The group is of `p`-rank 3 and its center has rank 1. So, we
        will eventually get two Dickson classes::

            sage: H.pRank
            3
            sage: H.CenterRk
            1
            sage: H.Dickson
            [None, None]

        We try whether the Dickson classes can be lifted after
        computing the ring structure out to degree 2::

            sage: H.make(2)
            sage: H.find_dickson()
            False
            sage: H.Dickson
            [None, None]

        In degree 4, still nothing is done. This is since there
        is no Duflot regular sequence yet.
        ::

            sage: H.make(4)
            sage: H.find_dickson()
            False
            sage: H.Dickson
            [None, None]
            sage: H.duflot_regular_sequence()
            []

        We compute out to degree 8, since we happen to know
        that there is the Duflot regular generator waiting.
        When using :meth:`make`, the Dickson invariants would
        be automatically determined. So, we work around.
        ::

            sage: H.make(7)
            sage: H.next()
            sage: H.Dickson
            [None, None]

        Now, we construct the Dickson elements manually, and find that
        indeed they could have been found in degree 4 already::

            sage: H.find_dickson()
            True
            sage: H.Dickson
            ['b_4_6+b_2_1^2', 'b_3_4+b_3_2']

        """
        if self.pRank == self.CenterRk:
            return True
        if self._found_dickson is not None:
            self.Dickson = [t for t in self._found_dickson]
            return True
        if self.Dickson is not None and self.Dickson.count(None)==0:
            return True
        if not self.verify_parameters_exist():
            return False
        cdef int i
        if not self.Gen:
            return False
        if self.knownDeg<2:
            return
        coho_logger.info("Try to lift Dickson invariants using elimination methods", self)

        cdef int p = self.Resl.coef()
        self.set_ring()
        ######################
        ## This shall become the intersection of lifts of the Nil radicals of the special subgroups
        DicksonLift,NilRad = self.find_dickson_in_subgroup(self.MaxelPos[0])
        if DicksonLift is None:
            return
        for Sg,Rk in zip(self.MaxelPos[1:],self.MaxelRk[1:]):
            NewDicksonLift, NewNilRad = self.find_dickson_in_subgroup(Sg)
            if NewDicksonLift is None:
                return
            ## Make sure that the items of DicksonLift and NewDicksonLift have the same degree
            singular.eval('intvec %sdvOld = degvec(%s)'%(self.prefix,DicksonLift.name()))
            singular.eval('intvec %sdvNew = degvec(%s)'%(self.prefix,NewDicksonLift.name()))
            TrueRk = min([int(singular.eval("nrows(%sdvOld)"%self.prefix)),
                          int(singular.eval("nrows(%sdvNew)"%self.prefix)),
                          Rk])
            singular.eval('for (int tmp_i=1;tmp_i<=%d;tmp_i++){ if (%sdvOld[tmp_i]>%sdvNew[tmp_i]) { %s[1,tmp_i]=%s[1,tmp_i]**(%sdvOld[tmp_i] div %sdvNew[tmp_i]); } else { if(%sdvOld[tmp_i]>0){ %s[1,tmp_i]=%s[1,tmp_i]**(%sdvNew[tmp_i] div %sdvOld[tmp_i]); }} }'%(TrueRk,self.prefix,self.prefix,NewDicksonLift.name(),NewDicksonLift.name(), self.prefix,self.prefix, self.prefix,DicksonLift.name(),DicksonLift.name(),self.prefix,self.prefix))
            singular.eval('kill tmp_i')
            singular.eval('kill %sdvOld'%(self.prefix))
            singular.eval('kill %sdvNew'%(self.prefix))
            if self.CenterRk == 0: # we have a non-primepower group
                singular.eval('%s = cosetIntersect(%s, %s, %s, %s, %s)'%(DicksonLift.name(), DicksonLift.name(), NilRad.name(), NewDicksonLift.name(), NewNilRad.name(), ','.join([str(j) for j in Integer (self._Order*self._prime**(self._HSyl.DicksonExp or 3)/self._POrder).divisors()])))
            else:
                singular.eval('%s = cosetIntersect(%s, %s, %s, %s, %s)'%(DicksonLift.name(), DicksonLift.name(), NilRad.name(), NewDicksonLift.name(), NewNilRad.name(), ','.join([str(p**i) for i in range(self._property_dict.get('DicksonExp',3))])))
            if str(DicksonLift.typeof())=='int':
                coho_logger.info("> simultaneous lift failed at %s subgroup", self, Integer(Sg).ordinal_str())
                return
            NilRad=NilRad.intersect(NewNilRad)
        #############
        ## Now, DicksonLift contains simultaneous lifts of the Dickson invariants.
        ## Try to optimize it, by factorizing the Dickson-lifts.
        ## But first, we need to save the original values, since factorisation
        ## may be interrupted.
        cdef list L=[]
        for i in range(1,DicksonLift.ncols()+1):
            L.append(singular.eval('%s[1,%d]'%(DicksonLift.name(),i)))
        if self.useFactorization:
            for i in range(1,DicksonLift.ncols()+1):
                try:
                    L[i-1] = self.small_factor(DicksonLift[1,i])
                except:
                    self.set_ring()
                    L[i-1] = self.small_factor(singular(L[i-1]))

        self.Dickson = L
        self.setprop('_found_dickson',[t for t in L])
        coho_logger.info( 'We succeeded to lift Dickson invariants!', self)
        return True

    def find_dickson_in_subgroup(self,n):
        """
        If possible, return a lift of the Dickson classes
        (type <SingularElement> matrix) and the nil-radical
        (type <SingularElement> ideal) of the `n`-th special
        subgroup. Result is cached.

        EXAMPLES:

        We use the option ``useElimination``, in order to avoid that the
        Dickson classes will be lifted by a different method.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,33, useElimination=True, from_scratch=True)
            sage: H.make(3)
            sage: H.find_dickson_in_subgroup(2)
            (None, None)
            sage: H.find_dickson_in_subgroup(3)
            (None, None)
            sage: H.make(4)
            sage: H.find_dickson_in_subgroup(2)
            (b_4_6+b_2_1^2,b_3_3, a_1_0,
            a_1_1,
            b_2_2,
            b_3_2,
            b_3_4+b_3_3,
            b_3_3^2+b_2_1*b_4_6,
            b_4_4^2+b_2_1^2*b_4_6)
            sage: H.find_dickson_in_subgroup(3)
            (b_4_6,b_3_4+b_3_2, a_1_0,
            a_1_1,
            b_2_1,
            b_3_3+b_3_2,
            b_4_4,
            b_3_2^2+b_2_2^3,
            b_3_4^2+b_2_2*b_4_6)

        """
        G = self.subgps[self.RestrMaps[n][0]]
        f = self.RestrMaps[n][1]
        coho_logger.info("Lift Dickson invariants of the %s special subgroup",self, Integer(n).ordinal_str())
        # we must assume that the subgroup cohomology  is known
        singular(G).set_ring()
        NilG = G.nil_radical()  # easy to compute

        cdef int i
        singular(G).set_ring()
        singular.eval('int tmp_i')
        dgb = singular.eval('degBound')
        singular.eval('degBound = 0')
        #########
        ## create Dickson invariants in subgroup
        DI = [singular('poly(Delta(%d,%d,%d,%d))'%(self.pRank,self.CenterRk,self.MaxelRk[self.MaxelPos.index(n)]-self.CenterRk,i+1)) for i in range(self.pRank-self.CenterRk)]

        #########
        ## try to lift Dickson invariants:
        DILift = []
        p = self._prime or self.Resl.coef()
        for di in DI:
            for i in range(self._property_dict.get('DicksonExp',3)):
                di_lift, NilPre = f.preimage(di,NilG) # It is cached!
                if di_lift is None:
                    singular(G).set_ring()
                    di = di**p
                else:
                    DILift.append(di_lift)
                    break
            if di_lift is None:
                singular.eval('kill tmp_i')
                singular.eval('degBound = '+dgb)
                coho_logger.info("> Lift failed", self)
                return None, None
        if not DILift:
            singular.eval('kill tmp_i')
            return None,None
        # Now, DILift contains Lifts of all Dickson invariants
        # (or powers thereof).
        # The lifts belong to the current basering, which is
        # singular(self), so that we must imap.
        name = singular(self).name()
        self.set_ring()
        LiftResult = singular.ideal(['imap(%s,%s)'%(name,t.name()) for t in DILift]).matrix()
        NilPre = singular(self).imap(NilPre)
        singular.eval('kill tmp_i')
        singular.eval('degBound = '+dgb)
        return (LiftResult,NilPre)

    def duflot_regular_sequence(self):
        """
        Return a Duflot regular sequence that is maximal in the current ring approximation.

        THEORY:

        A sequence of elements is called *Duflot regular*, if its restrictions to the greatest
        `p`-elementary abelian subgroup in the centre of a Sylow `p`-subgroup is regular.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(144,186,prime=3, from_scratch=True)
            sage: H.sylow_cohomology().duflot_regular_sequence()
            ['c_2_1', 'c_2_2']
            sage: H.make(4)
            sage: H.duflot_regular_sequence()
            ['c_4_0']
            sage: H.make()
            sage: H.duflot_regular_sequence()
            ['c_4_0', 'c_8_1']

        We compute the restrictions to the greatest central elementary abelian
        subgroup of a Sylow `3`-subgroup is a regular sequence, which are indeed
        regular::

            sage: r = H.restriction_maps()[1][1]; r
            Induced homomorphism of degree 0 from H^*(SmallGroup(144,186); GF(3)) to H^*(SmallGroup(9,2); GF(3))
            sage: [r(H(t)).as_polynomial() for t in H.duflot_regular_sequence()]
            ['c_2_2^2+c_2_1^2', 'c_2_1^2*c_2_2^2']

        """
        if self.CenterRk:
            return [t.name() for t in self.Gen if t.rdeg()]
        if self.knownDeg<2:
            return []
        totalRel = ''.join(self.Rel)
        if self.Resl.coef()%2:
            return [t.name() for t in self.Gen if (t.name() not in totalRel) and not t.deg()%2]
        return [t.name() for t in self.Gen if (t.name() not in totalRel)]

    @permanent_result
    def filter_regular_gready_parameters(self, first_parameters=[], BreakPoint=None, ignore_nilpotent=True):
        r"""
        Greadily explore smallest degree filter regular parameters.

        INPUT:

        - ``first_parameters`` (optional list) -- list of strings defining some
          filter regular parameters that come after the Duflot elements
        - ``BreakPoint`` (optional integer) -- maximal number of parameter candidates
          tested in each degree. Default ``None`` means unbounded.
        - ``ignore_nilpotent`` (optional bool, default True) -- whether to ignore
          nilpotent generators in the enumeration of filter regular parameters;
          there are filter regular parameters that can be expressed without nilpotent
          generators, but we are not sure if the smallest degree parameters can
          be obtained in that way, too.

        OUTPUT:

        - A system of filter regular parameters.
        - The filter degree type is computed and stored. If the filter degree
          type of this ring has been computed before, it is asserted that the
          results are equal. Also it is tested whether the result contradicts
          the strong form of Dave Benson's regularity conjecture.

        ..ALGORITHM::

            It is assumed that the completeness of the ring has already been proved.
            The function starts with a Duflot regular sequence and finds the
            new parameters by enumerating potential parameters in a greedy way.

        ..WARNING::

            We do not guarantee that this routine will always succeed, as we have
            no proof. However, on all groups of order 64 and 81, it works, and
            on about 10 percent of cases it yields filter regular parameters in
            smaller degrees than our previous methods.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()        # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,32,from_scratch=True)
            sage: H.make()
            sage: H.filter_regular_parameters()
            ['c_4_11',
             'b_1_1*b_3_6+b_1_1^4+b_2_3^2+b_2_2^2+b_2_1^2',
             'b_1_1^3*b_3_6+b_2_3^2*b_1_1^2+b_2_2*b_1_1*b_3_6+b_2_2*b_2_3^2+b_2_2^2*b_1_1^2+b_2_1*b_2_3^2',
             'b_1_1']

        So, we have parameters in degrees 4, 4, 6 and 1. Note that after
        computing the filter degree type, the ring is automatically stored,
        in order to preserve the result of this potentially very difficult
        computation (a warning is logged)::

            sage: H.filter_degree_type()
            H^*(SmallGroup(64,32); GF(2)):
                      Updating stored data after computation of filter degree type
            [-1, -2, -3, -4, -4]

        We delete the previous result, compute filter regular parameters in
        degrees 4, 2, 2 and 1, and find that the filter degree type coincides
        with what was computed above::

            sage: H.delprop('fdt')
            sage: CohomologyRing.global_options('info')
            sage: H.filter_regular_gready_parameters()
            H^*(SmallGroup(64,32); GF(2)):
                Compute filter_regular_gready_parameters
                Computing quotient modulo Duflot regular sequence ['c_4_11']
                Exploring 2nd filter-regular parameter in degree 2
                Determine degree 2 standard monomials
            explore_one_parameter:
                8 = (2-1)^1*2^3 parameter candidates
                We found a parameter.
                > But it is not filter-regular.
                We found a parameter.
                > It is filter-regular.
            H^*(SmallGroup(64,32); GF(2)):
                Exploring 3rd filter-regular parameter in degree 2
                Determine degree 2 standard monomials
            explore_one_parameter:
                4 = (2-1)^1*2^2 parameter candidates
                We found a parameter.
                > It is filter-regular.
            H^*(SmallGroup(64,32); GF(2)):
                Exploring 4th filter-regular parameter in degree 2
                Determine degree 2 standard monomials
            explore_one_parameter:
                2 = (2-1)^1*2^1 parameter candidates
                We found a parameter.
                > It is filter-regular.
            ['c_4_11', 'b_2_2+b_2_1', 'b_2_3', 'b_1_1^2']
            sage: H.fdt
            [-1, -2, -3, -4, -4]

        """
        assert self.completed, "%r is not complete, search for smallest parameters doesn't apply"%self
        P = list(self.duflot_regular_sequence())
        # We originally coded this routine so that plain algebraically independent
        # parameters or regular parameters could be found.
        # - regularity==0: plain
        # - regularity==1: filter regular
        # - regularity==2: regular.
        # But we don't see a use case for it. Internally, we keep the code as
        # flexibly, but for now we hardcode regularity=1
        regularity = 1
        self.set_ring()
        dgb = singular.eval("degBound")
        singular.eval('degBound=0')
        Id = self.relation_ideal()
        if P:
            coho_logger.info('Computing quotient modulo Duflot regular sequence %s', self, P)
            sP = singular.ideal(P)
            singular.eval('%s=std(%s,%s)'%(Id.name(),Id.name(),sP.name()))
        p = self.base_ring().characteristic()
        HV = [[0] for para in P]
        DV = [Integer(singular.eval('deg(%s)'%para)) for para in P]
        HP0 = first_hilbert_series(Id)
        taste = {0:'', 1:'filter-regular', 2:'regular'}
        cdef list L
        try:
            while len(P) < self.dimension():
                if first_parameters:
                    x = first_parameters.pop(0)
                    para = singular(x)
                    coho_logger.info('Computing quotient modulo %s %s parameter (user provided)', self, Integer(len(P)+1).ordinal_str(), taste[regularity])
                    Id2 = Id.std(para)
                    coho_logger.debug('Testing filter regularity',self)
                    reg_vec = is_filter_regular(Id, para, HP0, Id2)
                    assert reg_vec, "{} is supposed to be filte regular.".format(para)
                    P.append(x)
                    if regularity == 1 or len(P) < self.dimension():
                        Id = Id2
                        HP0 = first_hilbert_series(Id)
                    HV.append(reg_vec)
                    DV.append(Integer(singular.eval('deg(%s)'%para.name())))
                else:
                    maxdim = p**self.dimension() - p**(self.dimension()-len(P))
                    for d in range(2, 2*maxdim+1):
                        coho_logger.info('Exploring %s %s parameter in degree %d', self, Integer(len(P)+1).ordinal_str(), taste[regularity], d)
                        if ignore_nilpotent:
                            L = [s for s in self.standard_monomials(d) if not ('a' in s)]
                        else:
                            L = self.standard_monomials(d)
                        para, x, reg_vec = explore_one_parameter(Id, L, p, BreakPoint, regularity, HP0)
                        if reg_vec:
                            P.append(singular.eval(para))
                            if regularity == 1 or len(P) < self.dimension():
                                singular.eval('%s=std(%s,%s)'%(Id.name(), Id.name(), para.name()))
                                HP0 = first_hilbert_series(Id)
                            HV.append(reg_vec)
                            DV.append(Integer(singular.eval('deg(%s)'%para.name())))
                            break
                assert para or (regularity==2), "Theoretical error: We should be able to find a system of %s parameters"%taste[regularity]

            if regularity == 1:
                # rfdt = vector of maximal degrees in the kernel resp. quotient
                PR = HP0.parent()
                t = PR.gen()
                Den = PR.prod([(1-t**d) for d in self.degvec])
                HS = HP0/Den
                if HS == 0:
                    HV.append([0])
                elif HS.denominator().degree():
                    raise RuntimeError('Theoretical error: The quotient by filter regular parameters must be finite dimensional')
                else:
                    HV.append(HS.numerator().list())

                rfdt = []
                for X in HV:
                    if X==[0]:
                        rfdt.append(-1)
                    else:
                        rfdt.append(len(X)-1)
                fdt = FilterDegreeType(DV,rfdt)
                if self.fdt:
                    assert self.fdt == fdt, 'Theoretical error: {} vs. {}, but the filter degree type cannot depend on the f.r. parameters'.format(self.fdt,fdt)
                else:
                    alpha = False
                    for i in range(1,len(fdt)):
                        if fdt[i] > -i:
                            alpha = True
                    if fdt[-1] > -len(fdt)+1:
                        alpha = True
                    if fdt[-1] < -len(fdt)+1:
                        raise RuntimeError("Theoretical error: We got a filter degree type %s, but the last value must not be smaller than %d!"%(repr(fdt),-len(fdt)+1))
                    self.setprop('fdt',fdt)
                    self.alpha = max([fdt[i]+i for i in range(len(fdt)-1)])
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
            return P
        finally:
            try:
                singular.eval('degBound='+dgb)
            except RuntimeError:
                pass

    @permanent_result
    def filter_regular_parameters(self):
        r"""
        Return elements of the ring approximation guaranteed to yield parameters in cohomology.

        OUTPUT:

        A list of strings, describing polynomials in ``self``, or ``None``.

        THEORY:

        (Powers of) Dickson elements in the polynomial part of the
        cohomology rings of maximal elementary abelian subgroups in a
        Sylow `p`-subgroup `S` of a finite group `G` give rise to a
        filter regular homogeneous system of parameters of the mod-`p`
        cohomology of `G` restricting to these Dickson elements,
        according to [Benson]_.

        The degree of these parameters may be very large. In
        [GreenKing]_, in the case that `G=S` is of prime power order,
        we propose to consider only Dickson elements in a complement
        of the greatest central elementary abelian subgroup `C` of `S`
        in the maximal abelian subgroups. We can show that these can
        be simultaneously lifted to cohomology elements of `G`, to
        which we refer as the *restricted Dickson elements*.  A filter
        regular hsop is then given by a maximal Duflot regular
        sequence, followed by the restricted Dickson elements.
        Moreover, parameters can be simplified by factorisation,
        potentially after adding a nilpotent element. This often
        yields fairly small parameters, but the factorisation may be
        quite difficult in some examples.

        In the case `G\not=S`, it is in general impossible to lift a
        power of the Dickson elements in complements of `C`. But if it
        is, the previous construction still yields a filter regular
        hsop. Therefore, we test whether the restricted Dickson
        elements of the cohomology of `S` happen to be stable. If they
        are, they yield a filter regular homogeneous system of
        parameters for the cohomology of `S`, together with a Duflot
        regular sequence. A factorisation may further simplify the
        parameters.

        Moreover, in either case, the last parameter found by the
        above construction could be replaced by any other parameter of
        smaller degree. See :meth:`find_small_last_parameter`

        EXAMPLES:

        Since we will access data from the cohomology of a subgroup,
        we will force its computation from scratch first::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: X = CohomologyRing(64,138,from_scratch=True)
            sage: X.make()
            sage: G = libgap.AlternatingGroup(8)
            sage: H = CohomologyRing(G,prime=2,GroupName='A8', from_scratch=True)

        We first demonstrate what happens in the cohomology ring of a
        sylow subgroup::

            sage: H.sylow_cohomology() is X
            True
            sage: H.sylow_cohomology().filter_regular_parameters()
            ['c_4_18', 'b_1_2^4+b_1_1^2*b_1_2^2+b_1_1^4+b_1_0^4+b_2_6^2+b_2_4*b_2_6+b_2_4^2', 'b_1_1^2*b_1_2^4+b_1_1^4*b_1_2^2+b_2_6^2*b_1_2^2+b_2_6^2*b_1_0^2+b_2_4*b_2_6*b_1_0^2+b_2_4*b_2_6^2+b_2_4^2*b_1_1*b_1_2+b_2_4^2*b_1_1^2+b_2_4^2*b_1_0^2+b_2_4^2*b_2_6', 'b_1_0']

        For computing the cohomology of `G`, we use the cohomology
        ring of an intermediate subgroup. It turns out that a filter
        regular hsop for the cohomology ring of that subgroup can be
        found by using Dickson elements in a complement of the centre
        of a Sylow subgroup::

            sage: H.subgroup_cohomology()
            H^*(SmallGroup(192,1493); GF(2))
            sage: H.subgroup_cohomology().filter_regular_parameters()
            ['c_4_10', 'b_1_0^4+b_2_2^2+b_2_0*b_2_2+b_2_0^2', 'b_3_6^2+b_3_2*b_3_5+b_3_2^2+b_2_2^2*b_1_0^2+b_2_0*b_2_2*b_1_0^2+b_2_0*b_2_2^2+b_2_0^2*b_1_0^2+b_2_0^2*b_2_2', 'b_1_0']

        We try if we can do the same for the cohomology of `G`::

            sage: H.make(8)
            sage: H.duflot_regular_sequence()
            ['c_4_1']
            sage: H.filter_regular_parameters()

        So, a maximal Duflot regular sequence is already available, but the
        remaining parameters are not. We compute out to degree 14 and then
        obtain filter regular parameters.
        ::

            sage: H.make(14)
            sage: H.filter_regular_parameters()
            ['b_3_1*b_5_2+b_2_0^4+c_4_1^2',
             'b_3_1^4+b_3_0^4+b_6_2*b_3_1^2+b_6_2^2+b_2_0^3*b_6_2+c_4_1*b_3_1*b_5_2+b_2_0*c_4_1*b_3_1^2+b_2_0^2*c_4_1^2',
             'b_7_6^2+b_3_1^3*b_5_2+b_6_2*b_3_1*b_5_2+b_2_0*b_6_2*b_3_1^2+b_2_0^3*b_3_1*b_5_2+b_2_0^4*b_6_2+b_2_0^2*c_4_1*b_3_1^2+b_2_0^2*c_4_1*b_6_2+c_4_1^2*b_3_0^2',
             'b_6_2']

        """
        if self._construct_fr_parameters():
            Par = [t for t in (self._final_parameters or self._current_parameters)]
            return Par

    def _construct_fr_parameters(self):
        """
        Try to construct reasonably small filter regular parameters.

        OUTPUT:

        ``True`` or ``False``, if parameters can be found or not.
        The attribute ``_current_parameters`` is assigned to a list of parameters (given by strings)

        NOTE:

        This is an auxiliary function for :meth:`filter_regular_parameters`
        and should not be called directly.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make(1)
            sage: H.duflot_regular_sequence()
            []
            sage: print(H)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 1
            Minimal list of generators:
            [b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            []

        Aparently this ring approximation has two regular parameters, namely the
        two ring generators. However, they would not yield parameters for the
        cohomology ring, and therefore we obtain::

            sage: H._construct_fr_parameters()
            False

        There is success in degree two, though::

            sage: H.next()
            sage: H._construct_fr_parameters()
            True
            sage: H._current_parameters
            ['c_2_2', 'b_1_1+b_1_0']

        """
        if self.knownDeg < 2:
            return False
        Par = self.duflot_regular_sequence()
        if len(Par) < (self.CenterRk or (self.CenterRk==0 and self.PCenterRk) or self.pRank or 0):
            coho_logger.info("We need to find more Duflot generators!", self)
            return False
        Par = Par + self.Dickson
        if not Par.count(None):
            self.setprop('_current_parameters',[t for t in Par])
            return True
        if Par.count(None)==1 and Par[-1] is None:
            Par[-1] = self.find_small_last_parameter(Par,self.knownDeg)
            if not Par.count(None):
                self.setprop('_current_parameters',[t for t in Par])
                return True
        if self.useElimination or self.completed: # the latter may occur if completeness was proved without filter regular parameters
            self.find_dickson()
            Par = self.duflot_regular_sequence() + self.Dickson
            if not Par.count(None):
                self.setprop('_current_parameters',[t for t in Par])
                return True
        return False

    def verify_parameters_exist(self):
        """
        Test whether the current ring approximation contains a HSOP for the cohomology ring.

        THEORY:

        The ring approximation contains a HSOP for the cohomology ring
        if and only if the cohomology rings of the maximal elementary
        abelian subgroups are finitely generated modules over the
        restriction of the ring approximation.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make(1)
            sage: print(H)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 1
            Minimal list of generators:
            [b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            []

        This ring is of Krull dimension two, which coincides with
        the dimension of the cohomology ring of ``SmallGroup(8,3)``
        (which is the dihedral group with 8 elements). But the ring
        approximation does not contain parameters for the cohomology
        ring, yet::

            sage: H.verify_parameters_exist()
            False

        Indeed, the restrictions of the current generators to any
        of the two maximal elementary abelian subgroups is only
        of Krull dimension one::

            sage: H.restrictions_as_string(2)
            ['0', 'c_1_1']
            sage: H.restrictions_as_string(3)
            ['c_1_1', '0']

        Hence, we have to compute one step further, and then succeed::

            sage: H.next()
            sage: H.verify_parameters_exist()
            True
            sage: H.parameters()
            ['c_2_2', 'b_1_1+b_1_0']

        """
        if not self.Gen:
            return False
        if self._parameters_do_exist:
            return True
        try:
            R = singular('basering')
        except TypeError:
            R = None
        cdef list L
        try:
            coho_logger.info("Testing whether parameters of the cohomology ring can be found", self)
            gb_command = self._gb_command()
            for i in self.MaxelPos:
                L = self.restrictions_as_string(i)
                self.RestrMaps[i][1].codomain().set_ring()
                if singular.eval('vdim(%s(ideal(%s)))'%(gb_command,','.join(L)))=='-1':
                    coho_logger.info("> Nein", self)
                    return False
            self.setprop('_parameters_do_exist',True)
            coho_logger.info("> Yes", self)
            return True
        finally:
            try:
                R.set_ring()
            except:
                pass

##########################################
# A potentially expensive heuristics to find small last parameters
    ## The is not @permanent, since it involves maps in the singular interface,
    ## and the domain could change over time
    @temporary_result
    def _parameter_restrictions(self, Par, radical=False):
        r"""
        Restrict a given set of elements to the maximal `p`\--elementary abelian subgroups.

        INPUT:

        - ``Par``, a frozenset of strings defining some elements of the ring approximation.
        - ``radical`` (optional bool, default ``False``): If ``True``, then the radical of
          the restricted ideal will be computed

        OUTPUT:

        A list of triples of the form (``cod``, ``phi``, ``I``), where

        - ``cod`` is a ring in singular,
        - ``phi`` is a map from the singular representation of ``self`` to ``cod``
        - ``I`` is a Gröbner basis of (the radical of) the restrictions of ``Par``
          under ``phi``, and ``I`` is of Krull dimension one.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,201)

        If the restrictions are of Krull dimension zero on all subgroups,
        an empty list is returned.

            sage: H._parameter_restrictions(['c_2_8', 'c_4_21', 'b_1_2^2+b_1_1*b_1_2+b_1_1^2'])
            []

        Otherwise, the restrictions respectively the radical of the restrictions is returned::

            sage: R = H._parameter_restrictions(['c_2_8', 'c_4_21'])
            sage: for (cod, phi, I) in R:
            ....:    cod.set_ring()
            ....:    print(list(I))
            [c_1_0^2, c_1_1^2*c_1_2^2+c_1_1^4]
            [c_1_0^2, c_1_1^2*c_1_2^2+c_1_1^4]
            [c_1_0^2, c_1_2^4+c_1_1^2*c_1_2^2+c_1_1^4]
            sage: R = H._parameter_restrictions(['c_2_8', 'c_4_21'], radical=True)
            sage: for (cod, phi, I) in R:
            ....:    cod.set_ring()
            ....:    print(list(I))
            [c_1_0, c_1_1*c_1_2+c_1_1^2]
            [c_1_0, c_1_1*c_1_2+c_1_1^2]
            [c_1_0, c_1_2^2+c_1_1*c_1_2+c_1_1^2]

        """
        if not Par:
            return tuple([])
        cdef dict cache = self._parameter_restriction_cache
        cdef list restrictions = []
        gb_command = self._gb_command()
        if radical:
            coho_logger.info("compute radicals of restricted parameter ideal", self)
            old_restrictions = self._parameter_restrictions(Par, radical=False)
            for cod_s, phi_s, I_s in old_restrictions:
                cod_s.set_ring()
                restrictions.append((cod_s, phi_s, getattr(I_s.radical(),gb_command)()))
            return restrictions
        singular = self.GenS.parent()
        self_s = singular(self)
        ch = self._prime or self.resolution().coef()
        try:
            dgb = singular.eval('degBound')
            try:
                br = singular('basering')
            except TypeError:
                br = None
            singular.eval('degBound=0')
            self_s.set_ring()
            Par_s = singular.ideal(list(Par))

            for pos in self.MaxelPos:
                phi = self.RestrMaps[pos][1]
                phi_s = singular(phi)
                cod_s = singular(phi.codomain())
                cod_s.set_ring()
                coho_logger.info('Compute restricted parameters', phi)
                I_s = singular('%s(%s(%s))'%(gb_command,phi_s.name(),Par_s.name()), type='ideal')
                if singular.eval('%s(%s)'%('dim' if ch==2 else 'GKdim', I_s.name()))!='0':
                    restrictions.append((cod_s, phi_s, I_s))
            return restrictions
        except KeyboardInterrupt:
            self.reconstruct_singular()
            return None
        finally:
            singular.eval('degBound=%s'%dgb)
            try:
                br.set_ring()
            except:
                pass

    @permanent_result
    def _get_obvious_parameter(self, Par, deg):
        """
        Use a non-enumerative heuristic to find a "last parameter" in a given degree.

        INPUT:

        - ``Par``, a frozenset of strings determining elements of this ring approximation
          that define an ideal of Krull dimension 1 in the cohomology ring.
        - ``deg``, an integer

        OUTPUT:

        Either a string determining an element of degree ``deg`` in the
        current ring approximation that generates an ideal of Krull dimension
        0 in the cohomology ring together with ``Par``, or a list of string
        determining elements of degree ``deg`` such that an enumeration over
        the linear combinations may yield an element that generates an ideal
        of Krull dimension 0 in the cohomology ring together with ``Par``.

        If it can be shown that such element does not exist in degree ``deg``,
        ``None`` is returned. A ``ValueError`` is raised if it can be shown
        that such element does not exist in any degree.

        THEORY:

        Whether a list of elements of the ring approximation yields an ideal
        of Krull dimension 0 in the complete cohomology ring can be read off
        of the restrictions to the maximal `p`\--elementary abelian subgroups.
        We determine the restrictions of degree\--``deg`` standard monomials
        and compute their normal form with respect to the radical of the
        restrictions of ``Par``. After some preprocessing involving Gauss
        elimination, we obtain a set of linear combinations of standard
        monomials. In this set, we try to find a subset, such that for each
        maximal `p`\--elementary abelian subgroup there is an element of the
        subset that restricts to a parameter, and the restrictions of all
        other elements are contained in the radical of the restrictions of
        ``Par``. It is then straight forward that the sum of the linear
        combinations in the subset yields a parameter.

        EXAMPLES:

        We use an example of order 64, that is thus contained in our database::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,201)
            sage: H._get_obvious_parameter(frozenset(['c_2_8', 'c_4_21']), 2)
            'b_1_2^2+b_1_1*b_1_2+b_1_1^2'
            sage: H.set_ring()
            sage: (H.relation_ideal()+singular.ideal(['c_2_8', 'c_4_21', 'b_1_2^2+b_1_1*b_1_2+b_1_1^2'])).std().dim()
            0

        Here, a last parameter can only be found in degree 2, but not in degree 1::

            sage: H._get_obvious_parameter(frozenset(['b_1_1 + b_1_2 + b_1_3', 'c_4_21']), 1)
            sage: H._get_obvious_parameter(frozenset(['b_1_1 + b_1_2 + b_1_3', 'c_4_21']), 2)
            'c_2_8'

        Here, there does not exist a single element (in any degree) that would
        generate an ideal of Krull dimension zero together with the given list
        of elements::

            sage: H._get_obvious_parameter(frozenset(['b_1_1', 'c_4_21']), 2)
            Traceback (most recent call last):
            ...
            ValueError: The input can not be extended to a hsop

        """
        # Par: String representation of some elements that will
        # define a 1-dimensional ideal
        # deg: Degree in which a last parameter is attempted to be found,
        # which is a sum of elements that are nilpotent modulo Par on all
        # maximal elementary abelian subgroups on which they do not restrict
        # to a parameter
        from sage.all import matrix

        ch = self._prime or self.resolution().coef()
        singular = self.GenS.parent()
        restrictions = []
        par_res = self._parameter_restrictions(Par,radical=ch==2)
        if not par_res:
            raise ValueError("Par=%s does not need to be extended"%repr(Par))
        try:
            par_res[0][0]._check_valid()
        except ValueError:
            par_res = self._parameter_restrictions(Par,radical=ch==2, forced=True)
        for cod_s,phi_s,IR_s in par_res:
            cod_s.set_ring()
            if int(singular.eval('%s(%s)'%('dim' if ch==2 else 'GKdim', IR_s.name())))>1:
                raise ValueError("The input can not be extended to a hsop")
            restrictions.append((cod_s,phi_s,IR_s, IR_s.kbase(deg)))
        if not restrictions:
            raise ValueError("Par=%s does not need to be extended"%repr(Par))
        S = self.standard_monomials(deg)
        self_s = singular(self)
        self_s.set_ring()
        tmp_poly = singular.poly(0)
        K = self.base()

        def get_restriction_coeffs(p):
            L = []
            self_s.set_ring()
            singular.eval('%s=%s'%(tmp_poly.name(),p))
            for cod_s, phi_s, G_res, KB in restrictions:
                cod_s.set_ring()
                tmp = singular('NF(%s(%s),%s)'%(phi_s.name(),tmp_poly.name(),G_res.name()))
                for k in range(1,int(singular.eval('size(%s)'%KB.name()))+1):
                    L.append(K(singular.eval('%s/%s[%d]'%(tmp.name(),KB.name(),k))))
            return L

        def get_matrix(S):
            L = []
            l = len(S)
            for i,s in enumerate(S):
                L.append(get_restriction_coeffs(s)+[0]*i+[1]+[0]*(l-i-1))
            M = matrix(L)
            return M

        def analyse_candidate(p):
            L = []
            for cod_s, phi_s, G_res, KB in restrictions:
                cod_s.set_ring()
                if singular.eval('NF(%s(%s),%s)==0'%(phi_s.name(),p.name(),G_res.name()))=='0':
                    L.append(1)
                else:
                    L.append(0)
            self_s.set_ring()
            return L

        def candidate_param(p):
            L = []
            for cod_s, phi_s, G_res, KB in restrictions:
                cod_s.set_ring()
                if singular.eval('dim(std(%s+ideal(%s(%s))))'%(G_res.name(),phi_s.name(),p.name()))=='0':
                    L.append(1)
                else:
                    L.append(0)
            self_s.set_ring()
            return L

        def get_parameter_basis(S):
            L = []
            l = len(S)
            M = get_matrix(S)
            lm = M.ncols()-l
            M.echelonize()
            Pivs = list(M.pivots())
            for i,piv in enumerate(Pivs):
                if piv<lm:
                    L.append(M[i].list()[lm:])
            self_s.set_ring()
            return [singular('+'.join(['{}*{}'.format(K(k),s) for k,s in zip(cl,S) if k])) for cl in L]

        def list2sparse(L):
            M = []
            for i,x in enumerate(L):
                if x:
                    M.append(i+1)
            return M
        ###############
        # Try to find parameters via an exact cover
        from sage.combinat.dlx import DLXMatrix
        P = get_parameter_basis(S)
        if not P:
            return None
        DLXM = DLXMatrix([[i+1, list2sparse(candidate_param(p)+analyse_candidate(p))] for i,p in enumerate(P)])
        out = list(DLXM)
        self_s.set_ring()
        if not out:
            # Now it might make sense to try enumeration on P
            return [repr(p) for p in P]
        param = sum([P[i-1] for i in out[0]])
        self.set_ring()
        return singular.eval('imap(%s,%s)'%(self_s.name(),param.name()))

    @permanent_result
    def find_small_last_parameter(self,Par, maxdeg=None):
        r"""
        Find an element of smallest degree that can replace the last element of a given HSOP.

        INPUT:

        - ``Par``: a list of parameters for the cohomology ring living in the
          current ring approximation, given by strings. The last entry may be
          ``None``.
        - ``maxdeg``: the maximal degree (int) in which a parameter will be sought.
          Default: The minimum of the degree of the current ring approximation and
          the degree of ``P[-1]`` (if not None) minus one.

        OUTPUT:

        Either a string defining a parameter in degree at most ``maxdeg``, or
        ``P[-1]`` if such parameter does not exist.  A value error is raised,
        if ``Par[:-1]`` can not be extended to a HSOP of the cohomology ring.

        THEORY:

        A set `P` of elements of the ring approximation provides parameters
        for the cohomology ring if and only if the cohomology rings of all
        maximal elementary abelian subgroups are finite over the restrictions
        of `P`. If the ring approximation is lacking relations in higher degrees,
        then `P` is not necessarily a hsop for the approximation as well.

        We obtain `P'` from `P` by replacing the last parameter with a
        parameter of smallest degree, that is obtained by enumeration of
        elements in small degrees.

        If `P` is filter regular then so is `P'`, which is proved in [GreenKing]_.

        NOTE:

        In each degree, a default of at most 512 candidates are tested; this
        default can be altered by assigning a value to
        ``pGroupCohomology.resolution.coho_options['NrCandidates']``. The
        reason for setting the default to such a small number is that
        both in the modified Benson criterion and in the
        Hilbert-Poincaré criterion we can do with an existence proof
        for parameters. So, it is normally not crucial to have a very
        small last parameter (though it may simplify the test for
        filter regularity).


        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make(1)
            sage: print(H)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 1
            Minimal list of generators:
            [b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            []

        Hence, the ring approximation has a hsop formed by the two
        generators. But the method realises that this would not yield
        parameters for the cohomology and consequently raises an error::

            sage: H.find_small_last_parameter(['b_1_0', None])
            Traceback (most recent call last):
            ...
            ValueError: The input can not be extended to a hsop

        Later it will turn out that the sum of the degree one generators,
        together with a generator in degree two, forms a homogeneous system of
        parameters. The program can verify it by restriction to maximal
        elementary abelian subgroups, and so the error vanishes. But we only
        know the ring out to degree one, and so we still don't find a second
        parameter::

            sage: P = ['b_1_0 + b_1_1', None]
            sage: print(H.find_small_last_parameter(P))
            None

        Computing one degree further, we have success::

            sage: H.next()
            sage: CohomologyRing.global_options('info')
            sage: P[-1] = H.find_small_last_parameter(P); P[-1]
            H^*(D8; GF(2)):
                Compute find_small_last_parameter
                Computing complete Groebner basis
                Compute _parameter_restrictions
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                Compute restricted parameters
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                Compute restricted parameters
            H^*(D8; GF(2)):
                Compute _get_obvious_parameter
                Compute _parameter_restrictions
                compute radicals of restricted parameter ideal
                Compute _parameter_restrictions
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                Compute restricted parameters
            Induced homomorphism of degree 0 from H^*(D8; GF(2)) to H^*(SmallGroup(4,2); GF(2)):
                Compute restricted parameters
            H^*(D8; GF(2)):
                Determine degree 1 standard monomials
                Compute _get_obvious_parameter
                Determine degree 2 standard monomials
                --> Last parameter found in degree 2
            'c_2_2'

        Let us verify that the two elements form a filter regular hsop::

            sage: H.raw_filter_degree_type(P)
                Compute raw_filter_degree_type
                Test filter regularity
                  Filter degree type: [-1, -2, -2]
            ([-1, -1, 1], [[0], [0], [1, 1]], [1, 2])
            sage: CohomologyRing.global_options('warn')

        """
        # sort out some trivial cases
        # Do we want to attempt to improve a Duflot regular sequence?
        # It won't make sense, because we constructed it in a minimal way.
        if len(self.duflot_regular_sequence())==self.dimension() and Par==self.duflot_regular_sequence():
            return Par[-1]
        if Par[:-1].count(None):
            return Par[-1]

        # Adjust maxdeg
        singular = self.GenS.parent()

        try:
            br = singular('basering')
        except TypeError:
            br = None
        self_s = singular(self)
        self.set_ring()
        if Par[-1] is not None:
            implicit_maxdeg = int(singular.eval('deg(%s)'%Par[-1]))
        else:
            implicit_maxdeg = self.knownDeg+1
        if maxdeg is None:
            maxdeg = min(implicit_maxdeg - 1, self.knownDeg)
        else:
            maxdeg = min(implicit_maxdeg - 1, self.knownDeg, maxdeg)
        if maxdeg<=0:
            # this can only happen for invalid input
            return Par[-1]

        # We use a cache
        cache = self._param_cache
        if cache is None:
            self.setprop('_param_cache',{})
            cache = self._param_cache
        ParamSet = frozenset(Par[:-1])

        if (ParamSet,-1) in cache:
            raise ValueError("The input can not be extended to a hsop")

        cdef int j,k, lenL
        # Some computational options
        p = self._prime or self.resolution().coef()
        cdef list L
        cdef tuple C
        from sage.all import cartesian_product_iterator
        interruption = False
        cdef int BreakPoint = coho_options['NrCandidates']
        gb_command = self._gb_command()

        # restrict Par[:-1] to the maximal elementary abelian subgroups
        cdef list restrictions
        cdef int curr_deg
        try:
            dgb = singular.eval('degBound')
            singular.eval('degBound=0')
            # not the radical, but that won't hurt anyway...:
            restrictions = self._parameter_restrictions(ParamSet)
            if not restrictions:
                # Par[:-1] already is a set of parameters
                return None
            for cod_s,phi_s,I_s in restrictions:
                cod_s.set_ring()
                if Integer(singular.eval('%s(%s)'%('dim' if p==2 else 'GKdim', I_s.name()))) > 1:
                    raise ValueError("The input can not be extended to a hsop")

            # Will the cohomology eventually be finite over a given ideal I in self_s
            def test_dim0(I):
                try:
                    for cod_s, phi_s, I_s in restrictions:
                        cod_s.set_ring()
                        if int(singular.eval('vdim(std(%s,%s(%s)))'%(I_s.name(),
                                                                    phi_s.name(),
                                                                    I.name()))) == -1:
                            return False
                    return True
                finally:
                    self_s.set_ring()

            # Is the given polynomial a parameter?
            def test_dim0_std(p):
                try:
                    for cod_s, phi_s, I_s in restrictions:
                        cod_s.set_ring()
                        if int(singular.eval('vdim(std(%s,%s(%s)))'%(I_s.name(),
                                                                     phi_s.name(),
                                                                     p.name()))) == -1:
                            return False
                    return True
                finally:
                    self_s.set_ring()


            # Test if the polynomial polynomial p is nilpotent, i.e., its restrictions are zero.
            def test_nilpotent(p):
                try:
                    for cod_s, phi_s, I_s in restrictions:
                        cod_s.set_ring()
                        if singular.eval('NF(%s(%s),std(0))==0'%(phi_s.name(), p.name()))=='0':
                            return False
                    return True
                finally:
                    self_s.set_ring()

            for curr_deg from 1<=curr_deg<=maxdeg:
                saved_val = cache.get((ParamSet,curr_deg))
                if saved_val is not None:
                    return saved_val

                obvious = self._get_obvious_parameter(ParamSet,curr_deg)
                if isinstance(obvious, basestring):
                    coho_logger.info("--> Last parameter found in degree %d", self, curr_deg)
                    cache[ParamSet,curr_deg] = obvious
                    return cache[ParamSet,curr_deg]
                elif obvious is None:
                    continue

                # Now it makes sense to start the real work
                coho_logger.info( "Trying to find a small last parameter in degree %d by enumeration", self, curr_deg)

                self_s.set_ring()

                L = obvious  # They are pre-processed linear combinations of standard monomials
                Poly_tmp = singular.poly(0)

                lenL = len(L)
                if lenL==0:
                    coho_logger.info("--> no relevant standard monomials in degree %d", self, curr_deg)
                    continue
                if lenL<50:
                    S = singular.ideal(L)
                else:
                    S = singular.ideal(0)
                    S[lenL]=0
                    for j from 0<=j<lenL:
                        S[j+1] = L[j]
                counter = 0

                # S contains all standard monomials of self of degree maxdeg.
                # Is there a chance that the restrictions yield parameters?
                if not test_dim0(S):
                    coho_logger.info('--> no last parameter in degree %d', self, curr_deg)
                    continue

                Help = singular.ideal(0)
                singular.eval('%s[size(%s)]=0'%(Help.name(),S.name()))
                # S might be by far too long. So, try to eliminate
                # some of its elements.
                for j from 1 <=j <=lenL:
                    singular.eval('%s=%s[%d]'%(Poly_tmp.name(),S.name(),j))
                    singular.eval('%s[%d]=0'%(S.name(),j))
                    if not test_dim0(S):
                        # restore the old value
                        singular.eval('%s[%d]=%s'%(S.name(),j,Poly_tmp.name()))
                    else:
                        # the old value may be helpful, but likely we can do without it
                        singular.eval('%s[%d]=%s'%(Help.name(),j,Poly_tmp.name()))

                # Perhaps S is shorter now
                singular.eval('%s=simplify(%s,2)'%(S.name(),S.name()))
                singular.eval('%s=simplify(%s,2)'%(Help.name(),Help.name()))
                lenL = int(singular.eval('size(%s)'%S.name()))
                lenHelp = int(singular.eval('size(%s)'%Help.name()))
                if lenL == 0:
                    # This can occur, e.g., if all standard monomials are nilpotent
                    coho_logger.info('--> no last parameter in degree %d', self, curr_deg)
                    continue
                coho_logger.debug('    %d = (%d-1)^%d*%d^%d candidates in degree %d', self, (p-1)**lenL*p**lenHelp,p,lenL,p,lenHelp,curr_deg)
                if BreakPoint < (p-1)**lenL*p**lenHelp:
                    coho_logger.debug('    Will break after %d candidates',self, BreakPoint)
                for C in cartesian_product_iterator([range(1,p)]*lenL):
                    v = singular.intmat(singular.intvec(*C),lenL,1)
                    vp = S*v
                    for D in cartesian_product_iterator([range(p)]*lenHelp):
                        if counter >= BreakPoint:
                            coho_logger.debug('No parameter among the %d considered candidates',self, BreakPoint)
                            return Par[-1]
                        if lenHelp:
                            w =  singular.intmat(singular.intvec(*D),lenHelp,1)
                            wp = Help*w
                        else:
                            wp = singular.matrix(1,1)
                        counter +=1
                        singular.eval('%s=%s[1][1]+%s[1][1]'%(Poly_tmp.name(),vp.name(),wp.name()))
                        if test_dim0_std(Poly_tmp):
                            coho_logger.info("--> Last parameter found in degree %d", self, curr_deg)
                            cache[ParamSet,curr_deg] = singular.eval(Poly_tmp.name())
                            return cache[ParamSet,curr_deg]

            coho_logger.info('The given last parameter could not be improved', self)
            return Par[-1]
        except KeyboardInterrupt:
            coho_logger.warning("You interrupted the attempt to improve the last parameter", self)
            try:
                self.GenS._check_valid()
            except ValueError:
                self.reconstruct_singular()
            return Par[-1]
        except:
            try:
                self.GenS._check_valid()
            except ValueError:
                self.reconstruct_singular()
            raise
        finally:
            if br is not None:
                try:
                    br.set_ring()
                except:
                    pass
            singular.eval('degBound='+dgb)

    @permanent_result
    def parameters(self,**kwds):
        """
        Return small parameters that are algebraically independent.

        OUTPUT:

        ``None``, if the ring approximation does not contain parameters for the
        cohomology ring. Otherwise, a sequence of elements, forming a hsop of
        the cohomology ring, but not necessarily of the ring approximation.

        THEORY:

        We start with a filter-regular hsop, as provided by
        :meth:`filter_regular_parameters`. Then, we try to replace
        any of these parameters by a parameter of smaller degree. The
        result is not guaranteed to be filter regular, of course.

        NOTE:

        Compared with previous versions of this spkg, the heuristics to find
        parameters in smaller degrees has substantially improved in version
        2.1.4.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: G = libgap.AlternatingGroup(8)
            sage: H = CohomologyRing(G,prime=2,GroupName='A8', from_scratch=True)
            sage: H.make(7)

        In this example, it was not automatically attempted to lift Dickson
        elements. Since the Dickson elements are the starting point of
        parameter construction in this case, we do not find parameters, even
        though they do exist::

            sage: H.parameters()
            sage: H.verify_parameters_exist()
            True

        We now use elimination to find paramters::

            sage: H.find_dickson()
            True

        The result of :meth:`parameters` is cached as long as the ring structure
        doesn't change. Here, the ring structure *has* changed since the previous
        call to the method, and indeed we can now find parameters::

            sage: H.parameters()
            ['b_2_0^2+c_4_1',
             'b_3_1^4+b_3_0^4+b_6_2*b_3_1^2+b_6_2^2+b_2_0^3*b_6_2+c_4_1*b_3_1*b_5_2+b_2_0*c_4_1*b_3_1^2+b_2_0^2*c_4_1^2',
             'b_7_6+c_4_1*b_3_1+c_4_1*b_3_0',
             'b_6_2']

        These elements are guaranteed to form a homogeneous system of
        parameters of the cohomology ring, but they are not parameters of the
        current ring approximation::

            sage: I = H.relation_ideal()
            sage: singular.eval('degBound = 0')
            ''
            sage: print(singular.eval('dim(groebner(%s+ideal(%s)))'%(I.name(), ','.join(H.parameters()))))
            4

        Continuing to degree 14, thus, having more relations, the above
        parameters do indeed turn into parameters for the ring approximation::

            sage: H.make(14)
            sage: I = H.relation_ideal()
            sage: print(singular.eval('dim(groebner(%s+ideal(%s)))'%(I.name(), ','.join(H.parameters()))))
            0

        """
        from pGroupCohomology.modular_cohomology import MODCOHO
        coho_logger.info("Try to find small parameters", self)
        if isinstance(self,MODCOHO):
            P = self.parameters_from_sylow_subgroup()
            if P is not None:
                if P.count(None) == 1:
                    P.append(P.pop(P.index(None)))
                    P[-1] = self.find_small_last_parameter(P,self.knownDeg)
                if P.count(None):
                    P = self.filter_regular_parameters()
            else:
                P = self.filter_regular_parameters()
        else:
            P = self.filter_regular_parameters()
        if not P:
            return
        if not self.MaxelPos:
            return P
        for i in range(len(P)):
            P.append(P.pop(0))
            P[-1] = self.find_small_last_parameter(P,self.knownDeg)
        return P

    def _factorise(self,C):
        """
        Return a factor of ``C`` of small degree, possibly after a nilpotent
        modification, but disregarding relations.

        INPUT:

        A cochain ``C``. ``C.name()`` should express ``C`` as
        polynomial in the generators of ``self``.

        NOTE:

        In order to express ``C`` as a polynomial in the generators of
        ``self``, use :meth:`element_as_polynomial`.

        OUTPUT:

        A string, providing the smallest found non-scalar factor of
        ``C``, potentially after modifying ``C`` by an element of the
        nil-radical.

        NOTE:

        If the method does not succeed to find a factor, it does not
        mean that ``C`` can't be factorised at all. This method is
        just a heuristics, that may be useful to simplify some
        computations.

        If relations in the ring should be taken into account, use
        :meth:`small_factor`.

        The computation can be interrupted with Ctrl-c; in this case,
        a string description of ``C`` modulo nilpotent generators is
        returned. However, due to some bug in the underlying
        factorisation software, interruption might yield to a crash of
        Sage.

        EXAMPLES::

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

        We construct a cochain and find a non-trivial factor, although it is not obvious
        from the definition that a factorisation modulo nilpotent classes exists::

            sage: c = H('-b_2_2^2+b_2_1*b_2_3-b_2_2^2-b_2_1^2+b_2_0*b_2_1')
            sage: H._factorise(c)
            'b_2_2-b_2_1'

        We verify that indeed the difference of ``c`` and some multiple
        of the returned factor is nilpotent (but not zero)::

            sage: H('b_2_2 - b_2_1')*H('-b_2_1') == c
            False
            sage: print((H('b_2_2 - b_2_1')*H('-b_2_1')-c)^2)
            8-Cocycle in H^*(E27; GF(3)),
            represented by
            [0 0 0 0 0 0 0 0 0 0 0 0]

        """
        if C is None:
            return None
        cdef RESL Resl = self.Resl
        R = PolynomialRing(GF(Resl.G_Alg.Data.p),[X.name() for X in self.Gen])
        cdef list L
        from pGroupCohomology.cochain import MODCOCH
        br = None
        try:
            if isinstance(C,COCH) or isinstance(C,MODCOCH) or repr(C.parent()) == 'Singular':
                if repr(C.parent()) == 'Singular':
                    s = C.parent().eval(C)
                else:
                    s = C.name()
                ## try to simplify, by killing nilpotent generators
                dgb = singular.eval("degBound")
                singular.eval("degBound = %d"%(C.deg()))
                coho_logger.debug("Simplification modulo nilpotent generators", self)
                L = [X.name() for X in self.Gen if X.ydeg()]
                try:
                    br = singular('basering')
                except TypeError:
                    pass
                self.set_ring()
                if L:
                    I = (singular("%sI"%(self.prefix))+singular.ideal(L)).groebner()
                    s = str(singular("NF(%s,%s)"%(s,I.name())))
                else:
                    s = str(singular("NF(%s,%sI)"%(s,self.prefix)))
            else:
                raise TypeError("Cochain expected")
            singular.eval('degBound = '+dgb)
            if s=='0':
                return '0'
            F=[(R(s),1)]
            coho_logger.info("Factorising an element; it can be interrupted with Ctrl-c", self)
            stopped = False
            try:
                F=F[0][0].factor(proof=False)
            except:
                coho_logger.warning("You interrupted the factorisation of a cochain (don't worry...)", self)
                stopped = True
            mindeg = min([Integer(singular.eval("deg(%s)"%(str(Nr[0])))) for Nr in F])
            for Nr in F:
                if (Integer(singular.eval("deg(%s)"%(str(Nr[0]))))==mindeg):
                    OUT_STR = singular.eval('normalize(%s)'%str(Nr[0]))
                    if stopped:
                        return [OUT_STR]
                    return OUT_STR
        finally:
            try:
                br.set_ring()
            except:
                pass

    def small_factor(self,C, enumerate=False):
        """
        Determine a small factor of an element, modulo nilpotent generators.

        INPUT:

        - ``C`` -- an element of ``self`` or a polynomial in the
          Singular interface. If it is an element of ``self``,
          ``C.name()`` must express ``C`` as polynomial in the
          generators of ``self``.
        - ``enumerate`` -- (bool, default ``False``) If ``True``,
          the factorisation takes into account the relations in
          ``self``, but may take a long time, as the factors are
          found by enumeration of elements in small degrees.

        NOTE:

        In order to express ``C`` as a polynomial in the generators of
        ``self``, use :meth:`element_as_polynomial`.

        OUTPUT:

        A string, providing a small non-scalar factor of ``C``,
        allowing modification by multiples of nilpotent generators.

        NOTE:

        If the optional argument ``enumerate`` is ``True``, then in
        each degree, at most 1000 candidates are tested; this default
        can be altered by assigning a value to
        ``pGroupCohomology.resolution.coho_options['NrCandidates']``.

        NOTE:

        If the computation is interrupted with Ctrl-c, the computation
        is continued in the next degree.

        EXAMPLES:

        We first load a cohomology ring of order 64 from the local sources
        shipped with this package.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: H = CohomologyRing(64,235)
            sage: H.gens()
            [1,
             c_4_13: 4-Cocycle in H^*(SmallGroup(64,235); GF(2)),
             c_4_14: 4-Cocycle in H^*(SmallGroup(64,235); GF(2)),
             a_1_1: 1-Cocycle in H^*(SmallGroup(64,235); GF(2)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(64,235); GF(2)),
             b_1_2: 1-Cocycle in H^*(SmallGroup(64,235); GF(2)),
             b_1_3: 1-Cocycle in H^*(SmallGroup(64,235); GF(2)),
             b_3_10: 3-Cocycle in H^*(SmallGroup(64,235); GF(2))]

        We construct a cochain of degree 6. A factorisation with the
        default arguments does not yield a factor of smaller degree;
        only the obvious nilpotent summand is removed::

            sage: p = H('b_1_3^3*b_3_10+c_4_14*b_1_3^2+c_4_14*b_1_2^2+c_4_13*b_1_3^2+c_4_13*b_1_2^2+c_4_13*a_1_0*a_1_1')
            sage: H.small_factor(p)
            'b_1_3^3*b_3_10+c_4_14*b_1_3^2+c_4_14*b_1_2^2+c_4_13*b_1_3^2+c_4_13*b_1_2^2'

        However, a smaller factor can be found if, in addition to nilpotent generators,
        the relations are taken into account, by using an optional argument::

            sage: CohomologyRing.global_options('info')
            sage: H.small_factor(p, enumerate=True)
            H^*(SmallGroup(64,235); GF(2)):
                Factorising an element; it can be interrupted with Ctrl-c
                Exploring factors of an element by enumeration (can be interrupted with Ctrl-c)
                Determine degree 1 standard monomials
                > Start enumeration with 2 monomials
            'b_1_3+b_1_2'

        We verify that indeed the difference of ``p`` and some multiple of the
        returned factor is nilpotent of order exactly 3::

            sage: CohomologyRing.global_options('warn')
            sage: f1 = H('b_1_3+b_1_2')
            sage: f2 = H('(b_1_3*b_3_10+c_4_14+c_4_13)*(b_1_3+b_1_2)')
            sage: ((singular(f1)*singular(f2) - singular(p))^2).NF('std(0)')
            c_4_14*a_1_1*a_1_0*b_1_2^6+c_4_13*a_1_1*a_1_0*b_1_2^6
            sage: ((singular(f1)*singular(f2) - singular(p))^3).NF('std(0)')
            0

        """
        if C is None:
            return None
        p = self._prime or self.resolution().coef()
        cdef list L,Lshort
        cdef int i, j, mdeg
        from pGroupCohomology.cochain import MODCOCH
        try:
            br = singular('basering')
        except TypeError:
            br = None
        if repr(C.parent()) == 'Singular' or isinstance(C,COCH) or isinstance(C,MODCOCH):
            s = self._factorise(C)
            stopped = False
            if isinstance(s,list):
                s = s[0]
                stopped = True
            if not (stopped or enumerate):
                return s
            self.set_ring()
            poly = singular.poly(s)
        else:
            raise TypeError("Cochain expected")

        cdef int BreakPoint = coho_options['NrCandidates']
        self.set_ring()
        mdeg = min(int(int(singular.eval('deg(%s)'%s))/2),self.knownDeg)
        self.make_groebner(mdeg)
        ## try to simplify, by killing nilpotent generators
        dgb = singular.eval('degBound')
        singular.eval('degBound=%d'%mdeg)
        gb_command = self._gb_command()

        if s!='0':
            try:
                coho_logger.info("Exploring factors of an element by enumeration (can be interrupted with Ctrl-c)", self)
                from sage.all import cartesian_product_iterator
                self.set_ring()
                I = singular(self.prefix+'I')
                if [X.name() for X in self.Gen if X.ydeg()]:
                    # std(...,...) was buggy at some point.
                    singular.eval('%s=std(%s,ideal(%s))'%(I.name(), I.name(), ','.join([X.name() for X in self.Gen if X.ydeg()])))
                for i from 1<=i<=mdeg:
                    L = [t for t in self.standard_monomials(i) if singular('%s/%s!=0'%(poly.name(),t))]
                    lenL = len(L)
                    if lenL==0:
                        continue
                    if lenL<50:
                        S = singular.ideal(L)
                    else:
                        S = singular.ideal(0)
                        S[lenL]=0
                        for j from 0<=j<lenL:
                            S[j+1] = L[j]
                    counter = 0
                    if singular('NF(NF(%s,%s),%s)==0'%(poly.name(),S.name(),I.name())):
                        coho_logger.info("> Start enumeration with %d monomials",self,lenL)
                        for j from lenL>j>=0:
                            # L is sorted in descending order. If L[j] is the leading
                            # monomial of a factor, then it must divide the leading monomial
                            # of ``poly``, and it can be of coefficient one.
                            if singular.eval('leadmonom(%s)/%s!=0'%(poly.name(),L[j]))=='1':
                                if singular('NF(NF(%s,ideal(%s[%d..ncols(%s)])),%s)==0'%(poly.name(),S.name(),j+1,S.name(),I.name())):
                                    coho_logger.debug("> > %d potential factors in degree %d",self, p**(lenL-j),i)
                                    if BreakPoint-counter < p**(lenL-j):
                                        coho_logger.debug("> > Will break after %d candidates", self, BreakPoint-counter)
                                    for Cand in cartesian_product_iterator([[0]]*(j)+[[1]]+[range(p)]*(lenL-j-1)):
                                        v = singular.intmat(singular.intvec(*Cand),lenL,1)
                                        vp = S*v
                                        counter +=1
                                        if counter >=BreakPoint:
                                            break
                                        if singular('NF(NF(%s,%s[1][1]),NF(%s,std(%s[1][1])))==0'%(poly.name(),vp.name(),I.name(),vp.name())):
                                            out = singular.eval(vp.name()+'[1][1]')
                                            if br is not None:
                                                br.set_ring()
                                            singular.eval('degBound='+dgb)
                                            return out
            except (TypeError,KeyboardInterrupt):
                coho_logger.warning("> Factorisation of an element interrupted", self)
                self.set_ring()
        if repr(C.parent()) == 'Singular':
            s = singular.eval(s)
        if br is not None:
            try:
                br.set_ring()
            except:
                pass
        singular.eval('degBound='+dgb)
        return s

    @permanent_result
    def dependent_parameters(self):
        """
        Parameters for the cohomology that are not guaranteed to be algebraically independent.

        OUTPUT:

        A subset of ring generators of the current ring
        approximation over which the cohomology ring is finite.

        NOTE:

        There is no guarantee that they give rise to parameters for
        the current ring approximation. There is no guarantee that
        the returned elements are algebraically independent.

        Since elements of degree one do not contribute to the degree bound in
        Symonds' completeness criterion, we always include the degree one
        generators.

        This method is applied for the Symonds test (see
        :meth:`SymondsTest`).

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(32,32, from_scratch=True)
            sage: H.make(2)

        The current ring approximation does not contain parameters
        for the cohomology ring, and thus we obtain::

            sage: H.verify_parameters_exist()
            False
            sage: print(H.dependent_parameters())
            None

        In degree 4, at last we find that the cohomology ring
        is finite over the returned element list, so that it can
        eventually be used in a completeness test -- even though
        the ring approximation isn't finite over it, yet::

            sage: H.make(4)
            sage: H.verify_parameters_exist()
            True
            sage: H.dependent_parameters()
            ['a_1_0', 'a_1_1', 'a_1_2', 'c_4_4', 'c_4_5']
            sage: print(H)
            Cohomology ring of Small Group number 32 of order 32 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 4
            Minimal list of generators:
            [c_4_4: 4-Cocycle in H^*(SmallGroup(32,32); GF(2)),
             c_4_5: 4-Cocycle in H^*(SmallGroup(32,32); GF(2)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(32,32); GF(2)),
             a_1_1: 1-Cocycle in H^*(SmallGroup(32,32); GF(2)),
             a_1_2: 1-Cocycle in H^*(SmallGroup(32,32); GF(2)),
             a_3_2: 3-Cocycle in H^*(SmallGroup(32,32); GF(2)),
             a_3_3: 3-Cocycle in H^*(SmallGroup(32,32); GF(2))]
            Minimal list of algebraic relations:
            [a_1_1^2+a_1_0*a_1_2,
             a_1_2^2+a_1_0*a_1_1+a_1_0^2,
             a_1_0^3,
             a_1_0^2*a_1_2+a_1_0^2*a_1_1,
             a_1_2*a_3_2+a_1_1*a_3_2+a_1_0*a_3_3+a_1_0*a_3_2,
             a_1_2*a_3_3+a_1_1*a_3_3+a_1_0*a_3_2]

        """
        coho_logger.info("Try to find a set of generators over which the cohomology ring is finite.", self)

        cdef int curr_deg
        singular = self.GenS.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        self_s = singular(self)
        self_s.set_ring()
        try:
            P = [t.name() for t in sorted([x for x in self.Gen if (not x.ydeg()) and x.deg()>1])]
            Ess = [t.name() for t in self.Gen if t.deg()==1]

            p = self._prime or self.Resl.coef()
            # we need at least Singular version 3-1-1 in order
            # to use GKdim
            gb_command = self._gb_command()

            dgb = singular.eval('degBound')
            singular.eval('degBound=0')
            self_s.set_ring()
            I = singular.ideal(Ess+P)
            for pos in self.MaxelPos:
                phi = self.RestrMaps[pos][1]
                phi_s = singular(phi)
                singular(phi.codomain()).set_ring()
                if int(singular.eval('%s(%s(%s(%s)))'%('dim' if p==2 else 'GKdim',gb_command,phi_s.name(),I.name())))>0:
                    coho_logger.info("The cohomology ring is not finite over the current ring approximation", self)
                    return None
            while P:
                coho_logger.debug("> Considering %d elements", self, len(P)+len(Ess)-1)
                x = P.pop(-1)
                self_s.set_ring()
                singular.eval('%s=ideal(%s)'%(I.name(), ','.join(Ess+P)))
                for pos in self.MaxelPos:
                    phi = self.RestrMaps[pos][1]
                    phi_s = singular(phi)
                    singular(phi.codomain()).set_ring()
                    if int(singular.eval('%s(%s(%s(%s)))'%('dim' if p==2 else 'GKdim',gb_command,phi_s.name(),I.name())))>0:
                        Ess.append(x)
                        break
            return Ess
        except:
            self.reconstruct_singular()
            raise
        finally:
            if br is not None:
                try:
                    br.set_ring()
                except:
                    pass
            singular.eval('degBound='+dgb)

    def set_ring(self):
        """
        The underlying free graded commutative ring of ``self`` in the Singular interface becomes the base ring.

        NOTE:

        This ring is, in general, not isomorphic to the cohomology ring, since
        the non-obvious relations are disregarded; the ring will only have the
        *obvious* quadratic relations that are common to any graded commutative
        ring in the Singular interface.

        You can obtain a ring in the Singular interface isomorphic to a cohomology
        ring ``H`` by simply doing ``singular(H)``.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.subgroups()[4,2].set_ring()
            sage: print(singular.eval('basering'))
            // coefficients: ZZ/2
            // number of vars : 2
            //        block   1 : ordering M
            //                  : names    c_1_0 c_1_1
            //                  : weights      1     1
            //                  : weights     -1     0
            //        block   2 : ordering C
            sage: H.set_ring()
            sage: print(singular.eval('basering'))
            // coefficients: ZZ/2
            // number of vars : 3
            //        block   1 : ordering M
            //                  : names    c_2_2 b_1_0 b_1_1
            //                  : weights      2     1     1
            //                  : weights     -1     0     0
            //                  : weights      0    -1     0
            //        block   2 : ordering C

        """
        try:
            singular.eval('setring %sr(%d)'%(self.prefix,self.lastRelevantDeg or self.knownDeg))
            return
        except:
            self.reconstruct_singular()
            singular.eval('setring %sr(%d)'%(self.prefix,self.lastRelevantDeg or self.knownDeg))
            return

    def reconstruct_singular(self):
        """
        Reconstruct data after the Singular interface crashed.

        NOTE:

        We tried to make this method robust emough that computations
        involving Singular can be interrupted at any point.

        EXAMPLES:

        We start a cohomology computation and carry it out to degree 3.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(720,763,prime=2, from_scratch=True)
            sage: H.make(3)

        We now simulate a crash of Singular. After reconstructing the data,
        the computation can proceed as usual. By logging, we show what
        happens internally.
        ::

            sage: singular.quit()
            sage: CohomologyRing.global_options('info')
            sage: H.reconstruct_singular()
            H^*(SmallGroup(720,763); GF(2)):
                Reconstructing data in the Singular interface
            H^*(D8xC2; GF(2)):
                Reconstructing data in the Singular interface
            H^*(SmallGroup(8,5); GF(2)):
                Reconstructing data in the Singular interface
            H^*(SmallGroup(4,2); GF(2)):
                Reconstructing data in the Singular interface

        Even after the simulated crash, we can continue with the computation::

            sage: CohomologyRing.global_options('warn')
            sage: H.make(7)
            sage: H.find_dickson()
            True
            sage: H.parameters()
            ['c_1_0', 'c_2_1', 'b_3_3+c_3_2']
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

        Note that this method is automatically called when Singular is called
        on the cohomology ring::

            sage: CohomologyRing.global_options('info')
            sage: singular(H)
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
            sage: singular.quit()
            sage: singular(H)
            H^*(SmallGroup(720,763); GF(2)):
                Reconstructing data in the Singular interface
            H^*(D8xC2; GF(2)):
                Reconstructing data in the Singular interface
            H^*(SmallGroup(8,5); GF(2)):
                Reconstructing data in the Singular interface
            H^*(SmallGroup(4,2); GF(2)):
                Reconstructing data in the Singular interface
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

        TESTS:

        The following used to fail in at some point in the development of this package.
        ::

            sage: CohomologyRing.doctest_setup()        # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(48,50, prime=2)
            sage: H.make()
            sage: c = H.subgroup_cohomology()('c_1_1*c_1_2^2*c_1_3^3+c_1_1*c_1_2^4*c_1_3+c_1_1*c_1_2^5+c_1_1^2*c_1_3^4+c_1_1^2*c_1_2*c_1_3^3+c_1_1^2*c_1_2^3*c_1_3+c_1_1^3*c_1_2^2*c_1_3+c_1_1^3*c_1_2^3+c_1_1^4*c_1_3^2+c_1_1^4*c_1_2*c_1_3+c_1_1^4*c_1_2^2+c_1_1^5*c_1_2+c_1_0*c_1_3^5+c_1_0*c_1_2^2*c_1_3^3+c_1_0*c_1_2^3*c_1_3^2+c_1_0*c_1_1^2*c_1_2*c_1_3^2+c_1_0*c_1_1^2*c_1_2^2*c_1_3+c_1_0*c_1_1^2*c_1_2^3+c_1_0*c_1_1^3*c_1_3^2+c_1_0*c_1_1^3*c_1_2^2+c_1_0*c_1_1^4*c_1_3+c_1_0*c_1_1^5+c_1_0^2*c_1_3^4+c_1_0^2*c_1_2^2*c_1_3^2+c_1_0^2*c_1_2^3*c_1_3+c_1_0^2*c_1_2^4+c_1_0^2*c_1_1*c_1_3^3+c_1_0^2*c_1_1*c_1_2^2*c_1_3+c_1_0^2*c_1_1^2*c_1_2*c_1_3+c_1_0^2*c_1_1^2*c_1_2^2+c_1_0^2*c_1_1^3*c_1_2+c_1_0^3*c_1_2*c_1_3^2+c_1_0^3*c_1_1*c_1_2^2+c_1_0^3*c_1_1^2*c_1_3+c_1_0^3*c_1_1^3+c_1_0^4*c_1_3^2+c_1_0^4*c_1_2*c_1_3+c_1_0^4*c_1_2^2+c_1_0^4*c_1_1*c_1_2+c_1_0^4*c_1_1^2+c_1_0^5*c_1_3+c_1_0^5*c_1_1')
            sage: d = H.stable_to_polynomial(c); d
            c_3_6^2+c_3_2*c_3_7+c_3_2*c_3_6+c_3_0*c_3_7+c_3_0*c_3_6+c_3_0*c_3_5+c_3_0*c_3_4+c_3_0*c_3_3+c_2_3^3+c_2_2*c_2_3^2+c_2_1^2*c_2_3+c_2_1^3+c_2_0*c_2_3^2+c_2_0*c_2_1*c_2_2+c_2_0*c_2_1^2+c_2_0^2*c_2_3: 6-Cocycle in H^*(SmallGroup(48,50); GF(2))
            sage: R = H.find_relations(6)
            sage: [r.name() for r in R[0]]
            ['c_3_6*c_3_7+c_3_6^2+c_2_3^3', 'c_3_6^2+c_2_3^3',
             'c_3_4*c_3_7+c_3_4*c_3_6+c_2_1*c_2_3^2', 'c_3_4*c_3_7',
             'c_3_2*c_3_6+c_2_1^2*c_2_3', 'c_3_2*c_3_7',
             'c_3_0*c_3_7+c_3_0*c_3_6+c_2_1^2*c_2_2+c_2_1^3+c_2_0*c_2_2*c_2_3',
             'c_3_0*c_3_7', 'c_3_6^2', 'c_3_4*c_3_7+c_2_2*c_2_3^2',
             'c_3_4*c_3_6', 'c_3_2*c_3_6+c_2_1*c_2_2*c_2_3+c_2_0*c_2_3^2',
             'c_3_2*c_3_7+c_3_2*c_3_6+c_2_1*c_2_2*c_2_3+c_2_1^2*c_2_3',
             'c_3_2*c_3_7+c_2_1^2*c_2_3', 'c_2_1^3+c_2_0*c_2_2*c_2_3+c_2_0*c_2_1*c_2_3',
             'c_2_1^2*c_2_2+c_2_1^3+c_2_0*c_2_1*c_2_3', 'c_3_0*c_3_7+c_2_1^2*c_2_2',
             'c_3_0*c_3_6+c_2_1^2*c_2_2+c_2_0*c_2_2*c_2_3',
             'c_3_0*c_3_5+c_3_0*c_3_4+c_2_0*c_2_1^2', 'c_3_0*c_3_5+c_2_0*c_2_1^2+c_2_0^2*c_2_3',
             'c_3_0*c_3_4+c_2_0*c_2_1*c_2_2+c_2_0*c_2_1^2', 'c_3_0*c_3_5+c_3_0*c_3_4+c_2_0^2*c_2_3',
             'c_3_0*c_3_5+c_2_0*c_2_1*c_2_2+c_2_0^2*c_2_3', 'c_3_0*c_3_2+c_2_0^2*c_2_1',
             'c_3_0*c_3_3', 'c_3_0*c_3_2+c_2_0^2*c_2_2+c_2_0^2*c_2_1', 'c_3_0*c_3_3+c_2_0^2*c_2_1',
             'c_3_0*c_3_1+c_3_0^2+c_2_0^3', 'c_3_0^2+c_2_0^3', 'c_3_0^2']
            sage: singular.quit()
            sage: d == H.stable_to_polynomial(c) #indirect doc test
            H^*(SmallGroup(16,14); GF(2)):
                Reconstructing data in the Singular interface
            H^*(SmallGroup(48,50); GF(2)):
                Reconstructing data in the Singular interface
            True
            sage: R == H.find_relations(6)
            True

        """
        coho_logger.warning("Reconstructing data in the Singular interface", self)
        singular = self.GenS.parent()
        try:
            br = singular('basering')
        except TypeError:
            br = None
        p = self._prime or self.Resl.coef()
        n = self.lastRelevantDeg or self.knownDeg
        if p!=2:
            singular.LIB("ncall.lib")
        singular.LIB('general.lib')
        singular.LIB('poly.lib')
        singular.LIB('dickson.lib')
        from pGroupCohomology.cochain import MODCOCH
        if singular.eval('defined(i)')=='0':
            singular.eval('int i')
        else:
            if singular.eval('typeof(i)')!='int':
                raise RuntimeError("Singular has defined that i is not an integer - but we need i as integer!")
        if self.Gen:
            if self._property_dict.get('use_dp'):
                if len(self.degvec)==1:
                    singular.eval('ring tmp = %d,(%s),%s'%(p, ','.join([x.name() for x in self.Gen]), '(a(%d),dp)'%(self.degvec[0])))
                else:
                    singular.eval('ring tmp = %d,(%s),%s'%(p, ','.join([x.name() for x in self.Gen]), '(wp%s)'%(str(tuple(self.degvec)))))
            else:
                self._makeOrderMatrix_()
                singular.eval('ring tmp = %d,(%s),M(%sM)'%(p, ','.join([x.name() for x in self.Gen]), self.prefix))
            if p!=2:   # non-commutative case
                singular.eval('degBound = 0')
                singular.eval('def %sr(%d) = superCommutative(%d,%d)'%(self.prefix,n,self.firstOdd+1, len(self.Gen)))
            else:
                singular.eval('def %sr(%d) = tmp'%(self.prefix,n))
            singular.eval('setring %sr(%d)'%(self.prefix,n))
            singular.eval('kill tmp')
            self.GenS = singular('%sr(%d)'%(self.prefix,n))
            singular.eval('option(redSB,redTail,redThrough)')
            if self.completeGroebner: # we can use RelG
                singular.eval('ideal %sI = %s'%(self.prefix,','.join(self.RelG)))
            else:
                if self.Rel:
                    singular.eval('ideal %sI = %s'%(self.prefix,','.join(self.Rel)))
                    dgb = singular.eval('degBound')
                    singular.eval('degBound=%d'%self.knownDeg)
                    singular.eval('%sI=groebner(%sI)'%(self.prefix,self.prefix))
                    singular.eval('degBound='+dgb)
                else:
                    singular.eval('ideal %sI'%(self.prefix))
            singular.eval('ideal %sDG'%self.prefix)
        self.StdMon = {0:{'1':singular('1')}}
        from pGroupCohomology.modular_cohomology import MODCOHO
        if isinstance(self,MODCOHO):
            singular(self._HP).set_ring()
            for g in self.Gen:
                try:
                    g._Svalue = singular(g.val_str())
                except:
                    raise RuntimeError("Sorry, the value in Singular of some generator could not be reconstructed")
            for L in self.Triangular.values():
                for x in L:
                    x._reconstruct_singular_(singular)
            self._PtoPcapCPdirectSing = [singular(f) for f in self._PtoPcapCPdirect]
            self._PtoPcapCPtwistSing = [singular(f) for f in self._PtoPcapCPtwist]
        if br is not None:
            br.set_ring()


    def _singular_(self, S):
        """
        Create a representation of self as a quotient ring in the Singular interface.

        NOTE:

        The singular representation of ``self`` is cached until the
        ring structure changes.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: H.make(1)
            sage: R1 = singular(H); R1
            polynomial ring, over a field, global ordering
            // coefficients: ZZ/2
            // number of vars : 2
            //        block   1 : ordering M
            //                  : names    b_1_0 b_1_1
            //                  : weights      1     1
            //                  : weights     -1     0
            //        block   2 : ordering C
            sage: R1 is singular(H)
            True
            sage: H.make()
            sage: R2 = singular(H); R2          # indirect doctest
            polynomial ring, over a field, global ordering
            // coefficients: ZZ/2
            // number of vars : 3
            //        block   1 : ordering M
            //                  : names    c_2_2 b_1_0 b_1_1
            //                  : weights      2     1     1
            //                  : weights     -1     0     0
            //                  : weights      0    -1     0
            //        block   2 : ordering C
            // quotient ring from ideal ...
            sage: R1 is singular(H)
            False
            sage: R2 is singular(H)
            True

        """
        if not self.Gen:
            raise ValueError("We don't know any generator of %s yet"%repr(self))
        if not (S is self.GenS.parent()):
            raise TypeError("This singular session is not the one which is used in %s"%(repr(self)))
        if hasattr(self,'_SINGULAR_'):
            R,d = self._SINGULAR_
            if d == self.last_interesting_degree():
                try:
                    R._check_valid()
                    return R
                except ValueError:
                    pass
        self.set_ring()
        self.make_groebner()
        self._SINGULAR_ = [S('%sI'%self.prefix,'qring'), self.last_interesting_degree()]
        S.eval('option(redSB,redTail,redThrough)')
        return self._SINGULAR_[0]

    def make_groebner(self,d=0):
        """
        Compute a Groebner basis for the relation ideal.

        INPUT:

        ``d``: (optional) degree bound. Default: no degree bound

        NOTE:

        We keep track up to what degree a Groebner basis for the
        relation ideal is known. Hence, calling ``make_groebner()`` twice
        would only result in a re-computation if the relation ideal
        has changed in the meantime.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3, from_scratch=True)
            sage: H.make(3)
            sage: CohomologyRing.global_options('info')
            sage: len(H.RelG)
            5
            sage: H.make_groebner(5)
            H^*(E27; GF(3)):
                Computing Groebner basis up to degree 5
            sage: len(H.RelG)
            8
            sage: H.make_groebner()
                Computing complete Groebner basis

        Since the Groebner basis is already completely known,
        it is avoided to repeat the computation when we now
        request a Groebner basis out to degree at least 5,
        which can be seen by the absence of any log messages::

            sage: H.make_groebner(5)

        """
        if self.completeGroebner:
            return
        if d==0:
            coho_logger.info("Computing complete Groebner basis", self)
        else:
            coho_logger.info("Computing Groebner basis up to degree %d"%d, self)
        if self.useSlimgb:
            coho_logger.debug("> using slimgb", self)
        elif self.useStd:
            coho_logger.debug("> using std", self)
        dgb = singular.eval('degBound', self)
        singular.eval('degBound = %d'%(d))
        self.set_ring()
        if self.useSlimgb:
            singular.eval('%sI=slimgb(%sI)'%(self.prefix, self.prefix))
        elif self.useStd:
            singular.eval('%sI=std(%sI)'%(self.prefix, self.prefix))
        else:
            singular.eval('%sI=groebner(%sI)'%(self.prefix, self.prefix))
        singular.eval('degBound = '+dgb)
        self.RelG = [s.strip() for s in singular.eval('print(%sI)'%(self.prefix)).split(',')]
        if d==0:
            self.setprop('completeGroebner',True)
        else:
            self.setprop('completeGroebner',False)

#####################################################################
## Ring theoretic properties of the cohomology ring
#####################################################################

    def is_isomorphic(self, other):
        r"""
        Test whether two cohomology rings are isomorphic as graded rings.

        INPUT:

        - ``other``, a cohomology ring

        OUTPUT:

        - False, if self is not isomorphic to the given other cohomology ring.
        - None, if no conclusion on the isomorphy could be obtained.
        - A tuple of strings defining the generator images in an isomorphism
          from self to other.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H173 = CohomologyRing(64, 173)
            sage: H176 = CohomologyRing(64, 176)
            sage: H173.make()
            sage: H176.make()

        The rings are similar, but not identical::

            sage: H173.rels()
            ['a_1_1*b_1_0+a_1_1^2',
             'b_1_2^2+b_1_0*b_1_2',
             'a_1_1^3',
             'a_1_1*b_3_6',
             'b_3_6^2+b_1_0^3*b_3_6+c_4_9*b_1_0^2+c_4_9*a_1_1^2']
            sage: H176.rels()
            ['a_1_1*b_1_0+a_1_1^2',
             'b_1_2^2+b_1_0*b_1_2',
             'a_1_1^3',
             'a_1_1*b_3_6',
             'b_3_6^2+b_1_0^2*b_1_2*b_3_6+b_1_0^3*b_3_6+c_4_9*b_1_0^2+c_2_4*b_1_0^3*b_1_2+c_4_9*a_1_1^2']

        The existence of an isomorphism will be determined by an enumeration
        of all possible ways to map the generators of the first ring to elements
        of the second ring. This would of course be a huge number, but it can
        be cut down by various tests (for instance, the ideal generated by the
        generator images need to have the same Poincaré series than the ideal
        generated by the mapped generators, and in some cases it is also
        helpful to take the Poincaré series of annihilators of ideals into account).
        Often, there only remains a single possibility to map some of the generators
        in a way that could potentially extend to an isomorphism.

        In an attempt to keep the average computation time small, the number
        of possible assignments tested is cut off. If no conclusion can be made
        from these tests, then the cut-off is automatically adapted until a conclusion
        can be achieved::

            sage: H173.is_isomorphic(H176)              # long time
            ('1*c_2_4',
             '1*b_1_2*b_3_6+1*c_4_9+1*c_2_4*b_1_0*b_1_2',
             '1*a_1_1',
             '1*b_1_0',
             '1*b_1_2',
             '1*b_3_6')

        We now demonstrate that even fairly similar cohomology rings can be
        shown to be non-isomorphic. In the following example, the Poincaré series,
        the generator degrees and the degrees of minimal relations coincide.
        ::

            sage: H85 = CohomologyRing(64, 85)
            sage: H85.make()
            sage: H85.poincare_series() == H173.poincare_series()
            True
            sage: H85.degvec == H173.degvec
            True
            sage: H85.rels()
            ['a_1_0^2', 'a_1_1^2', 'a_1_0*b_1_2^2', 'a_1_0*a_3_6', 'a_3_6^2']
            sage: H173.rels()
            ['a_1_1*b_1_0+a_1_1^2',
             'b_1_2^2+b_1_0*b_1_2',
             'a_1_1^3',
             'a_1_1*b_3_6',
             'b_3_6^2+b_1_0^3*b_3_6+c_4_9*b_1_0^2+c_4_9*a_1_1^2']
            sage: CohomologyRing.global_options('info')
            sage: H85.is_isomorphic(H173)
            IsomorphismTest(H^*(SmallGroup(64,85); GF(2)), H^*(SmallGroup(64,173); GF(2))):
                Trying to find an isomorphism
            H^*(SmallGroup(64,85); GF(2)):
                Inserting SmallGroup(4,2) as a subgroup
                Inserting SmallGroup(8,5) as a subgroup
                Reconstructing subgroup data
            H^*(SmallGroup(64,173); GF(2)):
                Determine degree 1 standard monomials
            IsomorphismTest(H^*(SmallGroup(64,85); GF(2)), H^*(SmallGroup(64,173); GF(2))):
                gen(5) is rigid: b_1_2 --> 1*b_1_0
            H^*(SmallGroup(64,173); GF(2)):
                Determine degree 1 standard monomials
            IsomorphismTest(H^*(SmallGroup(64,85); GF(2)), H^*(SmallGroup(64,173); GF(2))):
                There cannot be a homomorphism, (gen(3)) cannot be mapped
                There cannot be a homomorphism, (gen(3)) cannot be mapped
                There cannot be a homomorphism, (gen(3)) cannot be mapped
                There cannot be a homomorphism, (gen(3)) cannot be mapped
                There is definitely no isomorphism
            False

        """
        if self == other:
            coho_logger.info("Ring presentations are identical")
            return tuple(x.name() for x in self.Gen)
        from pGroupCohomology.isomorphism_test import IsomorphismTest
        T = IsomorphismTest(self, other)
        Tinv = IsomorphismTest(other, self)
        while True:
            result = T.explore_isomorphisms()
            if result is not None:
                return result
            coho_logger.info("We achieved no conclusion on isomorphy.", self)
            coho_logger.info("Trying to find an inverse isomorphism instead.", self)
            result = Tinv.explore_isomorphisms()
            if result is None:
                T.cutoff *= 10
                Tinv.cutoff *= 10
                continue
            if result is False:
                return result
            Tinv._R_elim.set_ring()
            result = [singular.eval('NF(@%s,%s)'%(x.name(),Tinv.urbild_GB.name())) for x in Tinv._codomain.Gen]
            T.set_images(result)
            assert T.is_isomorphism(), "Inverting the isomorphism didn't work!"
            return result

    def dimension(self):
        """
        Return the dimension of ``self``.

        NOTE:

        It is known that the dimension of self equals the `p`-rank of the underlying group.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.dimension()
            2

        """
        if self.pRank:
            return self.pRank
        return Integer(self.group().RankPGroup())

    def _lower_bound_depth(self):
        """
        Returns a lower bound for the depth of a cohomology ring.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: CohomologyRing.set_local_sources(tmp_dir())

        For the cohomology ring of a group that is not of prime
        power order, the depth of the cohomology ring of the
        subgroup for which the stable element method is used
        provides a lower bound for the depth::

            sage: H = CohomologyRing(184,5, prime=2)
            sage: H._lower_bound_depth()
            2
            sage: H.subgroup_cohomology().depth()
            2

        For a prime power group, the rank of the center provides
        a lower bound for the depth, by a result of Duflot.
        ::

            sage: H = CohomologyRing(64,89)
            sage: H._lower_bound_depth()
            2
            sage: H.CenterRk
            2

        However, when completing the computation of this cohomology
        ring, the lower bound is replaced by the actual depth::

            sage: H.make()
            sage: H.depth()
            3
            sage: H._lower_bound_depth()
            3
            sage: CohomologyRing.set_local_sources(False)

        """
        try:
            return self.depth()
        except KeyboardInterrupt:
            self.reconstruct_singular()
        except ValueError:
            pass
        HP = self._HP
        if HP is None:
            return self.CenterRk
        return self._HP._lower_bound_depth()

    @permanent_result
    def depth(self):
        """
        Return the depth of ``self``, i.e., the length of a maximal regular sequence.

        NOTE:

        By theorems of Duflot and Kuhn, the rank of the center of the underlying group
        is a lower bound for the depth. The `p`-rank of the group is equal to the
        dimension of the cohomology ring, and thus is an upper bound.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(32,27)
            sage: H.make()
            sage: H.dimension()
            4
            sage: H.CenterRk
            2
            sage: H.depth()
            3

        """
        if not self.completed:
            raise ValueError("The ring structure is not completely known yet")
        # see if there is cached data
        for a,b in self._decorator_cache.items():
            if a[0] == 'raw_filter_degree_type':
                if not isinstance(b[0],KeyboardInterrupt):#b[0] is not NotImplemented:
                    return b[0][0][:-1].count(-1)
        from pGroupCohomology.modular_cohomology import MODCOHO
        if isinstance(self,MODCOHO):
            if len(self._PtoPcapCPdirect)==0:
                return self._HP.depth()
        if self._depth is not None:
            d = self._depth
            self.delprop('_depth')
            return d

        coho_logger.info('Computation of depth interruptible with Ctrl-c', self)

        try:
            br = singular('basering')
        except TypeError:
            br = None
        self.make_groebner()

        d = 0
        self.set_ring()
        dgb = singular.eval('degBound')
        singular.eval('degBound=0')
        I = singular(self.prefix+'I')
        singular.eval('attrib(%s,"isSB",1)'%I.name())
        gb_command = self._gb_command()
        P = self.filter_regular_parameters()
        self.set_ring()
        RAW = self.raw_filter_degree_type(P)
        d = RAW[0][:-1].count(-1)

        singular.eval('degBound='+dgb)
        try:
            if br is not None:
                br.set_ring()
        except RuntimeError:
            pass
        return d

    def filter_degree_type(self):
        """
        Return the filter degree type of ``self``.

        OUTPUT:

        The filter degree type (list of integers) of a filter regular
        system of parameters of self, or ``None``, if the cohomology
        computation is not finished yet.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: print(H.filter_degree_type())
            None
            sage: H.make()

        Since by default data are stored on disk, when we now compute the
        filter degree type (which in some cases is a very long computation!),
        the stored data are updated::

            sage: print(H.filter_degree_type())
            H^*(D8; GF(2)):
                      Updating stored data after computation of filter degree type
            [-1, -2, -2]

        """
        from pGroupCohomology.modular_cohomology import MODCOHO
        if isinstance(self,MODCOHO):
            if len(self._PtoPcapCPdirect)==0:
                return self._HP.filter_degree_type()
        if self.fdt is None:
            if self.completed:
                coho_logger.info('Computing filter degree type', self)
                coho_logger.info('Interruptible with Ctrl-c', self)
                # In the past, we first tried whether "general" small degree
                # parameters happen to be filter regular. This was often the case
                # and was helpful, as the computation of the raw filter degree
                # type used to be a bottle neck. But this is not the case anymore.
                # Hence, we directly start with parameters that are known to be
                # filter regular.
                P = self.filter_regular_parameters()
                if isinstance(P,KeyboardInterrupt):
                    raise RuntimeError("Computation of filter regular parameters failed\n"+repr(P))
                RAW = self.raw_filter_degree_type(P)
                if isinstance(RAW,KeyboardInterrupt):#RAW is NotImplemented:
                    coho_logger.warning('Computation of filter degree type was interrupted.', self)
                    self.set_ring()
                    return None
                if RAW is None:
                    raise RuntimeError("The parameters {} are supposed to be filter regular, but aren't. Theoretical error.".formal(P))
            if self.fdt is not None:
                if coho_options['save']:
                    coho_logger.warning( "Updating stored data after computation of filter degree type", self)
                    safe_save(self,self.autosave_name())
        return self.fdt

    @permanent_result
    def a_invariants(self):
        """
        Return the `a`-invariants of ``self``.

        THEORY:

        A filter regular homogeneous system of paramaters can be
        used for an iterative computation of the `a`-invariants,
        provided the parameters are of sufficiently high degree.
        Often the data obtained by verifying Benson's completeness
        criterion are sufficient for the computation of `a`-invariants.
        However, in some cases it is needed to raise the parameters
        occuring in Benson's criterion to some power.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, useElimination=True, from_scratch=True)
            sage: H.make()
            sage: H.a_invariants()
            [-Infinity, -Infinity, -2]

        The attribute ``H.A_INV_Expos`` tells whether it was needed to raise
        the parameters to some power (this is not the case here)::

            sage: H.A_INV_Expos
            [1, 1]

        """
        if not self.completed:
            return
        if self.A_INV:
            A_INV = self._A_INV
            self.delprop('A_INV')  # it is cached elsewhere
            return A_INV
        PAR = self.filter_regular_parameters()
        coho_logger.info("Computing a-invariants", self)
        coho_logger.info("Interruptible with Ctrl-c", self)
        cdef int m,n
        RAW = self.raw_filter_degree_type(PAR)
        if not RAW:
            raise ValueError("The given parameters are not filter regular")
        if isinstance(RAW,KeyboardInterrupt):
            raise RAW
        rfdt, HV, ParDeg = RAW
        Expos = [1]*len(ParDeg)
        # H_m shall be H modulo the first m parameters
        # a^n_m shall be the n-th a-invariant of H_m
        while (1):
            NeedSquaring=False
            A={}
            for m from len(PAR)>=m>=0:
                if rfdt[m]==0:
                    A[m,0]=0
                else:
                    A[m,0] = min(rfdt[m]*infinity, rfdt[m])
                for n from 0<n<=len(PAR)-m:
                    if (A[m+1,n-1]>A[m,n-1]) or (A[m+1,n-1]==-infinity):
                        # recursion formula works
                        A[m,n] = A[m+1,n-1] - ParDeg[m]
                    else:
                        NeedSquaring = True
                        break
                if NeedSquaring:
                    coho_logger.debug('> Squaring %s parameter', self, Integer(m+1).ordinal_str())
                    PAR[m]='('+PAR[m]+')**2'
                    Expos[m]=2*Expos[m]
                    break
            if NeedSquaring:
                RAW = self.raw_filter_degree_type(PAR)
                # now, the raw filter degree type might suffice to get the `a`-invariants.
                if isinstance(RAW,KeyboardInterrupt):
                    raise RAW
                rfdt, HV,ParDeg = RAW
            else:
                break
        self.setprop('A_INV_Expos',Expos)
        return [A[0,n] for n in range(len(rfdt))]

    def _poincare_series_of_ideal_(self, I, in_quotient=True):
        r"""
        Return the Poincaré series of the ideal `I`, which must define the standard
        basis of an ideal in the singular interface version of ``self``.

        INPUT:

        - ``I`` -- something that can be interpreted as the standard basis of an
          ideal in the current ring approximation.
        - ``ìn_quotient`` (optional bool, default ``True``) -- whether or not
          ``I`` is sought in the quotient ring corresponding to ``self``, or
          in the polynomial ring that covers the quotient ring.

        EXAMPLES:

        The input `'std(0)'` yields the Poincaré series of the current ring
        approximation::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,4, from_scratch=True)

        Computed out to degree 1, the ring approximation is a polynomial ring
        with two generators, with the expected Poincaré series::

            sage: H.make(1)
            sage: H.Gen
            [a_1_0: 1-Cocycle in H^*(Q8; GF(2)), a_1_1: 1-Cocycle in H^*(Q8; GF(2))]
            sage: H.rels()
            []
            sage: H._poincare_series_of_ideal_('std(0)')
            1/(t^2 - 2*t + 1)

        Computing one degree further, some relation but not new generator is
        found and the Poincaré series changes::

            sage: H.make(2)
            sage: H.Gen
            [a_1_0: 1-Cocycle in H^*(Q8; GF(2)), a_1_1: 1-Cocycle in H^*(Q8; GF(2))]
            sage: H.rels()
            ['a_1_1^2+a_1_0*a_1_1+a_1_0^2']
            sage: H._poincare_series_of_ideal_('std(0)')
            (-t - 1)/(t - 1)

        After a complete computation, the Poincaré series has changed
        again. Note that one can do the same computation in the quotient ring
        or in a polynomial ring::

            sage: H.make()
            sage: H.Gen
            [c_4_0: 4-Cocycle in H^*(Q8; GF(2)),
             a_1_0: 1-Cocycle in H^*(Q8; GF(2)),
             a_1_1: 1-Cocycle in H^*(Q8; GF(2))]
            sage: H.rels()
            ['a_1_1^2+a_1_0*a_1_1+a_1_0^2', 'a_1_0^3']
            sage: H._poincare_series_of_ideal_('std(0)')
            (-t^2 - t - 1)/(t^3 - t^2 + t - 1)
            sage: H._poincare_series_of_ideal_('std(0)', True) == H._poincare_series_of_ideal_('std(0)', False)
            True

        Of course, it is possible to compute the Poincaré series of other
        ideals as well. In the following example, we have three groups of
        order 64 whose cohomology rings have the same Poincaré series and also
        the same generator degrees, but the Poincaré series of their
        nil-radicals are pairwise different. Note that we do not need to call
        `.make()`, since the cohomology rings are taken from the database that
        is part of this Sage package::

            sage: H1 = CohomologyRing(64, 18)
            sage: H2 = CohomologyRing(64, 19)
            sage: H3 = CohomologyRing(64, 25)
            sage: H1.make()
            sage: H2.make()
            sage: H3.make()
            sage: H1.degvec == H2.degvec == H3.degvec
            True
            sage: H1.poincare_series() == H2.poincare_series() == H3.poincare_series()
            True
            sage: H1._poincare_series_of_ideal_(H1.nil_radical())
            (-t^4 + 2*t^3 - 3*t^2 + 2*t - 1)/(t^10 - 2*t^9 + t^8 - t^2 + 2*t - 1)
            sage: H2._poincare_series_of_ideal_(H2.nil_radical())
            (2*t^6 - 2*t^5 - t^4 + 2*t^3 - 3*t^2 + 2*t - 1)/(t^10 - 2*t^9 + t^8 - t^2 + 2*t - 1)
            sage: H3._poincare_series_of_ideal_(H3.nil_radical())
            (t^6 - t^5 - t^4 + 2*t^3 - 3*t^2 + 2*t - 1)/(t^10 - 2*t^9 + t^8 - t^2 + 2*t - 1)

        We check that the computation also works in odd characteristic and in
        some corner cases, which was broken before version 2.1.5::

            sage: H = CohomologyRing(2, 1)
            sage: H.make()
            sage: H._poincare_series_of_ideal_(H.nil_radical())
            -1/(t - 1)
            sage: H = CohomologyRing(3, 1)
            sage: H.make()
            sage: H._poincare_series_of_ideal_(H.nil_radical())
            -1/(t^2 - 1)
            sage: H = CohomologyRing(81, 7)
            sage: H.make()
            sage: H._poincare_series_of_ideal_(H.nil_radical())
            -1/(t^10 - 2*t^8 + t^6 - t^4 + 2*t^2 - 1)

        """
        singular = self.GenS.parent()
        dgb = singular.eval('degBound')
        self.make_groebner()
        singular.eval('degBound = 0')
        try:
            if in_quotient:
                singular(self).set_ring()
                selfname = singular(self).name()
            else:
                self.set_ring()
                selfname = '%sr(%d)'%(self.prefix,self.lastRelevantDeg or self.knownDeg)
            if isinstance(I, (str, unicode)):
                I = singular(I)
            if not in_quotient:
                I = singular('%sI+%s'%(self.prefix, I.name()))
                singular.eval('attrib(%s,"isSB",1)'%I.name())
            HP = first_hilbert_series(I)
            t = HP.parent().gen()
            HS = HP/mul([(1-t**d) for d in self.degvec])
            if HS.denominator().leading_coefficient()<0:
                return (-HS.numerator()/(-HS.denominator()))
            return HS
        finally:
            try:
                singular.eval('degBound = %s'%dgb)
            except:
                pass

    @temporary_result
    def poincare_series(self, test_duality=False):
        r"""
        Return the Poincaré series of ``self``, a univariate rational function.

        ALGORITHM:

        If Benson's criterion was used to proof completeness of the ring
        structure, it was needed to verify that certain parameters of the
        ring are filter regular. This involves computing kernel and
        quotients of multiplication maps. These data are saved, and now
        used for the computation of the Poincaré series.

        Otherwise, some standard way of computation from commutative
        algebra is used.

        INPUT:

        ``test_duality`` -- (bool, default ``False``) If this argument
        is ``True`` and``self`` is already completed and happens to be
        Cohen-Macaulay, a self consistence check is applied, based on
        Benson-Carlson duality [BensonCarlson]_.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.poincare_series()
            1/(t^2 - 2*t + 1)

        """
        if self.POINCARE:
            POINCARE = self.POINCARE
            self.delprop('POINCARE')  # it is cached differently now
            return POINCARE
        if not self.completed:
            return self._poincare_without_parameters()
        if self.CenterRk is None:
            return self._poincare_without_parameters(test_duality)
        HilbertVectors = None
        # test if there is a cached value
        cdef list DV
        for a,b in self._decorator_cache.items():
            if a[0]=='raw_filter_degree_type':
                if b[0] and not isinstance(b[0],KeyboardInterrupt):#b[0] is not NotImplemented:
                    rfdt, HilbertVectors, DV = b[0]
                    break
        if not HilbertVectors:
            return self._poincare_without_parameters(test_duality)
        cdef int lenHV = len(HilbertVectors)-1
        cdef int i
        PS = HV2Poly(HilbertVectors[-1])
        R = PolynomialRing(QQ,'t')
        t = R('t')
        Xtra = R(1)
        for i from lenHV > i >= 0:
            PS = PS - (t**DV[i])*Xtra*HV2Poly(HilbertVectors[i])
            Xtra = Xtra*(1-t**DV[i])
        OUT = PS/Xtra
        if test_duality and self._lower_bound_depth()==self.dimension(): # the poincare series has to satisfy Benson-Carlson duality
            if OUT(t.__invert__())!=(-t)**self.dimension()*OUT:
                raise RuntimeError("Theoretical Error: The cohomology ring is Cohen-Macaulay, but Benson-Carlson duality fails to hold.")
        if Xtra.leading_coefficient() < 0:
            return (-PS)/(-Xtra)
        return OUT

    def _poincare_without_parameters(self, test_duality=False):
        r"""
        Return the Poincaré series of ``self``, a univariate rational function.

        INPUT:

        ``test_duality`` -- (bool, default ``False``) If this argument
        is ``True`` and``self`` is already completed and happens to be
        Cohen-Macaulay, a self consistence check is applied, based on
        Benson-Carlson duality [BensonCarlson]_.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H._poincare_without_parameters()
            1/(t^2 - 2*t + 1)

        """
        if self.POINCARE:
            POINCARE = self.POINCARE
            self.delprop('POINCARE') # now cached differently
            return POINCARE
        try:
            br = singular('basering')
        except:
            br = None
        try:
            self.make_groebner()
            self.set_ring()
            OUT = hilbert_poincare_series(singular.ideal(self.prefix+'I'))
            if test_duality and self.completed and self._lower_bound_depth()==self.dimension():
                # the poincare series has to satisfy Benson-Carlson duality
                t = OUT.parent().gen()
                if OUT(t.__invert__())!=(-t)**self.dimension()*OUT:
                    raise RuntimeError("Theoretical Error: The cohomology ring is Cohen-Macaulay, but Benson-Carlson duality fails to hold.")
            return OUT
        finally:
            try:
                br.set_ring()
            except:
                pass

    def _verify_consistency_of_dimensions(self, count_standard_monomials=False):
        r"""
        Assert consistency of dimensions and Poincaré series.

        It should of course be the case that the dimension
        of the `k`-th cohomology group coincides with the `k`-th
        coefficient of the Poincaré series. So, we obtain a
        consistency test that is relatively cheap.

        In the case of a prime power group, it is only tested that the
        rank of the `k`-th term of the minimal free resolution is
        consistent with the `k`-th coefficient of the Poincaré series,
        unless the optional argument ``count_standard_monomials`` is
        True.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()
            sage: H = CohomologyRing(192, 1023, prime=2)
            sage: H.make(8)
            sage: H._verify_consistency_of_dimensions()
            sage: H.subgroup_cohomology()._verify_consistency_of_dimensions(True)
            sage: [len(H.standard_monomials(i)) for i in range(8)]
            [1, 0, 4, 6, 2, 13, 20, 14]
            sage: [PowerSeriesRing(QQ,'t')(H.poincare_series())[i] for i in range(8)]
            [1, 0, 4, 6, 2, 13, 20, 14]
            sage: H.subgroup_cohomology().resolution().rank()
            (1, 4, 8, 12, 20, 33, 48, 64, 87, 118, 152, 188, 234)
            sage: [PowerSeriesRing(QQ,'t')(H.subgroup_cohomology().poincare_series())[i] for i in range(13)]
            [1, 4, 8, 12, 20, 33, 48, 64, 87, 118, 152, 188, 234]

        """
        from sage.all import PowerSeriesRing, QQ
        P = PowerSeriesRing(QQ,'t',default_prec=self.knownDeg+1)
        p = self.poincare_series()
        dims = P(p.numerator())/P(p.denominator())
        cdef size_t i
        cdef RESL R
        if self._HP is None:
            R = self.Resl
            for i in range(self.knownDeg+1):
                assert R.rank(i) == dims[i], "Degree {}: Rank should be {}, Poincaré series predicts {}".format(i,R.rank(i),dims[i])
                if count_standard_monomials:
                    lstdmon = len(self.standard_monomials(i))
                    assert dims[i] == lstdmon, "Degree {}: Should have {} standard monoials, got {}".format(i,dims[i],lstdmon)
        else:
            for i in range(self.knownDeg+1):
                lstdmon = len(self.standard_monomials(i))
                assert dims[i] == lstdmon, "Degree {}: Should have {} standard monoials, got {}".format(i,dims[i],lstdmon)

#################################
## Persistent Group Cohomology ##
#################################

    @permanent_result
    def bar_code(self, command, degree=-1):
        r"""
        Compute the persistent cohomology for a specified normal subgroup series.

        ASSUMPTION:

        The subgroups and quotient groups can be found in the SmallGroups library.

        INPUT:

        ``command``: The name (string) of a Gap command that produces
                     a series of normal subgroups when applied to the
                     group ``self.group()``, starting with ``self.group()``
                     and terminating with the trivial group.

        ``degree=-1``: Optional parameter. If ``degree>=0`` then only
                       the bar code in the specified degree is computed;
                       otherwise, all degrees are studied simultaneously,
                       by Poincaré series.

        OUTPUT:

        ``self``'s full bar code (class
        :class:`~pGroupCohomology.barcode.BarCode`) respectively
        bar code of the given degree (class
        :class:`~pGroupCohomology.barcode.BarCode2d`),
        associated with the specified normal series.

        THEORY:

        Any sequence of group homomorphisms `\phi_i: G_i \to G_{i+1}`
        with `i=1,...,n` gives rise to a series of induced homomorphisms
        of cohomology rings. Persistent group cohomology, introduced by
        [EllisKing]_, asks how long cocycles in a given degree"survive"
        being mapped by the induced homomorphisms. For a given degree
        `d`, the persistent cohomology can be described by an upper
        triangular matrix of non-negative integers, where entry
        `i,j` (`i\le j`) is the dimension of the image of the degree
        `d` part of `H^*(G_j)` in `H^*(G_i)` under the induced
        homomorphism given by the composition of
        `\phi_i,\phi_{i+1},...,\phi_{j-1}`, including the case
        `i=j` in which the matrix entry simply gives the dimension
        of the degree `d` part of `H^*(G_i)`.

        As usual, the sequence of dimensions sorted by degree gives
        rise to a Poincaré series. Hence, an upper triangular
        matrix of rational functions results and this provides
        information for all degrees.

        EXAMPLES:

        We work here with groups of order 64, that are part of the
        cohomology data base shipped with this package.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: H158 = CohomologyRing(64,158)
            sage: H158.make()
            sage: H160 = CohomologyRing(64,160)
            sage: H160.make()

        The Poincaré series, the `a`-invariants, the degrees of
        generators and of relations of the cohomology rings coincide::

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
        series. It turns out that the non-trivial terms of the upper
        central series and the resulting factor groups are isomorphic::

            sage: G158 = libgap.SmallGroup(64,158)
            sage: G160 = libgap.SmallGroup(64,160)
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

        Nevertheless, the groups can be distinguished using the bar
        codes associated with the upper central series::

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

        These pictures (bar codes) can be interpreted as follows.
        Let `G` be a finite `p`-group and let
        `G=G_0 > G_1 > ... > G_n > 1` be a normal series; in our
        example, we have `n=2`. The first `n+1` columns of the bar
        code correspond to the normal subgroups groups
        `G_n, G_{n-1},..., G_0`, while the last `n` columns correspond
        to the factor groups `G/G_n, G/G_{n-1},..., G/G_1`. We consider
        the sequence of group homomorphisms given by inclusions and
        quotients. The stars in the bar code correspond to basis
        vectors of the degree `d` part of the cohomology rings of the
        respective groups. Stars are connected by a line (i.e., a hyphen)
        if the corresponding basis vectors are mapped to each other by
        the induced maps (which of course go from right to left).

        In terms of the persistance matrix::

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

        The bar codes in degree 3 can also be computed directly, and
        of course it coincides with the bar codes obtained from the
        "full" bar codes (based on Poincaré series)::

            sage: B158[3] == H158.bar_code('UpperCentralSeries',degree=3)
            True
            sage: B160[3] == H160.bar_code('UpperCentralSeries',degree=3)
            True

        Since apparently the ``(2,4)`` entries of the persistence
        matrices differ, we show here how the Poincaré series
        in that position look like::

            sage: B158.matrix()[2,4]
            2*t^2 + 2*t + 1
            sage: B160.matrix()[2,4]
            t^3 + 2*t^2 + 2*t + 1

        Hence, the image of the map `H^*(G/G_2) \to H^*(G)` induced
        by the quotient map contains only finitely many cocycles,
        where `G` is group number 158 or 160 of order 64, and `G_2`
        is the second term of the upper central series.

        """
        cdef int i,j,l
        from pGroupCohomology import CohomologyRing
        gap = self.group().parent()
        try:
            C = gap.function_factory(command)
        except:
            raise ValueError('The given command "%s" is not known to Gap'%command)
        _gap_reset_random_seed()
        L = list(C(self.group()))
        G = L.pop(0)
        if G != self.group():
            raise ValueError('The given command "%s" must produce a normal series of subgroups when applied to self.group()'%command)
        if L.pop(-1).Order()>1:
            raise ValueError('The given command "%s" must produce a normal series of subgroups when applied to self.group()'%command)
        l = len(L)  # the number of non-trivial subgroups in the normal series
        # In the following dictionaries, the keys range from -l to l, where
        # the key 0 corresponds to the group of this ring.
        Groups = { 0 : G } # dictionary of Groups.
        CRings = { 0 : self } # the cohomology rings corresponding to Groups
        # isomorphism from CRings' groups to Groups and (later)
        # the group homomorphism from CRing[i].group() to CRing[j].group()
        # In this dictionary, the keys are integers i and pairs [i,j] with -l<=i<j<=l
        Morphs = { 0 : self.group().IsomorphismGroups(G) }
        QuMaps = { 0 : G.IdentityMapping() }
        i = 0
        while L:
            S = L.pop(-1)
            if not G.IsNormal(S):
                raise ValueError('The given command "%s" must produce a normal series of subgroups when applied to self.group()'%command)
            # First insert the subgroups into the dictionaries
            Groups[-l+i] = S
            q,n = S.IdGroup().sage()
            CRings[-l+i] = CohomologyRing(q,n, prime=self._prime)
            CRings[-l+i].make()
            Morphs[-l+i] = CRings[-l+i].group().IsomorphismGroups(S) # just choose one isomorphism
            # Next insert the quotient groups into the dictionaries
            i += 1
            QMap = G.NaturalHomomorphismByNormalSubgroupNC(S)
            QuMaps[i] = QMap
            Q = gap.Group([QMap.Image(g) for g in QMap.Source().GeneratorsOfGroup()])
            Groups[i] = Q
            q,n = Q.IdGroup().sage()
            CRings[i] = CohomologyRing(q,n, prime=self._prime)
            CRings[i].make()
            Morphs[i] = CRings[i].group().IsomorphismGroups(Q) # just choose one isomorphism
        # Now we have all the groups, and will construct the group
        # homomorphisms. First, the elementary ones:
        for i in range(0,l):
            # 1. Subgroup inclusion
            S = Groups[-l+i]
            Sgen = S.GeneratorsOfGroup()
            G = Groups[-l+i+1]
            Morphs[-l+i, -l+i+1] = Morphs[-l+i+1].InverseGeneralMapping().CompositionMapping(
                    S.GroupHomomorphismByImagesNC(G,Sgen,Sgen), Morphs[-l+i])
            # 2. Quotient maps, using the isomorphism theorem, (G/S) = (G/T)/(T/S)
            Q = Groups[i]
            Qgen = Q.GeneratorsOfGroup()
            Q1 = Groups[i+1]
            QMap_i  = QuMaps[i]
            QMap_i1 = QuMaps[i+1]
            Morphs[i, i+1] = Morphs[i+1].InverseGeneralMapping().CompositionMapping(
                    Q.GroupHomomorphismByImagesNC(Q1, Qgen, [QMap_i1.Image(QMap_i.PreImagesRepresentative(g)) for g in Qgen]),
                    Morphs[i])
        # Now, we are computing the compositions of the above mappings, and eventually
        # the induced morphisms and their ranks.
        OUT = {}
        for i in range(-l,l):
            if degree==-1:
                OUT[i,i] = CRings[i].poincare_series()
            else:
                OUT[i,i] = CRings[i].resolution().rank(degree)
            f = Morphs[i,i+1]
            if degree==-1:
                OUT[i, i+1] = CRings[i+1].hom( f, CRings[i]).poincare_of_image()
            else:
                OUT[i, i+1] = CRings[i+1].hom( f, CRings[i]).rank_of_image(degree)
            for j in range(i+1, l):
                f = Morphs[j, j+1].CompositionMapping2( f )
                if degree==-1:
                    OUT[i, j+1] = CRings[j+1].hom( f, CRings[i]).poincare_of_image()
                else:
                    OUT[i, j+1] = CRings[j+1].hom( f, CRings[i]).rank_of_image(degree)
        if degree==-1:
            OUT[l,l] = CRings[l].poincare_series()
        else:
            OUT[l,l] = CRings[l].resolution().rank(degree)

        from pGroupCohomology.barcode import BarCode,BarCode2d
        if degree==-1:
            return BarCode(OUT, ring=self.__repr__(),command=command)
        return BarCode2d(OUT, degree=degree,ring=self.__repr__(),command=command)

#####################
## Massey products ##
#####################
    def massey_products(self, *L, all=True):
        r"""
        All possible elements of ``self`` that realize the Massey product of the given input.

        INPUT:

        - ``C_1,C_2,...``: Elements of the cohomology ring.
        - ``all`` (optional, default ``True``): If it is ``False``, a set containing at most
          one cocycle is returned.

        OUTPUT:

        The set valued Massey product of ``C_1,C_2,...``

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: H.2
            b_1_0: 1-Cocycle in H^*(D8; GF(2))
            sage: H.3
            b_1_1: 1-Cocycle in H^*(D8; GF(2))
            sage: H.rels()
            ['b_1_0*b_1_1']

        Since the product of ``H.2`` and ``H.3`` vanishes, we can compute some
        triple Massey products, transforming the result into a sorted list for
        having reproducible doc tests::

            sage: sorted(list(H.massey_products(H.2,H.3,H.2)))
            [0: 2-Cocycle in H^*(D8; GF(2)), b_1_0^2: 2-Cocycle in H^*(D8; GF(2))]
            sage: sorted(list(H.massey_products(H.3,H.2,H.3)))
            [0: 2-Cocycle in H^*(D8; GF(2)), b_1_1^2: 2-Cocycle in H^*(D8; GF(2))]

        Here is another example, for testing against a bug that occurred in a
        previous version of the code::

            sage: H = CohomologyRing(16,2)
            sage: H.make()
            sage: sorted(list(H.massey_products(H.3*H.1,H.3,H.3*H.1)))
            [0: 6-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_2_1*c_2_2*c_1_0*c_1_1: 6-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_2_1^2*c_1_0*c_1_1: 6-Cocycle in H^*(SmallGroup(16,2); GF(2)),
             c_2_1*c_2_2*c_1_0*c_1_1+c_2_1^2*c_1_0*c_1_1: 6-Cocycle in H^*(SmallGroup(16,2); GF(2))]

        If one is interested in only one element of the Massey product, one can use the optional
        parameter ``all=False``::

            sage: H.massey_products(H.3*H.1,H.3,H.3*H.1,H.3*H.1, all=False)
            {c_2_1^4: 8-Cocycle in H^*(SmallGroup(16,2); GF(2))}

        There are various results on Massey products that can be used for
        testing our computations.  We give one explicit computation in the
        documentation of :meth:`~pGroupCohomology.cochain.COCH.massey_power`.
        Here, we test against a part of the Juggling Theorem (see [Ravenel]_
        Section A1.4) that states

            `\langle c_1,c_2,...,c_n\rangle c \subset \langle c_1,c_2,...,c_{n-1},c_nc\rangle,`

        where `c,c_1,...,c_n` are cocycles, and the multiplication on the left
        hand side is taken element-wise. For our example, we use the
        extraspecial 3-group of order 27 and exponent 3::

            sage: H = CohomologyRing(27,3)
            sage: H.make()
            sage: H.gens()
            [1, b_2_0: 2-Cocycle in H^*(E27; GF(3)), b_2_1: 2-Cocycle in H^*(E27; GF(3)), b_2_2: 2-Cocycle in H^*(E27; GF(3)), b_2_3: 2-Cocycle in H^*(E27; GF(3)), c_6_8: 6-Cocycle in H^*(E27; GF(3)), a_1_0: 1-Cocycle in H^*(E27; GF(3)), a_1_1: 1-Cocycle in H^*(E27; GF(3)), a_3_4: 3-Cocycle in H^*(E27; GF(3)), a_3_5: 3-Cocycle in H^*(E27; GF(3))]
            sage: H.massey_products(H.6,H.6,H.6,all=False)
            {-b_2_0: 2-Cocycle in H^*(E27; GF(3))}
            sage: H.massey_products(H.6,H.6,H.6*H.5,all=False)
            {-b_2_0^2*a_1_1*a_3_5+b_2_0^2*a_1_0*a_3_4-b_2_0*c_6_8: 8-Cocycle in H^*(E27; GF(3))}

        Note that there is the summand ``-b_2_0*c_6_8`` that we would
        expect. There remains to show that the other summands belong to the
        indeterminacy of the Massey product. More precisely, we show that
        ``-b_2_0^2*a_1_1*a_3_5+b_2_0^2*a_1_0*a_3_5`` is a multiple of
        ``H.6``::

            sage: H.6*(2*H.8*H.2*H.2+2*H.8*H.1*H.2 + H.1^2*H.9) == H('-b_2_0^2*a_1_1*a_3_5+b_2_0^2*a_1_0*a_3_5')
            True

        Hence, ``H.massey_products(H.6,H.6,H.6*H.5)`` contains ``-b_2_0*c_6_8``.

        """
        R = self.resolution()
        for X in L: # X should be an element of self
            if (not hasattr(X,'parent')) or (X.parent() is not self):
                raise ValueError("Item %s is not an element of self"%X)
        from pGroupCohomology.resolution import MasseyDefiningSystems
        from pGroupCohomology.cochain import YCOCH
        YCList = [C.yoneda_cocycle() for C in L]
        P = MasseyDefiningSystems(*YCList, all=all)
        SOut = set([ ( X.deg(), R.ChainmapToCochain( (X.deg(),0,X[0]) ) ) for X in P.values()])
        return set([self.element_as_polynomial(COCH(self, X[0], 'bla', X[1])) for X in SOut])

#####################################################################
##  Completion tests
##  - a heuristics to choose the two available tests
##  - Benson
##    * degree in which the last relation is expected
##    * degree in which the criterion potentially applies
##    * filter regularity
##  - Symonds
#####################################################################

    def test_for_completion(self,forced = False):
        """
        Test whether the current ring approximation is complete.

        OUTPUT:

        ``True`` (complete), ``False`` (incomplete) or ``None`` (can't be decided yet)

        THEORY:

        We choose between two criteria:

        * The [Benson]_ criterion modified by [GreenKing]_:
          It relies on the construction of a filter regular
          hsop for the ring approximation that is guaranteed
          to correspond to a hsop in cohomology, and on the
          existence of a filter regular hsop in small degrees
          over a finite extension of the coefficient field.
        * The [Symonds]_ criterion: It relies on the construction
          of a hsop for the cohomology in small degrees,
          and the generator degree of the ring approximation
          as a module over these parameters. These parameters
          do not need to be algebraically independent.

        The advantage of the Benson criterion is that often there
        exist fairly small parameters over a finite extension field
        that can not be found in the original cohomology ring; hence
        it may apply much earlier than the Symonds test. Note that
        if the rank of the centre of a Sylow subgroup is at least
        two then the degree bound drops by one.

        The advantage of the Symonds test is that it does not rely on
        filter regularity. Often, one finds a general hsop in smaller
        degrees than a filter regular hsop. Moreover, it is not needed
        to compute the filter degree type of the ring, which can be a
        very difficult part of Benson's test. Note that the rank of
        the centre of a Sylow subgroup has no influence on the degree
        bound.

        We give more details in the documentation of :mod:`pGroupCohomology`.

        ALGORITHM:

        - If the Symonds test has a chance to apply (which can be seen
          in the degrees of the hsop) then it is tried.
        - If the Symonds test has no chance to apply yet, Benson's
          test is chosen.

        EXAMPLES:

        We compute the rings in a way that avoids the automatic
        execution of this method.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H64 = CohomologyRing(64,6, useElimination=True, from_scratch=True)
            sage: H64.make(3)
            sage: H64.next()

        Now, the ring structure is known out to degree four. A hsop
        can be found in sufficiently small degrees. Therefore, the
        Symonds test is chosen, which can be seen in the log and in
        the attribute ``_method``::

            sage: H64.parameters()
            ['c_2_2', 'c_2_3', 'b_1_1']
            sage: CohomologyRing.global_options('info')
            sage: H64.test_for_completion()
            H^*(SmallGroup(64,6); GF(2)):
                Compute dependent_parameters
                Try to find a set of generators over which the cohomology ring is finite.
                Trying Symonds' criterion
                Successful application of the Symonds criterion
            True
            sage: CohomologyRing.global_options('warn')
            sage: H64._method
            'Symonds'
            sage: H64.completed
            True

        In our second example, the Benson criterion is used. Again,
        we compute the ring structure to a sufficient degree, but
        avoiding the automatic completion testing.
        ::

            sage: H81 = CohomologyRing(81,14, from_scratch=True)
            sage: H81.make(7)
            sage: H81.next()

        We find filter regular parameters that would allow the
        original form of Benson's test (see [Benson]_) to apply in
        degree `5+3+1=9`. We don't find smaller algebraically
        independent parameters, but there are algebraically dependent
        parameters in rather small degree, so that the completeness
        can be proved using the [Symonds]_ criterion::

            sage: H81.filter_regular_parameters()
            ['c_6_8', 'b_4_5-b_2_4^2-b_2_3^2']
            sage: H81.parameters()
            ['c_6_8', 'b_4_5-b_2_4^2-b_2_3^2']
            sage: H81.dependent_parameters()
            ['a_1_0', 'a_1_1', 'a_1_2', 'c_6_8', 'b_2_3', 'b_2_4']
            sage: CohomologyRing.global_options('info')
            sage: H81.test_for_completion()
            H^*(E27*C9; GF(3)):
                Trying Symonds' criterion
                Successful application of the Symonds criterion
            True

        Note that the modified Benson criterion of [GreenKing]_
        applies in degree eight as well::

            sage: H81.BensonTest(H81.filter_regular_parameters(),[6,4])
                Testing whether it makes sense to try Benson's completeness criterion
                It is possible that Benson's degree bound applies
                Compute raw_filter_degree_type
                Test filter regularity
                  Filter degree type: [-1, -2, -2]
            True
            sage: CohomologyRing.global_options('warn')
            sage: H81.WhatFRS
            (1, 2)

        By the last line, it is possible to replace one (namely the
        last) parameter by an element of degree two, over a finite
        extension of the field of coefficients. This suffices for
        the modified Benson criterion.

        """
        from pGroupCohomology.modular_cohomology import MODCOHO
        if self.suffDeg>-1 and self.knownDeg >= self.suffDeg:
            self.completed=True
            return True
        if (self.expect_last_relation() > self.knownDeg) and not forced:
            coho_logger.info("We expect a relation in degree at least %d",self, self.expect_last_relation())
            return
        #########
        ## Attempt Symonds' test
        Benson = None
        DepPars = self.dependent_parameters()
        if DepPars is None:
            return False
        self.set_ring()
        Depdv = [Integer(singular.eval("deg(%s)"%(x))) for x in DepPars]  # this is the real degree vector
        if sum([t-1 for t in Depdv]) < self.knownDeg:
            Pars = DepPars
            dv = Depdv
        else: # the following can be very costly, but the user can interrupt it.
            Pars = self.parameters()
            #########
            if Pars is None:
                Pars = DepPars
            dv = [Integer(singular.eval("deg(%s)"%(x))) for x in Pars]  # this is the real degree vector
            if sum([t-1 for t in dv]) > sum([t-1 for t in Depdv]):
                Pars = DepPars
                dv = Depdv
        Symonds = self.SymondsTest(Pars,dv, forced = forced)
        if Symonds:
            coho_logger.info("Successful application of the Symonds criterion", self)
            self.completed = True
            self.setprop('_parameters_for_criterion',[t for t in Pars])
            self.setprop('_method','Symonds')
            return True
        elif Symonds is None:
            # For Benson's test, we compute *filter regular* parameters.
            FRS = self.filter_regular_parameters()
            self.set_ring()
            dv = [Integer(singular.eval("deg(%s)"%(x))) for x in FRS]
            Benson = self.BensonTest(FRS,dv, forced = forced)
            if Benson:
                coho_logger.info("Successful application of the Benson criterion", self)
                self.completed = True
                self.setprop('_parameters_for_criterion',[t for t in FRS])
                self.setprop('_method','Benson')
                return True
            return Benson
        else:
            return False

    def BensonTest(self,FRS,dv, forced = False):
        """
        A modified version of Benson's completeness criterion.

        INPUT:

        - ``FRS``, a list of strings providing elements of ``self`` that are known to provide
          a filter regular HSOP for the cohomology ring
        - ``dv``, the degrees (list of integers) of these parameters
        - ``forced`` [optional, default = ``False``]: If ``True``, perform Benson's test even if it seems to be too low degree

        OUTPUT:

        - ``True`` if the test succeeded
        - ``None`` if the test was not conclusive
        - ``False`` if the test showed that the ring is incomplete.

        The attribute ``suffDeg`` may be modified.

        THEORY:

        See [GreenKing]_ and the outline we gave in :mod:`pGroupCohomology`.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,6, useElimination=True, from_scratch=True)
            sage: H.next()

        There are no suitable parameters of the current ring
        approximation, so that a completion test wouldn't make sense
        yet. So, we continue, and succeed with finding filter regular
        parameters::

            sage: H.filter_regular_parameters()
            sage: H.next()
            sage: H.filter_regular_parameters()
            ['c_2_2', 'c_2_3', 'b_1_1']

        It is not reasonable to apply Benson's test, yet, since we expect
        a relation in degree 4::

            sage: H.expect_last_relation()
            4

        And of course, the degrees of the parameters do not allow to
        prove completeness already in degree two::

            sage: CohomologyRing.global_options('info')
            sage: H.BensonTest(H.filter_regular_parameters(),[2,2,1])
            H^*(SmallGroup(64,6); GF(2)):
                Testing whether it makes sense to try Benson's completeness criterion
                We expect that Benson's test will not apply before degree 3

        So, we must go ahead. The log states that Benson's test will
        not apply before degree three. Perhaps it *does* apply in
        that degree, although we expect a relation in degree four?
        ::

            sage: CohomologyRing.global_options('warn')
            sage: H.next()
            sage: CohomologyRing.global_options('info')
            sage: H.BensonTest(H.filter_regular_parameters(),[2,2,1])
            H^*(SmallGroup(64,6); GF(2)):
                Testing whether it makes sense to try Benson's completeness criterion
                It is possible that Benson's degree bound applies
                Compute raw_filter_degree_type
                Computing complete Groebner basis
                Test filter regularity
                > Sequence is NOT filter regular. Sorry.
            False

        It does not. But in degree 4, everything works::

            sage: CohomologyRing.global_options('warn')
            sage: H.next()
            sage: CohomologyRing.global_options('info')
            sage: H.BensonTest(H.filter_regular_parameters(),[2,2,1])
            H^*(SmallGroup(64,6); GF(2)):
                Testing whether it makes sense to try Benson's completeness criterion
                It is possible that Benson's degree bound applies
                Compute raw_filter_degree_type
                Computing complete Groebner basis
                Test filter regularity
                  Filter degree type: [-1, -2, -3, -3]
            True

        Now the 'sufficient degree' is less than or equal to the known
        degree, hence, we are done::

            sage: H.suffDeg
            3
            sage: H.knownDeg
            4
            sage: CohomologyRing.global_options('warn')

        """
        try:
            #########
            ## Test whether Benson's criterion might apply yet
            if forced:
                potBound = self.potential_degree_bound(FRS,dv,forced=2)
            else:
                potBound = self.potential_degree_bound(FRS,dv,forced=1)
            if (potBound > self.knownDeg): # it makes no sense to test filter regularity right now
                coho_logger.info("We expect that Benson's test will not apply before degree %d", self, potBound)
                if forced:
                    coho_logger.info("However, we'll try...", self)
                else:
                    return
            else:
                coho_logger.info("It is possible that Benson's degree bound applies", self)
            ######
            ## Now, either we are forced to do the test or it actually makes sense to do so...
            if self.raw_filter_degree_type(FRS):
                suffDeg = max([0,self.alpha]) + potBound
            else:
                # if the FRS is not filter regular, then the ring is incomplete.
                return False
            if self.suffDeg > -1:
                self.suffDeg = min(self.suffDeg, suffDeg)
            else:
                self.suffDeg = suffDeg
            if self.knownDeg >= self.suffDeg:
                return True
        except KeyboardInterrupt:
            coho_logger.warning("Benson's completeness test was interrupted.", self)

    #######
    ## Auxiliary methods for Benson's test
    #######

    def expect_last_relation (self):
        """
        Returns a degree up to which there will provably be further non-obvious relations.

        ALGORITHM:

        1. If there are two different generators of degree `d_1` and `d_2` that are both not
           Duflot regular, then we expect a relation at least in degree `d_1+d_2`.
        2. If there is a nilpotent generator in degree `d`, then there will certainly
           be a relation in degree `2d`. In the case of `p`-groups with `p>2`, that relation
           is obvious for `d` odd and is not counted, and only part 1. applies.


        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3, from_scratch=True)
            sage: H.make(3)
            sage: H.expect_last_relation()
            6

        Indeed, there are two different non-regular generators of degree 3::

            sage: H.7
            a_3_4: 3-Cocycle in H^*(E27; GF(3))
            sage: H.8
            a_3_5: 3-Cocycle in H^*(E27; GF(3))

        """
        cdef RESL R = self.Resl
        cdef list L   = [X.deg() for X in self.Gen if not X.rdeg()]
        L.sort()
        if not L: # all cohomology rings should be at least computed out to degree 2
            return 2

        if R.G_Alg.Data.p!=2: # In this case, we can slightly improve the degree bound
            if L[-1]%2: # Hence, we have a nilpotent generator, but consider its relation automatically
                if len(L)==1:
                    return 2
                return L[-1]+L[-2]
        return 2*L[-1]

    #@temporary_result ## problem: man darf nicht self.knownDeg+1 liefern.
    def potential_degree_bound(self,FRS,dv, forced = 1, previous_bound=None):
        """
        Return the potential degree bound obtained from the modified Benson test.

        INPUT:

        - ``FRS``: a list of polynomials (given by strings)
        - ``DV``: the list of degrees of the polynomials from ``FRS``
        - ``forced`` (optional int); let `n` be the degree up to which
          the cohomology is known

          * If ``forced == 2``: return the best possible bound, even if
            it is smaller than `n`
          * If ``forced == 1``: the best potential bound, if it is
            greater than `n`, or some potential bound if it is at most `n`.

        ASSUMPTION:

        ``FRS`` were a filter regular HSOP, provided self was completely
        computed.

        THEORY:

        See [GreenKing]_, Proposition 3.2 and Theorem 3.3.

        EXAMPLES:

        We first create a cohomology ring. For constructing Dickson classes,
        we use the linear algebra method.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(27,3, useElimination=False, from_scratch=True)

        The computational steps in this example will internally be done
        by ``H.make()``. Here, we do them step by step.
        ::

            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
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

        During these computations, Dickson classes have been computed.
        We found::

            sage: H.Dickson
            ['b_2_3^2-b_2_0*b_2_2-b_2_0*b_2_1+b_2_0^2']

        It is known that the Duflot regular generator ``c_6_8`` and
        the Dickson class form a filter regular homogeneous HSOP of
        ``H``, provided the computation is complete.  However,
        Benson's criterion would only apply in degree 5+3+1=9. Now we
        test whether it is possible to replace the Dickson class by a
        parameter of smaller degree *over some finite extension
        field*. If there is more than one Dickson class, we would
        potentially replace several (but not necessarily all) of
        them. Note that our method is not constructive -- we just show
        the *existence* of a filter regular HSOP! In general, it is
        inevitable to extend the coefficient field.
        ::

            sage: H.potential_degree_bound(['c_6_8','b_2_3^2-b_2_0*b_2_2-b_2_0*b_2_1+b_2_0^2'],[6,4])
            7

        The previous line means: *If* ``['c_6_8','b_2_3^2-b_2_0*b_2_2-b_2_0*b_2_1+b_2_0^2']``
        gives rise to a filter regular HSOP of a ring approximation
        out to degree at least seven, and *if* the `n`-th term
        of the resulting filter degree type is not greater than `-n`
        for all but the last term, then the ring approximation is
        complete. Indeed::

            sage: H.raw_filter_degree_type(['c_6_8','b_2_3^2-b_2_0*b_2_2-b_2_0*b_2_1+b_2_0^2'])
            ([-1, -1, 8], [[0], [0], [1, 2, 4, 6, 6, 6, 4, 2, 1]], [6, 4])
            sage: H.filter_degree_type()
            [-1, -2, -2]

        So, we have shown that the cohomology computation is complete.
        """
        # Sets self.WhatFRS self.potential_bound. The significance is
        # different for Benson or Hilbert-Poincare criterion. But this
        # doesn't matter, since the criteria will not be simultaneously
        # applied
        if (forced!=2) and (self.potential_bound is not None):
            if self.last_interesting_degree()==self.knownDeg:
                self.delprop('potential_bound') # we need a re-computation
            else:
                if self.potential_bound == -1:
                    coho_logger.info("The ring approximation is incomplete", self)
                    return self.knownDeg + 1
                return self.potential_bound
        if previous_bound is None:
            coho_logger.info("Testing whether it makes sense to try Benson's completeness criterion", self)
        else:
            coho_logger.info("Testing whether we can do better than degree %d", self, previous_bound)
        cdef int i,N,d,D,tai
        cdef list DV
        DV = [max(2,NR) for NR in dv]
        cdef int lenDV
        if (self.CenterRk or (self._HP and self._HP._lower_bound_depth()) or 0)>1:
            lenDV = len(dv)
        else:
            lenDV = len(dv)-1
        cdef int natBound,potBound
        N = self.pRank - self.CenterRk
        # If the following was the case, then the ring was already
        # completed. But this can mean that completeness was detected
        # by a different criterion. So, cut this one out.
        natBound = previous_bound or (sum(DV)-lenDV)
        if N:
            potBound = sum(DV[:-N])+2*N - lenDV # takes the center into account, since lenDV is modified
        else:
            potBound = sum(DV) - lenDV
        if (natBound <= self.knownDeg) and (forced!=2): # makes no sense to try and improve
            self.setprop('potential_bound', natBound)
            return natBound
        if (potBound > self.knownDeg) and (forced!=2): # makes no sense to struggle, unless we force it
            # Since we don't do an actual computation, we don't store that figure
            return potBound
        ## Strategy: Keep all but n items of FRS and see whether the
        ## remaining can be replaced by parameters of degree d.
        ## Optimize n and d!

        self.set_ring()
        dgb=singular.eval("degBound")
        singular.eval("degBound = 0")
        if self.completeGroebner:
            singular.eval('attrib(%sI,"isSB",1)'%(self.prefix))
            I0 = singular('%sI'%(self.prefix))
            if N:
                for PL in FRS[:-N]:
                    singular.eval('%s = std(%s,%s)'%(I0.name(),I0.name(),PL))
            else:
                for PL in FRS:
                    singular.eval('%s = std(%s,%s)'%(I0.name(),I0.name(),PL))
        else:
            if N:
                I0 = (singular('%sI'%(self.prefix))+singular.ideal(['0']+FRS[:-N])).groebner()
            else:
                I0 = (singular('%sI'%(self.prefix))+singular.ideal(['0']+FRS)).groebner()
        if (self.Resl.coef()==2 and I0.dim()>N) or (self.Resl.coef()>2 and I0.GKdim()>N):
            coho_logger.info("Dimension %d > %d - The ring approximation is incomplete", self, I0.dim() if self.Resl.coef()==2 else I0.GKdim(),N)
            self.setprop('potential_bound',-1)
            return self.knownDeg + 1
        cdef int lastBoundFound = natBound
        for n from N >= n >= 1:
            tai = sum(DV[-n:])
            D = int(tai/n)  # replacements only make sense out to degree D
            for d from 2 <= d <= D:  # kill standard monomials of degree d
                                     # and generators whose degree devides d
                potBound = sum(DV[:-n]) + d*n - lenDV # natBound - tai + d*n
                if previous_bound and (potBound > previous_bound):
                    break
                if (potBound <= self.knownDeg) or ((d<=self.knownDeg) and forced): # it makes sense to try, or we *want* to try
                    J0 = singular.ideal(['0'])
                    for divis in Integer(d).divisors():
                        L=[X.name() for X in self.Gen if X.deg()==divis]
                        if L:
                            singular.eval('%s=%s+ideal(%s)'%(J0.name(), J0.name(), ','.join(L)))
                    I = I0 + J0   # now, the generators will be killed, and we proceed to add the standard monomials
                    for J in (self.StdMon.get(d,{})).values():
                        singular.eval('%s=%s+%s'%(I.name(), I.name(), J.name()))
                    G = I.groebner()
                    if int(singular.eval('vdim(%s)'%G.name()))>=0: #I.groebner().vdim()>=0: # we proved the existens of frHSOP
                        if (potBound <= self.knownDeg) and (forced!=2): # we are happy with that bound - return it!
                            singular.eval('degBound = %s'%(dgb))
                            self.setprop('WhatFRS',(n,d))
                            self.setprop('potential_bound',potBound)
                            return potBound
                        else:
                            if potBound<lastBoundFound:
                                lastBoundFound = potBound
                                self.setprop('WhatFRS',(n,d))
                                self.setprop('potential_bound',potBound)
            singular.eval("%s = %s,%s"%(I0.name(),I0.name(),FRS[-n])) # we can not replace FRS[-n], hence, it will be killed now
        from pGroupCohomology.modular_cohomology import MODCOHO
        if isinstance(self, MODCOHO) and FRS[:len(self.duflot_regular_sequence())]!=self.duflot_regular_sequence():
            I0 = (self.relation_ideal() + singular.ideal(self.duflot_regular_sequence())).groebner()
            degsum = sum([int(singular.eval('deg(%s)'%el)) for el in self.duflot_regular_sequence()]) - self.dimension()
            nb = self.dimension()-len(self.duflot_regular_sequence())
            for d from 1<=d<=self.knownDeg:
                if degsum+nb*d >= lastBoundFound:
                    break
                G = (I0 + singular.ideal(self.standard_monomials(d))).groebner()
                if int(singular.eval('vdim(%s)'%G.name()))>=0:
                    singular.eval('degBound = %s'%(dgb))
                    self.setprop('WhatFRS',(self.duflot_regular_sequence(),d))
                    self.setprop('potential_bound',degsum+nb*d)
                    return degsum+nb*d
        singular.eval('degBound = %s'%(dgb))
        return lastBoundFound  # sorry, but we found nothing better...

    @temporary_result
    def raw_filter_degree_type(self,FRS):
        r"""
        Test whether a given list of elements forms a filter-regular HSOP.

        INPUT:

        - ``FRS``: a list of strings defining elements of the cohomology ring

        OUTPUT:

        - ``None``, if the input is not a filter regular HSOP.
        - Otherwise, a triple of lists of numbers is returned:

          * The "raw filter degree type" of that HSOP
          * Data that are of internal use to compute the Poincaré series
          * The degree vector of the parameters.

        EXAMPLES:

        We first create a cohomology ring. For constructing Dickson classes,
        we use the elimination method.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, useElimination=True, from_scratch=True)
            sage: H.next()
            sage: H.next()
            sage: H.next()

        Of course, Dickson classes are not there, yet, so we construct them.
        ::

            sage: H.Dickson
            [None]
            sage: H.find_dickson()
            True
            sage: H.Dickson
            ['b_1_1+b_1_0']

        There is one Duflot regular class::

            sage: [X for X in H.Gen if X.rdeg()]
            [c_2_2: 2-Cocycle in H^*(D8; GF(2))]

        So, if the computation was complete, ``c_2_2`` and ``b_1_1+b_1_0``
        were a filter regular HSOP in degrees 2 and 1. This is indeed the
        case, as we verify now::

            sage: H.raw_filter_degree_type(['c_2_2','b_1_1+b_1_0'])
            ([-1, -1, 1], [[0], [0], [1, 1]], [2, 1])

        The raw filter degree type is the first item in the above triple.
        The filter degree type of that HSOP is now available::

            sage: H.filter_degree_type()
            [-1, -2, -2]

        Now, we try a slightly different sequence of elements::

            sage: H.raw_filter_degree_type(['c_2_2^2','b_1_0^2+b_1_1^2'])
            ([-1, -1, 4], [[0], [0], [1, 2, 2, 2, 1]], [4, 2])

        It is known that the filter degree type is the same for any filter
        regular HSOP. But apparently the *raw* filter degree type is
        different.

        """
        dgb=singular.eval("degBound")
        singular.eval("degBound = 0")
        self.set_ring()
        DV = [int(singular.eval('deg(%s)'%t)) for t in FRS]
        self.make_groebner()
        coho_logger.info("Test filter regularity", self)
        coho_logger.debug("Parameters: %s", self, repr(FRS))
        HV = is_filter_regular_parameter_system(self.prefix+'I', FRS)
        self.setprop('lastTested',self.knownDeg)
        if not HV:
            coho_logger.info("> Sequence is NOT filter regular. Sorry.", self)
            return None
        # rfdt = vector of maximal degrees in the kernel resp. quotient
        rfdt = []
        for X in HV:
            if X==[0]:
                rfdt.append(-1)
            else:
                rfdt.append(len(X)-1)
        fdt = FilterDegreeType(DV,rfdt)
        self.setprop('fdt',fdt)
        coho_logger.debug("  Raw filter degree type: %s"%repr(rfdt), self)
        coho_logger.info("  Filter degree type: %s"%repr(fdt), self)
        singular.eval("degBound = "+dgb)
        self.alpha = max([fdt[i]+i for i in range(len(fdt)-1)])
        return rfdt, HV, DV

    def SymondsTest(self, hsop,dv, forced=False):
        """
        Apply the Symonds test.

        INPUT:

        - ``hsop``: A list of strings defining a homogeneous system
          of parameters for the current ring approximation.
        - ``dv``: The degrees (list of integers) of ``hsop``.

        OUTPUT:

        - ``True``, ``False`` or ``None``, depending on whether the
          criterion proves completeness, the approximation is provably
          incomplete, or there is no conclusive application of the
          criterion possible yet.
        - The attribute ``_max_module_deg`` is set.

        ASSUMPTION:

        The ring approximation contains paramters for the cohomology
        ring.

        THEORY:

        By [Symonds]_, under the above assumption, the ring
        approximation is complete if it is known to a degree greater
        than the sum of the degrees in ``hsop`` minus their number,
        and the ring approximation is generated at most out to that
        degree as a module over the algebra generated by ``hsop``.

        NOTE:

        The method :meth:`test_for_completion` chooses between the
        modified Benson test and the Symonds test.

        EXAMPLES:

        We compute a cohomology ring out to degree 10, avoiding
        automatic application of the criterion.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(64,32, from_scratch=True)
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.next()
            sage: H.knownDeg
            10

        There are fairly small parameters::

            sage: H.parameters()
            ['c_4_11', 'b_2_3+b_2_2+b_2_1', 'b_2_2+b_2_1', 'b_1_1']
            sage: H.verify_parameters_exist()
            True

        The previous line asserts that the assumption of this criterion
        is satisfied. Indeed, the criterion applies::

            sage: H.SymondsTest(H.parameters(),[4,2,2,1])
            True

        As a module, the ring is generated in degree at most five::

            sage: H._max_module_deg
            5

        """
        try:
            N = sum([x-1 for x in dv])+1
            if (N > self.knownDeg) and not forced:
                return
            coho_logger.info( "Trying Symonds' criterion", self)
            self.set_ring()
            dgb = singular.eval('degBound')
            singular.eval('degBound=0')
            self.make_groebner()
            # The following was a bug in singular-3-1-1
            I = singular('std(%sI,ideal(%s))'%(self.prefix,','.join(hsop)))
#~             #Work-around was:
#~             gb_command = self._gb_command()
#~             I = singular('%s(%sI+ideal(%s))'%(gb_command, self.prefix,','.join(hsop)))
            if singular.eval('vdim(%s)'%I.name())=='-1':
                coho_logger.info("The ring approximation is not finite over the given parameters", self)
                return False
            M = max([Integer(singular.eval('deg(%s)'%t.name())) for t in I.kbase()])
            self.setprop('_max_module_deg',M)
            if self.knownDeg >=  max(M,N):
                self.completed = True
                self.suffDeg = max(M,N)
                self.setprop('_SymondsTestdata',hsop)
                return True
            else:
                coho_logger.info("Symmonds' criterion can only apply in degree %d", self, max(M,N))
        except KeyboardInterrupt:
            coho_logger.warning("Symonds' completeness test was interrupted.", self)

###################################################
###################################################
## Compute the visible ring structure
###################################################
###################################################

    ###########################
    ## get next degree:
    def next(self, Forced=False, KeepDecomposables=False):
        """
        Compute generators and relations up to the next unknown degree.

        TESTS:

        We first create a cohomology ring.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(8,3, useElimination=True, from_scratch=True)
            sage: print(H)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 0
            Minimal list of generators:
            []
            Minimal list of algebraic relations:
            []
            sage: H.next()
            sage: print(H)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 1
            Minimal list of generators:
            [b_1_0: 1-Cocycle in H^*(D8; GF(2)),
            b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            []
            sage: H.next()
            sage: print(H)
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 2
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
            b_1_0: 1-Cocycle in H^*(D8; GF(2)),
            b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        """
        ###########
        ## In order to have 100 percent doctest coverage
        ## for resolution.pyx, I remove liftAll from there
        ## and insert it as external function.
        cdef COCH X
        if self.SUBGPS:
            self.reconstructSubgroups()
        if self.completed and (not Forced) and (not self.ElAb):
            coho_logger.info("Complete ring structure has already been computed", self)
            return
        cdef RESL R
        R = self.Resl

        cdef Matrix_t *tmpMTX0
        cdef Matrix_t *tmpMTX
        cdef Matrix_t *tmpMTXout
        cdef MTX NilDec

        ############
        ## Compute next term of resolution, if necessary
        while R.Data.numproj <= self.knownDeg:
            R.nextDiff()
            if R.Data.numproj<=min(self._property_dict['auto'],max([1]+[X.deg() for X in self.Gen if X.rdeg()==0])):
                R.makeAutolift(R.Data.numproj)
        n = self.knownDeg + 1
        cdef int i,k,m,j
        cdef FEL fel, fel2
        cdef int lenDecGen,lenMonExp
        lenMonExp = 0
        cdef MTX template = None

        ######################################
        ## Main Procedure
        ######################################
        if self.ElAb:
            self.NilBasis[n]=[]
        ## Find decomposables and relations in degree n

        # The following keeps track about decomposable vector space generators of H^n
        cdef list VSGen=R.Data.projrank[n]*[1]
        cdef list DecGen=[]  # will be a triangular basis of the sub space of decomposables of H^n
        cdef list pivot=[]
        cdef COCH Cand, origCand # will be the 'next candidate' for a decomposable generator or a relation

        cdef list MonExp,lastPiv
        FfSetField(self.base_ring().order())
        previous_number_rels = len(self.Rel)
        if self.Gen!=[]:  # there can only be decomposables if there are generators, yet
            ####################################
            # We must lift self.RelG to the new degree.
            # First, switch to the previous ring
            singular.eval('setring %sr(%d)'%(self.prefix,n-1))
            if n==2:
                singular.eval('ideal %sI = std(0)'%(self.prefix))
            else:
                # At least for J3mod3, it is good to compute a complete GB
                # if there were no relations in the previous degree
                if (self.lastRel < n-1):
                    self.make_groebner()
                else:
                    self.make_groebner(n)
            sizeG = int(singular.eval('ncols(%sI)'%(self.prefix)))

            #######################################
            # Get standard monomials:
            self._makeStdMon(n,"Mon")

            if singular.eval('Mon[1]')!='0':
                coho_logger.info("We got %s standard monomials", self, singular.eval('ncols(Mon)'))
                # get list of exponent vectors of the standard monomials
                MonExp = [[int(y.strip()) for y in x.split(',')] for x in \
                          [s.strip() for s in (singular.eval('for (i=1;i<=ncols(Mon);i++) { print(leadexp(Mon[i]));print(\";\");}')+'\n').split(';')] if x]
                lenMonExp = len(MonExp)

                #######################################
                # Perform the products
                for i from 0<= i < lenMonExp:
                    coho_logger.debug('Monomial %d', self, i)
                    coho_logger.debug('> Candidate: %s', self, singular.eval('Mon[%d]'%(i+1)))
                    coho_logger.debug('> Express monomial as a Cochain', self)
                    Cand = self.MonToProd(MonExp[i])
                    if self.ElAb and (R.G_Alg.Data.p!=2) and (MonExp[i][self.firstOdd:].count(0) < (len(MonExp[i])-self.firstOdd)):
                        self.NilBasis[n].append(Cand.Data._rowlist_(0))
                    FfSetNoc(Cand.Data.Data.Noc)
                    j = FfFindPivot(Cand.Data.Data.Data, &fel)
                    IsMonomial = True
                    lenDecGen = len(DecGen)
                    if j>=0:
                        Cand = copy(Cand)
                        Cand.set_mtx_globals()
                        for k from 0 <= k < lenDecGen:
                            if (j <= pivot[k]):
                                fel2 = FfExtract(Cand.Data.Data.Data, pivot[k])
                                if fel2!=FF_ZERO:
                                    Cand.isubmul(DecGen[k], fel2)
                                    j = FfFindPivot(Cand.Data.Data.Data, &fel)
                                    IsMonomial = False
                                    if j<0:
                                        break
                    if j>=0: # We found a decomposable generator of H^n
                        coho_logger.debug('Decomposable cochain found\n', self)
                        DecGen.append(Cand/fel)
                        if len(DecGen[-1].name()) < 850:
                            singular.eval(('%sDG[%d]='%(self.prefix,len(DecGen)))+DecGen[-1].name())
                        else:
                            ComL = Cand.name().split('-(')
                            DGstr = '%sDG[%d]'%(self.prefix,len(DecGen))
                            singular.eval(DGstr+'='+ComL[0])
                            DGstr = DGstr + '=' + DGstr + '-('
                            for trm in ComL[1:]:
                                singular.eval(DGstr+trm)
                            singular.eval('%sDG[%d]=%sDG[%d]/%d'%(self.prefix,len(DecGen),self.prefix,len(DecGen),fel))
                        if not IsMonomial:
                            DecGen[-1].setname('%sDG[%d]'%(self.prefix,len(DecGen)))
                        pivot.append(j)
                        VSGen[j]=0
                    else: # We found a relation in degree n
                        self.lastRel = n
                        self.delprop('completeGroebner')
                        self.delprop('_current_parameters')
                        self.delprop('lastTested')
                        self.delprop('potential_bound')
                        sizeG+=1
                        if len(Cand.name()) < 850:
                            singular.eval(('%sI[%d] = '%(self.prefix,sizeG))+Cand.name())
                        else:
                            ComL = Cand.name().split('-(')
                            Idstr = '%sI[%d]'%(self.prefix,sizeG)
                            singular.eval(Idstr+'='+ComL[0])
                            Idstr = Idstr + '=' + Idstr + '-('
                            for trm in ComL[1:]:
                                singular.eval(Idstr+trm)
                        self.Rel.append(singular.eval('%sI[%d]'%(self.prefix,sizeG)))
                        coho_logger.debug('New relation found: %s\n', self, self.Rel[-1])
            else:
                coho_logger.info("There are no standard monomials in degree %d", self, n)

        ###################
        ## RESULT:
        ## I. COCH types
        ############
        ## lift restrictions
        ## Unfortunately, self.Resl must be lifted one step further
        ## in order to lift the restriction maps.

        cdef list NewGen = []
        cdef list CandL
        cdef PTR p_tmpX0
        NrNewGen = VSGen.count(1)
        if VSGen.count(1)==0:
            coho_logger.info("There is no new generator in degree %d", self, n)
        if NrNewGen>0:  # there are new ring generators, hence, we must lift the restriction maps
            self.delprop('completeGroebner')
            self.delprop('_small_last_parameter_attempted')
            self.delprop('_current_parameters')
            self.delprop('lastTested')
            self.delprop('potential_bound')
            if singular.eval("defined(%sQ)"%(self.prefix))=='1':
                singular.eval("kill %sQ"%(self.prefix))
            if self.RestrMaps:
                coho_logger.info("There are new generators, we have to lift the restriction maps", self)
            for sgp in (self.subgps or {}).values():
                while (sgp.knownDeg < n):
                    sgp.next(Forced=True,KeepDecomposables=True)
            while (R.Data.numproj <=n):
                R.nextDiff()
                # it seems that it doesn't help to make Autolift if there are many generators.
                # Degree 4 seems to be best, at least for groups of order 64
            # For technical reasons, we need to lift R out to degree n+1 if we want to
            # obtain new generators in degree n. But we only need the autolift out to
            # a degree in which generators live -- therefore R.Data.numproj-1
            if (R.Data.numproj<=self._property_dict['auto']+1) and (not R.Data.numproj-1 in R.Autolift):
                R.makeAutolift(R.Data.numproj-1)
            for NR, chm in self.RestrMaps.items():
                coho_logger.debug("Restriction to %s subgroup (order %s)", self, Integer(NR).ordinal_str(), chm[0][0])
                while(chm[1].knownDeg()<n):
                    chm[1].lift()
                if coho_options['sparse']:
                    import os
                    chm[1].exportData(os.path.join(self.inc_folder,self.GStem+'sg'+str(NR)+'_'))
            R.free_ugb()
        ###################
        ## CHOOSING NEW RING GENERATORS
        ##################
            if VSGen.count(1)==1:
                coho_logger.info("We have to choose 1 new generator in degree %d"%(n), self)
            else:
                coho_logger.info("We have to choose %d new generators in degree %d"%(VSGen.count(1),n), self)
        ## 1. New generators with nilpotent restriction on all
        ## maximal elementary abelian subgroups
        ## --> These are nilpotent!
            # VSGen: coeff == 0 => pivot of some decomposable class
            ZN_comp = len(VSGen)*[1] # eventually coeff == 0 => pivot of a decomposable nilpotent
                                    ## and ==2 => pivot of a new nilpotent generator
            if self.MaxelPos:
                # The following is a basis in echelon form of the subspace of decomposable nilpotent classes of degree n
                if DecGen: # there are decomposables, so let's intersect with the nilpotents:
                    X = DecGen[0]
                    tmpMTX0 = MatAlloc(X.Data.Data.Field, len(DecGen), X.Data.Data.Noc)
                    p_tmpX0 = tmpMTX0.Data
                    for X in DecGen:
                        memcpy(p_tmpX0, X.Data.Data.Data, FfCurrentRowSizeIo)
                        p_tmpX0 += FfCurrentRowSize
                    tmpMTX = nil_preimages([self.RestrMaps[mpos][1] for mpos in self.MaxelPos], list(DecGen))
                    tmpMTXout = MatMulStrassen(MatAlloc(R.G_Alg.Data.p, tmpMTX.Nor, tmpMTX0.Noc), tmpMTX, tmpMTX0)
                    NilDec = new_mtx(tmpMTXout, template)
                    template = NilDec
                    NilDec.echelonize()
                    FfSetNoc(NilDec.Data.Noc)
                    MatFree(tmpMTX0)
                    MatFree(tmpMTX)
                    for i in range(NilDec.nrows()):
                        j = FfFindPivot(MatGetPtr(NilDec.Data, i), &fel)
                        assert j>=0
                        ZN_comp[j]=0
                ## Now we compute a basis in echelon form of a complement of decomposable nilpotent classes in the nilpotent classes
                NilNonDec = new_mtx(nil_preimages([self.RestrMaps[mpos][1] for mpos in self.MaxelPos], [[n,i] for i in range(len(ZN_comp)) if ZN_comp[i]]), template)
                template = NilNonDec
                NilNonDec.set_immutable()
                # The rows of this matrix yield (ydeg=1,rdeg=0)-generators (i.e., nilpotent but nondecomposable classes).
                # We need to insert the normalised entries of NilNonDec at the places where ZN_comp has coefficient 1.
                for i in range(NilNonDec.nrows()):
                    CandL = []
                    NilL = NilNonDec._rowlist_(i)
                    for j in ZN_comp:
                        if j:
                            CandL.append(NilL.pop(0))
                        else:
                            CandL.append(0)
                    CandM = new_mtx(rawMatrix(R.G_Alg.Data.p, [CandL]), template)
                    template = CandM
                    CandM.set_immutable()
                    FfSetNoc(CandM.Data.Noc)
                    j = FfFindPivot(CandM.Data.Data, &fel)
                    assert j>=0
                    NewGen.append(COCH(self, n, 'a_%d_%d'%(n,j), CandM/fel, ydeg=1,rdeg=0, is_polyrep=True))  # a new normalised generator with nilpotent restriction
                    ZN_comp[j] = 2 # hence, the coeffs of NilL are still inserted in the right place, but it is clear
                                   # for later that there will be no new generator with that pivot
                NrNewGen = NrNewGen-ZN_comp.count(2)
                if ZN_comp.count(2)!=len(NewGen):
                    raise ArithmeticError("%d==%d -- that seems strange"%(ZN_comp.count(2),len(NewGen)))
                if len(NewGen)==1:
                    coho_logger.info("> There is 1 nilpotent generator in degree %d", self, n)
                else:
                    coho_logger.info("> There are %d nilpotent generators in degree %d", self, len(NewGen),n)

        ###########
        ## 2. New generators with nilpotent restriction on the
        ## greatest elementary abelian central subgroup
            RdegPiv = len(VSGen)*[1] # eventually, coeff will be 2 if there is a regular generator with that pivot
            if (self.CElPos in self.RestrMaps and NrNewGen):
                # The following is a basis in echelon form of the subspace of decomposable or nilpotent classes of degree n
                # which in addition have nilpotent restriction to the greatest central elementary abelian subgroup
                if DecGen or NewGen:
                    X = (DecGen or NewGen)[0]
                    tmpMTX0 = MatAlloc(X.Data.Data.Field, len(DecGen)+len(NewGen), X.Data.Data.Noc)
                    p_tmpX0 = tmpMTX0.Data
                    for X in DecGen:
                        memcpy(p_tmpX0, X.Data.Data.Data, FfCurrentRowSizeIo)
                        p_tmpX0 += FfCurrentRowSize
                    for X in NewGen:
                        memcpy(p_tmpX0, X.Data.Data.Data, FfCurrentRowSizeIo)
                        p_tmpX0 += FfCurrentRowSize
                    tmpMTX = nil_preimages([self.RestrMaps[self.CElPos][1]], DecGen+NewGen)
                    tmpMTXout = MatMulStrassen(MatAlloc(R.G_Alg.Data.p, tmpMTX.Nor, tmpMTX0.Noc), tmpMTX, tmpMTX0)
                    NilDec = new_mtx(tmpMTXout, template)
                    template = NilDec
                    NilDec.echelonize()
                    MatFree(tmpMTX0)
                    MatFree(tmpMTX)
                    FfSetNoc(NilDec.Data.Noc)
                    for i in range(NilDec.nrows()):
                        j = FfFindPivot(MatGetPtr(NilDec.Data, i), &fel)
                        assert j>=0
                        RdegPiv[j] = 0 # no regular element has that pivot, because some decomposables or nilpotents have
                NilNonDec = new_mtx(nil_preimages([self.RestrMaps[self.CElPos][1]], [[n,i] for i in range(len(ZN_comp)) if RdegPiv[i]]), template)
                template = NilNonDec
                NilNonDec.set_immutable()
                # The rows of this matrix yield (ydeg=rdeg=0)-generators (i.e., nondecomposable non-nilpotent classes with nilpotent restr. on CElAb).
                # We need to insert the normalised entries of NilNonDec at the places where RdegPiv has coefficient 1.
                loopbound = NilNonDec.nrows()
                for i from 0 <= i < loopbound:
                    CandL = []
                    k = 0
                    for j in RdegPiv:
                        if j:
                            CandL.append(NilNonDec[i,k])
                            k += 1
                        else:
                            CandL.append(0)
                    CandM = new_mtx(rawMatrix(R.G_Alg.Data.p, [CandL]), template)
                    CandM.set_immutable()
                    FfSetNoc(CandM.Data.Noc)
                    j = FfFindPivot(CandM.Data.Data, &fel)
                    assert j>=0
                    NewGen.append(COCH(self, n, 'b_%d_%d'%(n,j), CandM/fel, ydeg=0,rdeg=0, is_polyrep=True))  # a new normalised generator with nilpotent restriction on CElAb
                    RdegPiv[j] = 2 # hence, the coeffs of NilL are still inserted in the right place, but it is clear
                                   # for later that there will be no regular generator with that pivot
                if RdegPiv.count(2)==1:
                    coho_logger.info('> There is 1 "boring" generator in degree %d', self, n)
                else:
                    coho_logger.info('> There are %d "boring" generators in degree %d', self, RdegPiv.count(2),n)
                NrNewGen = NrNewGen - RdegPiv.count(2)

        ###########
        ## 3. Regular generators (rdeg=1, ydeg=0)
            if NrNewGen:
                LastPiv = len(VSGen)*[1] # coeff will remain 0 for the pivots of regular generators
                if DecGen or NewGen:
                    X = (DecGen or NewGen)[0]
                    tmpMTX0 = MatAlloc(X.Data.Data.Field, len(DecGen)+len(NewGen), X.Data.Data.Noc)
                    p_tmpX0 = tmpMTX0.Data
                    for X in DecGen:
                        memcpy(p_tmpX0, X.Data.Data.Data, FfCurrentRowSizeIo)
                        p_tmpX0 += FfCurrentRowSize
                    for X in NewGen:
                        memcpy(p_tmpX0, X.Data.Data.Data, FfCurrentRowSizeIo)
                        p_tmpX0 += FfCurrentRowSize
                    NilDec = new_mtx(tmpMTX0, template)
                    template = NilDec
                    NilDec.echelonize()
                    NilDec.set_immutable()
                    FfSetNoc(NilDec.Data.Noc)
                    p_tmpX0 = NilDec.Data.Data
                    for i in range(NilDec.nrows()):
                        j = FfFindPivot(p_tmpX0, &fel)
                        assert j>=0
                        p_tmpX0 += FfCurrentRowSize
                        LastPiv[j] = 0
                if (R.G_Alg.Data.p!=2) and (n%2): # this can only happen for abelian groups
                    NewGen.extend([self.standardCochain(n, i, ydeg=1,rdeg=0,name='a') for i in range(len(LastPiv)) if LastPiv[i]])
                    if LastPiv.count(1)!=NrNewGen:
                        raise ArithmeticError("%d==%d -- that seems strange"%(LastPiv.count(1),NrNewGen))
                    if LastPiv.count(1)==1:
                        coho_logger.info("> There is 1 nilpotent generator in degree %d", self, n)
                    else:
                        coho_logger.info("> There are %d nilpotent generators in degree %d", self, LastPiv.count(1),n)
                else:
                    NewGen.extend([self.standardCochain(n, i, ydeg=0, rdeg=1) for i in range(len(LastPiv)) if LastPiv[i]])
                    if LastPiv.count(1)!=NrNewGen:
                        raise ArithmeticError("%d==%d -- that seems strange"%(LastPiv.count(1),NrNewGen))
                    if LastPiv.count(1)==1:
                        coho_logger.info("> There is 1 Duflot regular generator in degree %d", self, n)
                    else:
                        coho_logger.info("> There are %d Duflot regular generators in degree %d", self, LastPiv.count(1),n)
        ## Insert the new generators:
        previous_number_gens = len(self.Gen)
        if self.ElAb and (R.G_Alg.Data.p!=2) and (n%2):
            self.NilBasis[n].extend([Ca.MTX()._rowlist_(0) for Ca in NewGen])
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

        coho_logger.info("Summary: %d relations and %d generators in degree %d", self, len(self.Rel)-previous_number_rels, len(self.Gen)-previous_number_gens, n)
        assert lenMonExp == len(DecGen)+len(self.Rel)-previous_number_rels, "Relation/Monomial count is wrong, we started with {} monomials".format(lenMonExp)
        assert R.rank(n) == len(DecGen)+len(self.Gen)-previous_number_gens, "Expected dimension {}, got {}+{}".format(R.rank(n), len(DecGen), len(self.Gen)-previous_number_gens)

        self.knownDeg=n
        if (KeepDecomposables) and (self.knownDeg > 1):
            singular.eval('setring %sr(%d)'%(self.prefix,self.knownDeg-1))
                              # The matrix DG in singular was to save name length. But we wouldn't save DG
            for X in DecGen:  # Hence: We need to change the names into clear names.
                X.setname(singular.eval(X.Name))
        ###################
        ## We can not simply extend self.Triangular by NewGen, since they are in general not triangular
        if (VSGen.count(1)>0):
            for Cand in NewGen:
                FfSetNoc(Cand.Data.Data.Noc)
                j = FfFindPivot(Cand.Data.Data.Data, &fel)
                lenDecGen = len(DecGen)
                if j>=0:
                    Cand = copy(Cand)
                    Cand.set_mtx_globals()
                    for k from 0 <= k < lenDecGen:
                        if (j <= pivot[k]):
                            fel2 = FfExtract(Cand.Data.Data.Data, pivot[k])
                            if fel2!=FF_ZERO:
                                Cand.isubmul(DecGen[k], fel2)
                                j = FfFindPivot(Cand.Data.Data.Data, &fel)
                                assert j>=0
                    DecGen.append(Cand/fel)
                    pivot.append(j)
        self.Triangular[n]=list(DecGen)
        ####################
        ## II. put the new generators into the dictionary of monomials and lifts
        for i from 0 <= i < len(self.Gen):
            self.Monomials[self.Gen[i].name()] = self.Gen[i]
            R.setLift(self.Gen[i],2*(self.Gen[i].deg()))

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
        if R.G_Alg.Data.p!=2:   # non-commutative case
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
            for ITEM in self.StdMon[i].items():
                self.StdMon[i][ITEM[0]]=singular('%sr(%d)'%(self.prefix,n-1)).imap(ITEM[1])
        # ... and don't forget that the new generators are standard monomials!
        for X in self.Gen:
            if X.Deg==n:
                self.StdMon[n][X.Name]=singular.ideal(X.Name)
        if n>1:
            singular.eval('ideal %sI = imap(%sr(%d),%sI)'%(self.prefix,self.prefix,n-1,self.prefix))
            # keep track of decomposable generators --
            # We need them for lifting the Dickson invariants!
            singular.eval('ideal %sDG = imap(%sr(%d),%sDG)'%(self.prefix,self.prefix,n-1,self.prefix))
        else:
            singular.eval('ideal %sI'%(self.prefix))
        if KeepDecomposables:
            self.GenS = singular('%sr(%d)'%(self.prefix,n))
            self.RelG = [s.strip() for s in singular.eval('print(%sI)'%(self.prefix)).split(',')]

        #####################################
        ## try and lift Dickson invariants...
        # ... unless the group is abelian or we use elimination
        if (self.pRank) and (self.CenterRk) and (not self.useElimination):
            m = self.pRank-self.CenterRk
            Ddg = Integer(R.G_Alg.Data.p)**m
            if R.G_Alg.Data.p==2:
                switch=1
            else:
                switch=2
            for i from 0<i<=m:
                if self.Dickson[i-1] is None:
                    j=0
                    while(1):
                        if self.knownDeg < (switch*(Ddg - Integer(R.G_Alg.Data.p)**(m-i)))*(Integer(R.G_Alg.Data.p)**j):
                            break
                        if self.knownDeg == (switch*(Ddg - Integer(R.G_Alg.Data.p)**(m-i)))*(Integer(R.G_Alg.Data.p)**j):
                            PotentialDicksonLift = self.lift_dickson(i-1,j)
                            if isinstance(PotentialDicksonLift,COCH):
                                if self.useFactorization:
                                    self.Dickson[i-1] = self.small_factor(self.element_as_polynomial(PotentialDicksonLift))
                                else:
                                    self.Dickson[i-1] = self.element_as_polynomial(PotentialDicksonLift).name()
                            break
                        j+=1
        singular.eval('ideal %sDG'%self.prefix) # because previously, DG was a copy of the decomposable classes from r(n-1)
        #####################
        ## Empty the dustbin!
        if n>1:
            singular.eval('setring %sr(%d)'%(self.prefix,n-1))
            singular.eval('kill %sI'%(self.prefix))
            singular.eval('kill %sDG'%self.prefix)
            singular.eval('kill Mon')
            singular.eval('setring %sr(%d)'%(self.prefix,n))
            singular.eval('kill %sr(%d)'%(self.prefix,n-1))
        if not KeepDecomposables:
            self.Triangular.pop(n)

        coho_logger.info("Ring approximation computed out to degree %d!", self, n)
        if coho_options['save']:
            coho_logger.info("Storing approximation data", self)
            safe_save(self, self.autosave_name())

    #########################
    ## make the complete ring
    ## resp. up to a certain degree
    def make (self, max_deg=-1):
        """
        Construct the visible ring structure.

        INPUT:

        - ``max_deg`` (optional positive integer): compute the complete
          ring structure at most up to degree ``max_deg``. The default
          is a *complete* computation.

        TESTS:

        We first create a cohomology ring.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.doctest_setup()       # reset, block web access, use temporary workspace
            sage: H = CohomologyRing(32,5, from_scratch=True)
            sage: H.make(2)
            sage: print(H)
            Cohomology ring of Small Group number 5 of order 32 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 2
            Minimal list of generators:
            [a_2_1: 2-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             c_2_2: 2-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             c_2_3: 2-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             b_1_1: 1-Cocycle in H^*(SmallGroup(32,5); GF(2))]
            Minimal list of algebraic relations:
            [a_1_0^2,
             a_1_0*b_1_1]
            sage: H.make()
            sage: print(H)
            Cohomology ring of Small Group number 5 of order 32 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [a_2_1: 2-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             c_2_2: 2-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             c_2_3: 2-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(32,5); GF(2)),
             b_1_1: 1-Cocycle in H^*(SmallGroup(32,5); GF(2))]
            Minimal list of algebraic relations:
            [a_1_0^2,
             a_1_0*b_1_1,
             a_2_1*a_1_0,
             a_2_1^2]

        """
        if max_deg == 0:
            return
        cdef RESL R = self.Resl
        if (not (isinstance(max_deg, int) or isinstance(max_deg, Integer))) or \
           (max_deg==0) or (max_deg<-1):
            raise IndexError("The degree bound must be a positive integer")
        if self.ElAb:
            if max_deg == -1:
                while self.knownDeg < 2:
                    self.next(KeepDecomposables=True)
            else:
                while self.knownDeg < min(2,max_deg):
                    self.next(KeepDecomposables=True)
            if self.knownDeg >= 2:
                self.completed = True
            return
        if ((self.suffDeg>-1) and (self.knownDeg >= self.suffDeg)) or self.completed:
            coho_logger.info("Complete ring structure has already been computed", self)
            return
        if (max_deg!=-1) and (max_deg <= self.knownDeg):
            coho_logger.info('The ring is already known up to degree %d', self, self.knownDeg)
            return
        if ((max_deg > 1) or (max_deg==-1)) and self.group_is_abelian():
            self.suffDeg = 2
        elif ((max_deg > 3) or (max_deg==-1)) and (self.pRank==1):
            self.suffDeg = 4
        if self.suffDeg == -1:
            coho_logger.info("We have no degree bound yet", self)
        else:
            coho_logger.info("We have the degree bound %d", self, self.suffDeg)
        if max_deg>0:
            coho_logger.info("We will compute at most up to degree %d",self, max_deg)
        while (1):
            coho_logger.info('Start computation in Degree %d', self, self.knownDeg+1)
            self.next(KeepDecomposables = self.KeepBases)
            self.test_for_completion()
            if (self.completed) or ((max_deg!=-1) and (self.knownDeg>=max_deg)):
                break
        # Catch the case of generalized quaternion groups:
        if self.completed and self.pRank==1:
            if not self.raw_filter_degree_type([X.name() for X in self.Gen if X.rdeg()]):
                raise RuntimeError("theoretical error")
        self.GenS = singular('%sr(%d)'%(self.prefix,self.lastRelevantDeg or self.knownDeg))
        self.set_ring()
        if not self.MaxelPos:
            self.make_groebner()
        self.RelG = [s.strip() for s in singular.eval('print(%sI)'%(self.prefix)).split(',')]
        coho_logger.info("Finished computation of the ring structure", self)
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
            coho_logger.info("Storing approximation data", self)
            safe_save(self, self.autosave_name())

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
r"""
Minimal Free `\mathbb F_p` Resolutions of Finite `p`-Groups.

AUTHORS:

- Simon King <simon.king@uni-jena.de> (Cython code)
- David J. Green <david.green@uni-jena.de> (underlying C-code)

"""

from __future__ import print_function, absolute_import

import sage
import sage.all
import inspect
from sage.all import cputime
from sage.all import walltime
import sys
import os
from sage.all import Integer
from sage.all import FiniteField as GF
from sage.all import Matrix
from sage.matrix.matrix_space import MatrixSpace
from sage.all import copy
from sage.all import deepcopy
from sage.all import load
from sage.env import DOT_SAGE, SAGE_ROOT, SAGE_LOCAL

from pGroupCohomology.auxiliaries import gap, singular, coho_options, _gap_init, coho_logger, safe_save
from pGroupCohomology.cochain cimport YCOCH
from pGroupCohomology.cochain cimport COCH

from libc.string cimport memcpy
from cysignals.memory cimport sig_free
from cysignals.signals cimport sig_check, sig_on, sig_off
#~ include 'sage/ext/stdsage.pxi'

from sage.matrix.matrix_gfpn_dense cimport Matrix_gfpn_dense as MTX
from sage.matrix.matrix_gfpn_dense cimport FieldConverter_class, FieldConverter
from sage.matrix.matrix0 cimport Matrix as Matrix0

####################
## MTX related auxiliary functions
cdef MTX makeMTX(Matrix_t *Data):
    """
    Make a mutable MTX-matrix out of the genuine MeatAxe-type <Matrix_t>.

    We can hardly test this method, since this cdef'd function and
    the MeatAxe-types can not be imported in Python. So, we only device
    an indirect test.

    EXAMPLES:

    The example produces files. For safety reasons, we choose files
    in a temporary directory; it will be removed as soon as Sage is quit.
    First, we create the basic data for the dihedral group of order 8
    (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

        sage: tmp_root = tmp_dir()
        sage: from pGroupCohomology.resolution import makeGroupData, RESL
        sage: makeGroupData(8,3,folder=tmp_root)
        sage: gstem='8gp3'
        sage: gps_folder=os.path.join(tmp_root,gstem)
        sage: res_folder=os.path.join(gps_folder,'dat')
        sage: R = RESL(gstem,gps_folder,res_folder)
        sage: R.firstDiff()   # indirect doctest
        sage: R
        Resolution of GF(2)[8gp3]
        sage: print(R)
        Resolution:
        0 <- GF(2) <- GF(2)[8gp3] <- rank 2

    """
    cdef MTX M = MTX.__new__(MTX)
    BR = GF(Data.Field, 'x')
    M._parent = MatrixSpace(BR, Data.Nor, Data.Noc, implementation=MTX)
    M._ncols  = Data.Noc
    M._nrows  = Data.Nor
    M._base_ring = BR
    M._converter = <FieldConverter_class>FieldConverter(BR)
    M.Data=Data
    return M

def baseMTX(f, m,n, i,j):
    r"""
    Return an immutable :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix with a single mark ``1``.

    INPUT:

    - ``f`` -- integer, the field size.
    - ``m``, ``n`` -- integers, row and column number.
    - ``i``, ``j`` -- integers, position of the single mark ``1``.

    OUTPUT:

    An immutable `(m\times n)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix
    over `GF(f)` with a single entry ``1`` at `(i,j)`

    EXAMPLE::

        sage: from pGroupCohomology.resolution import baseMTX
        sage: baseMTX(3, 4, 5, 1, 2)
        [0 0 0 0 0]
        [0 0 1 0 0]
        [0 0 0 0 0]
        [0 0 0 0 0]

    """
    cdef MTX M
    M = MTX(MatrixSpace(GF(f,'x'), m,n, implementation=MTX))
    M[i,j]=1
    M.set_immutable()
    return M

####################
## Group data related auxiliary functions

def makeGroupData(q,n, folder, ElAb=False,Forced=False):
    r"""
    Create basic data files the cohomology computation of ``SmallGroup(q,n)``.

    INPUT:

    - ``q`` -- the order of some finite `p`-group `G`
    - ``n`` -- the number of the group in the SmallGroups library
    - ``folder`` -- name of a directory in which the data files will be stored.
      The directory will be created, if necessary.
    - ``ElAb`` (optional bool, default False) -- indicates whether the
      group is elementary abelian.
    - ``Forced`` (optional bool, default False) -- if True, force
      recomputation.

    OUTPUT:

    Various files will be created in subdirectories of the specified folder.
    These files provide information needed to construct a minimal projective
    resolution of the group, using David Green's programs.

    ALGORITHM:

    This function is based on Gap functions written by David Green.

    - First, it is checked whether there already are certain files in the
      specified directory. If they are, nothing is done, unless the optional
      argument ``'forced'`` is True. The present data are not checked for
      consistency. So, if data are corrupted, one may empty the folder
      or simply specify ``'forced=True'``).
    - Minimal generators for the group are computed, giving rise to a
      certain basis of the group algebra `\mathbb F_pG`.
    - The matrices for left and right action of `G` on the group algebra
      are computed.
    - The greatest central elementary abelian subgroup of `G` and
      representatives for the conjugacy classes of maximal elementary
      abelian subgroups of `G` are computed.

    The data are stored in files.

    EXAMPLES:

    This example produces files. For safety reasons, we choose files
    in a temporary directory; it will be removed as soon as Sage is quit.
    We construct the data for the dihedral group of order 8, which is
    number 3 in the SmallGroups library. For illustration, we use logging::

        sage: tmp_root = tmp_dir()
        sage: from pGroupCohomology.resolution import makeGroupData, coho_logger
        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.global_options('info')
        sage: makeGroupData(8,3,folder=tmp_root)
        Computing basic setup for Small Group number 1 of order 2
        Computing basic setup for Small Group number 2 of order 4
        Computing basic setup for Small Group number 3 of order 8
        sage: CohomologyRing.global_options('warn')

    The files defining the basis for the group algebra of the dihedral group
    and its special subgroups are located in subfolders of ``tmp_root``, whose
    name are given by the order and the SmallGroups library number of the
    respective group. We call this the stem folder of the group.
    It looks like this::

        sage: f = open(os.path.join(tmp_root,'8gp3','8gp3.nontips'))
        sage: print(f.read())
        2 8 4 3 2 R
        (1);
        a;
        b;
        ab;
        ba;
        aba;
        bab;
        baba;
        sage: f.close()
        sage: f = open(os.path.join(tmp_root,'4gp2','4gp2.nontips'))
        sage: print(f.read())
        2 4 2 3 2 R
        (1);
        a;
        b;
        ba;
        sage: f.close()

    Other files, contained in the sub-directory 'sgp' of the stem folder,
    describe the embedding of the elementary abelian subgroups. The first
    subgroup will always be the greatest central elementary abelian.
    Here is a matrix defining the embedding of the third special subgroup,
    which is elementary abelian of order 4. The matrix is a MeatAxe matrix
    (see :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense`).
    ::

        sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
        sage: M = MTX(os.path.join(tmp_root,'8gp3','sgp','8gp3sg3.ima'))
        sage: print(M)
        [1 0 0 0 0 0 0 0]
        [0 0 0 1 1 1 1 1]
        [0 1 0 0 0 0 0 0]
        [0 0 0 0 0 1 0 1]
        sage: CohomologyRing.reset()

    """
    import os
    _gap_init()
    if q==1:
        return
    F=Integer(q).factor()
    if len(F)>1:
        raise ValueError("The group order must be a prime power")
    if not ElAb:  # we will create data for all smaller elementary abelian groups
        for i in xrange(1,F[0][1]):
            makeGroupData(F[0][0]**i, Integer(gap('NumberSmallGroups(%d)'%(F[0][0]**i))), folder, True, Forced)
    GStem = str(q)+'gp'+str(n)
    if folder == '':
        gps_folder = GStem
    else:
        gps_folder = os.path.join(folder, GStem)
    if os.access(os.path.join(gps_folder,GStem+'.nontips'),os.R_OK):
        if Forced:
            coho_logger.info("Forcing recomputation of group data for %s",None,GStem)
        else:
            return
    coho_logger.info( "Computing basic setup for Small Group number %d of order %d"%(n,q), None)
    ## clean the folder, in order to avoid being asked questions...
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch.gz'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.gens'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.gens.gz'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.lgens'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.lgens.gz'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch.gz'))
    except OSError:
        pass
    ## finally, construct the data
    gap.eval('makeThisSmallGroup([%d,%d],"%s")'%(q,n,folder))
    # there seems to be a racing condition when creating the .ima files,
    # which becomes immanent when doing parallel tests. So,
    # we verify that the files are OK before returning.
    # 1. test if the sgs is there. If it isn,t then it is safe to think
    # that we have an (elementary) abelian group.
    inc_folder = os.path.join(gps_folder,'sgp')
    try:
        L = gap('ReadAsFunction("%s")()'%(os.path.join(inc_folder,GStem+'.sgs')))
    except TypeError:  # can't be loaded
        return
    NumSubgps = Integer(L[1])
    for sg in range(1,NumSubgps+1):
        cr = 0
        filename = os.path.join(inc_folder,GStem+'sg%d.ima'%sg)
        while(1):
            cr += 1
            if cr >= 1000000:
                raise IOError('File "%s" has not been created')
            M = MTX(filename)
            if M.ncols():  # finally the file is written!
                break

def makeSpecialGroupData(H, GStem, folder):
    """
    Creating data files for computing the cohomology of a finite `p`-Group.

    INPUT:

    - ``H`` -- a finite `p`-group defined in the Gap interface
    - ``GStem`` -- a string, providing a short and unique descriptor of ``H``
    - ``folder`` (optional string) -- name of a directory in which
      the data files will be stored. The directory will be created, if necessary.

    OUTPUT:

    See :func:`~pGroupCohomology.resolution.makeGroupData`

    NOTE:

    In contrast to  :func:`~pGroupCohomology.resolution.makeGroupData`,
    this function does not have an optional argument ``forced``. So,
    if corrupted data are present for the given folder and the given
    ``GStem``, they must be removed before invoking ``makeSpecialGroupData``.

    ALGORITHM:

    See :func:`~pGroupCohomology.resolution.makeGroupData`

    EXAMPLES:

    This example produces files. For safety reasons, we choose files
    in a temporary directory; it will be removed as soon as Sage is quit.
    We construct the data for the dihedral group of order 8. In contrast
    to the example for makeGroupData, we define it directly in the Gap
    interface::

        sage: G = gap('DihedralGroup(8)')
        sage: GStem = 'DihedralGroup'
        sage: tmp_root = tmp_dir()
        sage: from pGroupCohomology.resolution import makeGroupData, makeSpecialGroupData, coho_logger

    Again, we log the computation.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.global_options('info')
        sage: makeSpecialGroupData(G,GStem,folder=tmp_root)
        Computing basic setup for Small Group number 1 of order 2
        Computing basic setup for Small Group number 2 of order 4
        Computing basic setup for DihedralGroup
        sage: CohomologyRing.global_options('warn')

    Now, all data concerning G are in subfolders of the stem folder of G,
    which is ``os.path.join(tmp_root,GStem)``. Also the file names make use of
    the given GStem. Here are the contents, analogous to the example of
    :func:`~pGroupCohomology.resolution.makeGroupData`::

        sage: f = open(os.path.join(tmp_root,GStem,GStem+'.nontips'))
        sage: print(f.read())
        2 8 4 3 2 R
        (1);
        a;
        b;
        ba;
        bb;
        bba;
        bbb;
        bbba;
        sage: import os
        sage: sorted(os.listdir(os.path.join(tmp_root,GStem,'sgp')))
        ['DihedralGroup.sgs',
         'DihedralGroupsg1.ima',
         'DihedralGroupsg1.irg',
         'DihedralGroupsg2.ima',
         'DihedralGroupsg2.irg',
         'DihedralGroupsg3.ima',
         'DihedralGroupsg3.irg']
        sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
        sage: M = MTX(os.path.join(tmp_root,GStem,'sgp',GStem+'sg3.ima'))
        sage: print(M)
        [1 0 0 0 0 0 0 0]
        [0 0 0 0 1 0 0 0]
        [0 1 1 1 0 0 0 0]
        [0 0 0 0 0 1 1 1]
        sage: CohomologyRing.reset()

    Note that the result is different from the result obtained with
    ``makeGroupData(8,3)`` (see
    :func:`~pGroupCohomology.resolution.makeGroupData`): We consider
    two *different* presentations of the dihedral group, so the output
    is not necessarily identical (but certainly isomorphic).

    """
    import os
    q = Integer(H.parent().eval('Order(%s)'%(H.name())))
    if folder == '':
        gps_folder = GStem
    else:
        gps_folder = os.path.join(folder,GStem)
    if q==1:
        return
    F=Integer(q).factor()
    if len(F)>1:
        raise ValueError("The group order must be a prime power")
    for i in xrange(1,F[0][1]):
        makeGroupData(F[0][0]**i, Integer(gap('NumberSmallGroups(%d)'%(F[0][0]**i))), folder, True)
    _gap_init(H.parent())
    coho_logger.info( "Computing basic setup for %s"%(GStem),None)
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch.gz'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.gens'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.gens.gz'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.lgens'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.lgens.gz'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch'))
    except OSError:
        pass
    try:
        os.remove(os.path.join(gps_folder,GStem+'.bch.gz'))
    except OSError:
        pass
    ## finally, construct the data
    H.parent().eval('makeThisGroup(%s,"%s","%s")'%(H.name(),GStem,folder))
    # there seems to be a racing condition when creating the .ima files,
    # which becomes immanent when doing parallel tests. So,
    # we verify that the files are OK before returning.
    import os
    from sage.all import sleep
    # 1. test if the sgs is there. If it isn,t then it is safe to think
    # that we have an (elementary) abelian group.
    inc_folder = os.path.join(gps_folder,'sgp/')
    try:
        L = gap('ReadAsFunction("%s")()'%(os.path.join(inc_folder,GStem+'.sgs')))
    except TypeError:  # can't be loaded
        return
    NumSubgps = Integer(L[1])
    for sg in range(1,NumSubgps+1):
        filename = os.path.join(inc_folder,GStem+'sg%d.ima'%sg)
        M = MTX(filename)
        if not M.ncols():
            sleep(1)
            M = MTX(filename)
            if not M.ncols():
                raise IOError, 'File "%s" has not been created'%filename

#####################################################################
#####################################################################
## Extension type for resolutions
#####################################################################
#####################################################################

## Unpickling

class RESL_sparse_unpickle_class:
    """
    Used for unpickling class instances of :class:`~pGroupCohomology.resolution.RESL`.

    EXAMPLES:

    The examples produce files. For safety reasons, we choose
    files in a temporary directory; it will be removed as soon
    as Sage is quit.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: tmp_root = tmp_dir()
        sage: CohomologyRing.set_user_db(tmp_root)
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: R = H.resolution()
        sage: print(R)
        Resolution:
        0 <- GF(2) <- GF(2)[D8] <- rank 2 <- rank 3 <- rank 4
        sage: R == loads(dumps(R))   # indirect doctest
        True
        sage: R is loads(dumps(R))
        False

    """
    def __init__(self):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: R = H.resolution()
            sage: R
            Resolution of GF(2)[D8]
            sage: R == loads(dumps(R))   # indirect doctest
            True
            sage: R is loads(dumps(R))
            False

        """
        self.__safe_for_unpickling__ = True
    def __call__(self,gstem,gps_folder,res_folder,degree,Lifts,Autolift,Action, ROOT = None):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,2)
            sage: H.make()
            sage: R = H.resolution()
            sage: R
            Resolution of GF(2)[SmallGroup(8,2)]
            sage: R == loads(dumps(R))   # indirect doctest
            True
            sage: R is loads(dumps(R))
            False

        """
        #print "unpickle:",gstem,gps_folder,res_folder,degree, ROOT
        ## First, we check whether a re-rooting occurs
        oldroot = coho_options.get('@oldroot@',None)
        if isinstance(oldroot,basestring):
            # Our folders are not supposed to be symlinks.
            # Hence, here it is realpath
            oldroot = os.path.realpath(oldroot)
        newroot = coho_options.get('@newroot@',None)
        if isinstance(newroot, basestring):
            newroot = os.path.realpath(newroot)
        gps_folder = os.path.realpath(gps_folder)
        res_folder = os.path.realpath(res_folder)
        # This is the root that was saved:
        r = os.path.realpath(os.path.split(gps_folder)[0])
        # We have a special treatment for the public and the private cohomology data base:
        if ROOT is not None:
            from pGroupCohomology.cohomology import COHO
            if ROOT == '@user_db@':
                newroot = newroot or COHO.user_db
                oldroot = r
            elif ROOT == '@public_db@':
                newroot = newroot or COHO.public_db
                oldroot = r
        if (newroot is not None):
            if oldroot is not None and (r!=oldroot) and (r!=newroot):
                raise RuntimeError("Unpickling failed since the parameter '@oldroot@' was incorrectly used")
            if r == newroot: # hence, no change is needed.
                # By removing @newroot@, we declare that self doesn't need to be saved
                if coho_options.has_key('@newroot@'):
                    del coho_options['@newroot@']
            else:
                gps_folder = os.path.join(newroot, os.path.split(gps_folder)[1])
                res_folder = os.path.join(gps_folder, os.path.split(res_folder)[1])
        cdef RESL OUT
        OUT = RESL(gstem,gps_folder,res_folder)
        cdef dict opts = dict(coho_options)
        coho_options['save']=False
        coho_options['reload']=True
        while OUT.deg() < degree:
            OUT.nextDiff()
        coho_options.clear()
        coho_options.update(opts)
        cdef list tmp
        if isinstance(Lifts,dict):
            if Lifts == {1:1}:
                tmp = load(os.path.join(res_folder,'L'+gstem+'.sobj'))  # realpath here?
                for X,Y in tmp:
                    if isinstance(Y,basestring):
                        if (newroot is not None):
                            Y = os.path.join(newroot,os.path.split(res_folder)[1], os.path.split(Y)[1])
                    OUT.Lifts[X]=Y
            else:
                for X,Y in Lifts.items(): # we have very old data format
                    OUT.Lifts[(X[0],X[1].deg(),X[1].MTX())] = Y
        else:
            for X,Y in Lifts:
                if isinstance(Y,basestring):
                    if newroot is not None:
                        Y =  os.path.join(newroot,os.path.split(res_folder)[1], os.path.split(Y)[1])
                    OUT.Lifts.Data[X]={1:Y}
                else:
                    OUT.Lifts[X]=Y
        # Neu: Autolift ist dict, nicht list
        if isinstance(Autolift,dict):
            OUT.Autolift = Autolift
            if isinstance(OUT.Autolift.get('Piv',None), list):
                OUT.Autolift['Piv'] = tuple(OUT.Autolift['Piv'])
        else:
            OUT.Autolift = {}
            for X in xrange(1,len(Autolift)):
                OUT.Autolift[X] = {}
                for Y in Autolift[X].keys():
                    OUT.Autolift[X][Y] = Autolift[X][Y]
            if isinstance(OUT.Autolift.get('Piv',None), list):
                OUT.Autolift['Piv'] = tuple(OUT.Autolift['Piv'])
        OUT.Action = Action
        OUT.exportAction()
        return OUT

resl_sparse_unpickle = RESL_sparse_unpickle_class()


cdef class RESL:
    r"""
    Computating minimal projective resolutions for finite `p`-groups with coefficients in ``GF(p)``.

    INPUT:

    - ``gstem`` -- a string, providing a short unique descriptor of a finite
      `p`-group (see :func:`~pGroupCohomology.resolution.makeSpecialGroupData`)
    - ``gps_folder`` (optional) -- a string, defining the folder in which data
      for the group specified by ``gstem`` can be found. Default: ``gps_folder=''``
    - ``res_folder`` (optional) -- a string, defining the folder in which the
      data for the resolution will be stored. Default: ``res_folder=''``

    NOTE:

    - Usually, one wouldn't create an instance of RESL on its own. The normal
      usage is to create a cohomology ring by :func:`~pGroupCohomology.CohomologyRing`,
      which internally will produce an instance of RESL.

    OUTPUT:

    A resolution, which is given by data files in ``res_folder``, where the
    file names start with ``'Res'+gstem``.

    EXAMPLES:

    Usually, objects of type RESL will only play a role when computing
    a cohomology ring. But as such, they are hardly visible, and will
    hardly ever be directly used. Nevertheless, we hope that the following
    examples give some insight on how the RESL class works.

    **Creating a RESL object**

    The examples produce files. For safety reasons, we choose files in
    a temporary directory; it will be removed as soon as Sage is quit.
    First, we create the basic data for the dihedral group of order 8
    (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

        sage: tmp_root = tmp_dir()
        sage: from pGroupCohomology.resolution import makeGroupData, RESL, coho_logger
        sage: makeGroupData(8,3,folder=tmp_root)

    The ``gstem`` is ``'8gp3'``, so, the group data are stored in the folder
    ``os.path.join(tmp_root,'8gp3')``, to which we refer as the stem
    folder. The function :func:`~pGroupCohomology.resolution.makeGroupData`
    also creates a subdirectory ``'dat'`` of the stem folder, which is
    intended to be used for storing the resolution.  ::

        sage: gstem='8gp3'
        sage: gps_folder = os.path.join(tmp_root,gstem)
        sage: res_folder = os.path.join(gps_folder, 'dat')
        sage: R = RESL(gstem,gps_folder,res_folder)
        sage: R
        Resolution of GF(2)[8gp3]
        sage: print(R)
        Resolution:
        0 <- GF(2) <- GF(2)[8gp3]

    So far, only term number zero of the resolution was created. We
    compute up to term number four, logging the computation::

        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.global_options('info')
        sage: R.nextDiff()
        sage: R.nextDiff()
        Resolution of GF(2)[8gp3]:
                  Computing next term
                  > rk P_02 =   3
        sage: R.nextDiff()
                  Computing next term
                  > rk P_03 =   4
        sage: R.nextDiff()
                  Computing next term
                  > rk P_04 =   5

    :meth:`nextDiff` writes data into the file ``res_folder``. By
    default, if data from previous computations are present, they will
    be automatically reloaded. This can be switched off by unsetting
    the option ``'reload'``.  We illustrate reloading here, by re-defining
    ``R``::

        sage: R = RESL(gstem,gps_folder,res_folder)
        sage: R.nextDiff()
        sage: R.nextDiff()
        Resolution of GF(2)[8gp3]:
                  Differential reloaded
                  > rk P_02 =   3
        sage: R.nextDiff()
                  Differential reloaded
                  > rk P_03 =   4
        sage: R.nextDiff()
                  Differential reloaded
                  > rk P_04 =   5
        sage: print(R)
        Resolution:
        0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3 <- rank 4 <- rank 5

    There is a copy method for resolutions, and it is also possible to save
    and load RESL objects::

        sage: S = copy(R)
        sage: print(S)
        Resolution:
        0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3 <- rank 4 <- rank 5
        sage: S = loads(dumps(R))
        Resolution of GF(2)[8gp3]:
                  Differential reloaded
                  > rk P_02 =   3
                  Differential reloaded
                  > rk P_03 =   4
                  Differential reloaded
                  > rk P_04 =   5
        sage: print(S)
        Resolution:
        0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3 <- rank 4 <- rank 5

    However, ``R`` and its copy ``S`` are not fully independent, as
    they share the same files on the disk. Moreover, when saving ``R``
    into a file 'file.sobj' then 'file.sobj' would not contain the
    data provided by the files in ``res_folder``; instead, it contains
    pointers to these data files. Therefore, moving 'file.sobj' to a
    different platform does not suffice to reconstruct the
    resolution. If ``res_folder`` and ``gps_folder`` are absolute path
    names, then even moving the whole root folder to another location
    would not allow for reloading the resolution, since the paths
    break.

    See :mod:`pGroupCohomology` for a discussion of that
    problem. However, the problem is rather easy to work around for
    :class:`~pGroupCohomology.resolution.RESL`: All data files used
    and produced by :class:`~pGroupCohomology.resolution.RESL` have a
    unique location relative to ``gps_folder`` and ``res_folder``. And
    all methods producing the data files would also be able to reload
    the data from the files. So, a re-construction of the
    :class:`~pGroupCohomology.resolution.RESL` object is easy provided
    the option 'reload' is used, and moving the folders thus is
    possible::

        sage: tmp_root2 = tmp_dir()
        sage: new_gps_folder = os.path.join(tmp_root2,gstem)
        sage: new_res_folder = os.path.join(new_gps_folder,'dat')
        sage: import os
        sage: os.rename(tmp_root,tmp_root2)
        sage: S = RESL(gstem,new_gps_folder,new_res_folder)
        sage: S.nextDiff()
        sage: S.nextDiff()
        Resolution of GF(2)[8gp3]:
                  Differential reloaded
                  > rk P_02 =   3
        sage: CohomologyRing.global_options('warn')
        sage: del S
        sage: os.rename(tmp_root2,tmp_root)

    **Differentials**

    A :class:`~pGroupCohomology.resolution.RESL` object represents a
    minimal free resolution for a finite `p`-group `G`, hence, it
    provides a sequence of free `\mathbb F_p`-modules that are
    related by homomorphisms, the differentials. The construction of
    the resolution relies on C-programs developped by `David Green
    <http://users.minet.uni-jena.de/~green/index.php>`_.  They involve
    a certain non-commutative Groebner basis theory due to David
    Green.

    A homomorphism from a rank `r` to a rank `s` free `\mathbb
    F_p`-module can be described by a `r\times s` matrix with
    coefficients in `\mathbb F_p`. An element of `\mathbb F_pG` can
    be represented by a tuple of length `|G|` of elements of `\mathbb
    F_p`. Therefore, the data for the differentials are stored as
    matrices with `|G|` columns and `r\times s` rows. Since David
    Green's programs use C-MeatAxe for linear algebra over finite
    fields, our :class:`~pGroupCohomology.resolution.RESL` class
    relies on our C-MeatAxe wrapper
    :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense`.

    If sufficiently many terms of the resolution are computed (using
    :meth:`nextDiff`), the differentials can be easily requested::

        sage: print(R)
        Resolution:
        0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3 <- rank 4 <- rank 5
        sage: R[2]
        [0 1 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 1 0 0 0 0 0]
        [0 0 0 0 0 0 1 0]
        [0 0 0 0 0 1 0 0]

    So, indeed the matrix has the right dimension: The group is of
    order 8, and the first and second term of the resolution are of
    rank 2 and 3, respectively::

        sage: R.rank(1)
        2
        sage: R.rank(2)
        3

    Blocks of `s=2` rows of the matrix correspond to elements in the image of the
    differential::

        sage: R[2][0:2]
        [0 1 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        sage: R[2][2:4]
        [0 0 0 0 0 0 0 0]
        [0 0 1 0 0 0 0 0]
        sage: R[2][4:6]
        [0 0 0 0 0 0 1 0]
        [0 0 0 0 0 1 0 0]

    These blocks encode a cochain, hence, a map from some term of the
    resolution (here: a term of rank two, corresponding to the number
    of rows) to the group algebra (whose elements are encoded by a
    `1\times |G|` matrix.

    The salient feature of a resolution is that the composition of two
    differentials is zero. This can be verified as follows (where we
    use :meth:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense.get_slice`,
    since ``R[2][0:2]`` would return a matrix relying on a different
    implementation)::

        sage: R.applyDiff(1,R[2].get_slice(0,2))
        [0 0 0 0 0 0 0 0]
        sage: R.applyDiff(1,R[2].get_slice(2,4))
        [0 0 0 0 0 0 0 0]
        sage: R.applyDiff(1,R[2].get_slice(4,6))
        [0 0 0 0 0 0 0 0]

    **Cochains and chain maps**

    A `d`-cochain `c` is a `\mathbb F_pG`-module morphism from the `d`-th term
    of the resolution to `\mathbb F_p`.

    Embedding `\mathbb F_p=\mathbb F_p\cdot 1 \subset \mathbb
    F_pG`, we obtain a map to the 0-th term of the resolution. This
    gives rise to a chain map of degree `-d`, hence, a collection of a
    map from the `(n+d)`-th term `R_{n+d}` to the `n`-th term `R_n` of
    the resolution, for all `n\ge 0`, that commute with the
    differentials.

    It is iteratively constructed as follows. Let the map `c_n:
    R_{n+d}\to R_n` be already known. We compose the differential
    `\partial_{n+1+d}` with it and obtain a map
    `\partial_{n+1+d}\circ c_n: R_{n+1+d}\to R_n`. It is easy to
    show that its image is contained in the image of
    `\partial_{d+1}`. We choose one of the pre-images, and obtain the
    next term `c_{n+1}: R_{n+1+d}\to R_{n+1}`.  We refer to that
    construction as 'lifting'.

    Here is a step-by-step example. Note that
    :class:`~pGroupCohomology.cochain.COCH` provides this
    functionality with high-level functions, hence, it is not needed
    to perform the following steps manually.

    First, we define a `1\times 3` matrix that represents a 2-cochain, and
    construct the lowest term of the corresponding chain map::

        sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
        sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX),[[1,0,1]])
        sage: c0 = R.CochainToChainmap(2,C)
        sage: c0
        (
              [1 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
        2, 0, [1 0 0 0 0 0 0 0]
        )

    In the next section, we discuss two differnt ways to lift the cochain. Here
    is the result::

        sage: c1 = R.liftChainMap(c0)
        sage: c1
        (
              [1 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]
              [0 0 0 1 0 0 0 0]
              [0 0 0 0 0 0 0 0]
        3, 1, [1 0 0 0 0 0 0 0]
        )

    We verify whether the result is correct. So, we first compose the third
    differential with ``c0``::

        sage: d3c0 = R.composeChainMaps(R[3],c0[2],3,2,0)
        sage: d3c0
        [0 1 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 1 0 0 0 0 1 0]
        [0 0 1 0 0 0 0 0]

    The matrix defining c1 contains 4 blocks of 2 rows, and we verify that
    their images under the first differential coincide with the rows of ``d3c0``::

        sage: d3c0.get_slice(0,1) == R.applyDiff(1,c1[2].get_slice(0,2))
        True
        sage: d3c0.get_slice(1,2) == R.applyDiff(1,c1[2].get_slice(2,4))
        True
        sage: d3c0.get_slice(2,3) == R.applyDiff(1,c1[2].get_slice(4,6))
        True
        sage: d3c0.get_slice(3,4) == R.applyDiff(1,c1[2].get_slice(6,8))
        True

    So, associated with the cochain ``C`` we obtain a chain map ``c``. For obtaining
    the cup product of ``C`` with itself, we compose ``c`` with itself. We obtain a
    chain map of degree `-4`, and its lowest term, composed with the augmentation map
    `\mathbb F_pG\to \mathbb F_p` yields the cochain ``C*C``. But first, we have
    to lift ``c`` one step further::

        sage: c2 = R.liftChainMap(c1)

    This can be composed with ``c0``::

        sage: cc = R.composeChainMaps(c2[2],c0[2],4,2,0)
        sage: cc
        [1 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [1 0 0 0 0 0 0 0]

    The basis of `\mathbb F_pG` is chosen so that the kernel of the augmentation
    map is given by all columns after the first. Hence, the cup product of ``C`` with
    itself is given by ``[1,0,0,0,1]``.

    Using the class :class:`~pGroupCohomology.cochain.COCH`, the computation is of
    course much more comfortable. For using this class, we need to create
    a cohomology ring, since we consider cochains as (representatives of)
    cohomology classes::

        sage: from pGroupCohomology.cochain import COCH
        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.set_user_db(tmp_root)
        sage: H = CohomologyRing(8,3, from_scratch=True)
        sage: C = COCH(H,2,'C',[1,0,1])
        sage: C*C
        (C)*(C): 4-Cocycle in H^*(D8; GF(2))
        sage: print(C*C)
        4-Cocycle in H^*(D8; GF(2)),
        represented by
        [1 0 0 0 1]

    **Urbild Groebner bases and autolift**

    We have seen in the previous section that for dealing with chain maps and
    for computing cup products one has to determine pre-images of differentials.
    In cohomology computations, these operations occur extremely often, so, it
    is essential to make them fast.

    When successively computing the terms of a resolutions, David Green's programs
    construct so-called Urbild Groebner bases and stores them in files in the
    directory ``res_folder`` (as provided in the definition of ``R``). They can also be
    used to lift chain maps. Using ``c1`` from above, we get::

        sage: CohomologyRing.global_options('info')
        sage: c2U = R.liftChainMap(c1)
        Resolution of GF(2)[8gp3]:
                  Compose chain maps R_4 -> R_3 -> R_1

    However, that method is rather slow. It is also possible to use some linear
    algebra to pick an element of the pre-image, but this requires to construct
    certain data first::

        sage: R.makeAutolift(2)
                  Make degree 2 autolift data
        sage: c2A = R.liftChainMap(c1)
                  Compose chain maps R_4 -> R_3 -> R_1

    It takes some time to make the autolift data, but if they are present, the
    lifting is *much* faster. Hence, if possible they are used. If one wants to
    use the Urbild Groebner bases, this can still be done with :meth:`ugb_liftChainMap`,
    although this has a slightly different syntax. The autolift method used to be more
    than 250 times faster than the Urbild Groebner basis method, but optimisations
    in recent package versions made the running time almost equal::

        sage: CohomologyRing.global_options('warn')
        sage: Ta = timeit.eval('cX = R.liftChainMap(c1)')
        sage: Tu = timeit.eval('cX = R.ugb_liftChainMap(c1[0]+1,c1[1]+1,c1[2])')
        sage: D={'s':10^6,'ms':10^3} # used for expressing the times in microseconds
        sage: 0.5 < Tu.stats[3]*D.get(Tu.stats[4],1)/(Ta.stats[3]*D.get(Ta.stats[4],1)) < 2
        True

    In general, the lifts obtained with both methods are not the same (they may
    vary up to elements in the radical, hence, in the kernel of the augmentation
    map), but here they are the same::

        sage: R.liftChainMap(c1)[2]==R.ugb_liftChainMap(c1[0]+1,c1[1]+1,c1[2])
        True

    Note that the construction of the autolift data in a certain degree only pays
    off if there will be many lifts to that degree. Hence, when computing a
    cohomology ring, we use the autolift method by default only up to degree 4.

    But there is also another problem: The memory consumption. For some more
    complicated groups, the Urbild Groebner bases are huge in higher degrees,
    and the autolift data would even be worse. Therefore, if the non-default
    option ``'sparse'`` is used, certain other data will be temporarily saved
    on disk before loading the Urbild Groebner bases, and vice versa.

    See :class:`~pGroupCohomology.cohomology.COHO` for examples.

    """
#####################
## init, dealloc etc
    def __init__(self,gstem,gps_folder='',res_folder='',groupname=None):
        """
        INPUT:

        - ``gstem`` -- a string that is an identifier for a finite `p`-group.
        - ``gps_folder`` -- (optional string) folder in which data for the
          group are stored.
        - ``res_folder`` -- (optional string) folder in which data for the
          resolution are stored (usually it is ``os.path.join(gps_folder,'dat')``).
        - ``groupname`` -- another string that identifies the group in
          a more human-readable way. Note that it is ignored when pickling.

        TESTS:

        The examples produce files. For safety reasons, we choose files in
        a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)

        The ``gstem`` is ``'8gp3'``, so, the group data are stored in the
        folder ``os.path.join(tmp_root,'8gp3')``, to which we refer as the
        stem folder. The function :func:`~pGroupCohomology.resolution.makeGroupData`
        also creates a subdirectory ``'dat'`` of the stem folder, which is
        intended to be used for storing the resolution.
        ::

            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)   #indirect doctest
            sage: R
            Resolution of GF(2)[8gp3]

        """
        if not (isinstance(gstem,basestring) and isinstance(res_folder,basestring) and isinstance(gps_folder,basestring)):
            raise TypeError("strings expected")
        self.gstem = gstem
        rstem='Res'+gstem
        self.rstem = rstem
        self.gps_folder=gps_folder
        self.res_folder=res_folder
        tmprstem = os.path.join(res_folder,rstem)
        tmpgstem = os.path.join(gps_folder,gstem)
        self.Data = newResolWithGroupLoaded(tmprstem,tmpgstem,1)
        self.Diff = []
        self.G_Alg = G_ALG('')
        freeGroupRecord(self.G_Alg.Data)
        self.G_Alg.Data = self.Data.group
        self.G_Alg.gstem = self.gstem
        self.G_Alg.groupname = groupname
        self.Lifts = LIFTcontainer(self)
        self.ToBeLifted = [] # Lists (n,MTX), if the cochain of degree n defined by MTX ought to be lifted to next degree.
        self.Autolift = {}
        self.ugb_deg = 0
        self.Action = [ self.G_Alg.r_action(baseMTX(self.G_Alg.Data.p, 1,self.G_Alg.Data.nontips, 0,i)) for i in range(self.G_Alg.Data.nontips)]
        self._Action_saved = 0
        self.exportAction()

    def __dealloc__(self):
        """
        Deallocation of underlying C-data.

        TESTS:

        The examples produce files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: m=get_memory_usage()
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: print(R)
            Resolution:
            0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3
            sage: del R   # indirect doctest

        """
        if self.Data:
            freeResolutionRecord(self.Data)
        # self.G_Alg.__dealloc__() is automatically called;
        # but self.G_Alg.Data=self.Data.group is already freed.
        # However, self.G_Alg.dependent is True, so, there will be no double-free.
        if self.ugb_deg:
            freeNRgs(self.nRgs)

    def __copy__(self):
        """
        Return a copy of ``self``.

        TESTS:
        The examples produce files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: m=get_memory_usage()
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: S=copy(R)   # indirect doctest
            sage: print(S)
            Resolution:
            0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3
            sage: S==R
            True
            sage: S is R
            False

        """
        cdef RESL OUT
        OUT = RESL(self.gstem,self.gps_folder,self.res_folder)
        OUT.Diff = copy(self.Diff)
        OUT.Lifts = copy(self.Lifts)
        OUT.ToBeLifted = copy(self.ToBeLifted)
        OUT.Autolift = deepcopy(self.Autolift)
        OUT.Action = copy(self.Action)
        cdef int n
        cdef int M = len(OUT.Diff)
        for n from 1 <= n <= M:
            setRankProj(OUT.Data, n, int(OUT[n].nrows()/OUT.Data.projrank[n-1]))
        return OUT

    def __reduce__(self):
        """
        Return data used for pickling/unpickling ``self``.

        NOTE:

        In the documentation of  :func:`~pGroupCohomology.cohomology.COHO`, it is explained in
        more detail why saving a resolution in a file does not suffice to port it to a different
        plattform.

        EXAMPLES:

        The examples produce files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: m=get_memory_usage()
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: S = loads(dumps(R))   # indirect doctest
            sage: S==R
            True
            sage: S is R
            False

        """
        self.exportLifts()
        cdef list Lifts = []
        for X,Y in self.Lifts.Data.items():
            s = Y.get('file','')
            if (not s) and isinstance(Y.get(1,None), tuple):
                # Problem: the number 1 evaluates equal to
                # the MTX matrix [1]. That hasn't been the
                # case in the past. Now we have to deal with
                # it, since in old data it is assumed that
                # they aren't equal.
                s = ''
            else: # That's old exported data
                s = Y.get(1,'')
            if not s:
                s = os.path.join(self.res_folder,'L'+self.gstem+'n'+str(X[0])+'d'+str(X[1]))
            Lifts.append((X,s))
        r = os.path.split(self.gps_folder)[0]
        from pGroupCohomology.cohomology import COHO
        if r == COHO.public_db:
            return resl_sparse_unpickle, (self.gstem,self.gps_folder,self.res_folder,self.deg(),Lifts,self.Autolift,self.Action,'@public_db@')
        if r == COHO.user_db:
            return resl_sparse_unpickle, (self.gstem,self.gps_folder,self.res_folder,self.deg(),Lifts,self.Autolift,self.Action, '@user_db@')
        return resl_sparse_unpickle, (self.gstem,self.gps_folder,self.res_folder,self.deg(),Lifts,self.Autolift,self.Action)

    def __str__(self):
        """
        Return a brief description of the resolution, providing the projective ranks.

        TESTS:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: print(R)   # indirect doctest
            Resolution:
            0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3 <- rank 4
        """
        cdef list L=['0',"GF(%d)"%(self.G_Alg.Data.p), repr(self.G_Alg)]+ \
           ['rank %d'%self.Data.projrank[n+1] for n in range(self.Data.numproj)]
        OUT='Resolution:\n'+' <- '.join(L)
        return OUT

    def __repr__(self):
        """
        Short string representation.

        EXAMPLES::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R
            Resolution of GF(2)[8gp3]
        """
        return 'Resolution of {}'.format(self.G_Alg)

    def label(self):
        """
        Return a short descriptor of this resolution.

        EXAMPLES::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.label()
            'Res8gp3'

        """
        return self.rstem

########################
# structural parts

    def __getitem_name__(self,key):
        """
        Return `n`-th differential or the name of a file providing that differential.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.global_options('sparse')
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()

        If the option 'sparse' is used (which currently is not the default!), then
        usually the matrices representing the differentials are not in memory
        but stored on disk::

            sage: isinstance(R.__getitem_name__(3),basestring)
            True

        We verify that indeed the stored matrix coincides with the third
        differential::

            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: MTX(R.__getitem_name__(3))==R[3]
            True

        However, if the differential is kept in memory, then ``__getitem_name__`` will
        return it::

            sage: R.__getitem_name__(1)
            [0 1 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            sage: CohomologyRing.reset()

        """
        return self.Diff[key-1]

    def __getitem__(self,key):
        """
        Return `n`-th differential (type mtx.MTX).

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.global_options('sparse')
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: print(R[3])   # indirect doctest
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 1 0]
            [0 0 0 0 0 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 1 0 0]
            [0 0 1 0 0 0 0 0]

        Note that, if the option 'sparse' is used (which currently is not
        the default), then most of the matrices representing the differentials
        are not in memory but stored on disk. The file name can be obtained
        with :meth:`__getitem_name__`::

            sage: isinstance(R.__getitem_name__(3),basestring)
            True
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: MTX(R.__getitem_name__(3))==R[3]
            True
            sage: CohomologyRing.reset()

        See  :class:`~pGroupCohomology.resolution.RESL` for further examples.

        """
        if isinstance(key,int) or isinstance(key,Integer):
            if (key<1) or (key>len(self.Diff)):
                raise IndexError("Index out of range")
            else:
                if isinstance(self.Diff[key-1],basestring):
                    return MTX(self.Diff[key-1])
                else:
                    return self.Diff[key-1]
        else:
            raise TypeError("integer expected")

    def G_ALG(self):
        """
        Return the  :class:`~pGroupCohomology.resolution.G_ALG` object over which the resolution is defined.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.G_ALG()
            GF(2)[8gp3]

        """
        return self.G_Alg

    def DiffList(self):
        """
        Return the list of computed differentials of a resolution, respectively the path to saved data.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.global_options('sparse')
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()

        Since in our test we use the non-default option 'sparse', most of
        the differentials are not kept in memory but saved on disk, and
        ``R.difflist()`` points to their location::

            sage: R.DiffList()
            [
            [0 1 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0],
             '.../8gp3/dat/Res8gp3d02.bin',
             '.../8gp3/dat/Res8gp3d03.bin'
            ]
            sage: CohomologyRing.reset()

        """
        return self.Diff

    def rank(self, n=-1):
        """
        Return projective rank(s) of a term or all terms  of ``self``.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: print(R)
            Resolution:
            0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3 <- rank 4
            sage: R.rank()
            (1, 2, 3, 4)
            sage: R.rank(2)
            3

        """
        if n==-1:
            return tuple([self.Data.projrank[i] for i in range(len(self.Diff)+1)])
        if (n<0):
            raise IndexError("Index out of range")
        while (n>len(self.Diff)):
            self.nextDiff()
        return self.Data.projrank[n]

    def deg(self):
        """
        Return the number of terms of self that have been computed so far.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.deg()
            3

        """
        return self.Data.numproj

    def coef(self):
        """
        Return the characteristic of the field over which ``self`` is defined.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.coef()
            2

        """
        return self.G_Alg.Data.p

    def grouporder(self):
        """
        Return the order of the group over wich ``self`` is defined.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.grouporder()
            8

        """
        return self.G_Alg.Data.nontips

    def getLifts(self):
        """
        Return the dictionary of cached lifts.

        NOTE:

        That function was only created in order to provide a
        doc test for :meth:`setLift`.

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import COCH
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3, from_scratch=True, options='sparse')
            sage: R = H.resolution()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = COCH(H,1,'C',[0,1])
            sage: R.getLifts()
            {}
            sage: print(C*C)
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 1 0]

        Now, two lifts of ``C`` (considered as a chain map of degree one)
        are cached. If the ``sparse`` option is used (which we do here,
        although it is currently not the default), one of the lifts is
        exported to a file in order to save memory::

            sage: sorted(R.getLifts().items())
            [((1, 1),
              {'file': '.../8gp3/dat/L8gp3n1d1'}),
             ((2, 1),
              {[0 1]: ((
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 1 0 0 0]
            2, 1, [0 0 0 0 0 0 0 0]
            ),
                2)})]
            sage: CohomologyRing.reset()

        """
        return self.Lifts.out()

    def setLift(self, COCH C, n_max):
        """
        Make a trivial entry in the list of known lifts for a given cochain.

        INPUT:

        - ``C``, a cochain defined over self
        - ``n``, maximal degree to which the cochain shall be lifted

        NOTE:

        This function should only be of internal use

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: R = H.resolution()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()

        Now we construct a cochain::

            sage: from pGroupCohomology.cochain import COCH
            sage: C = COCH(H,2,'C',[1,0,1])
            sage: R.getLifts()
            {}
            sage: R.setLift(C,4)
            sage: R.getLifts().keys()
            [(2, 2)]

        Hence, now there are cochains (i.e., chain maps) of degree 2 whose lifts are
        known in degree 2.
        ::

            sage: R.getLifts().values()
            [{[1 0 1]: ((
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            2, 0, [1 0 0 0 0 0 0 0]
            ),
               4)}]

        In fact, the known lift is the trivial one::

            sage: R.getLifts()[(2,2)][C.MTX()][0] == R.CochainToChainmap(2,C.MTX())
            True

        """
        if not (isinstance(n_max,int) or isinstance(n_max,Integer)):
            raise TypeError("integer expected")
        if n_max < C.deg():
            raise IndexError("Maximal lift index must be at least the degree of the cochain")
        self.Lifts[(C.deg(),C.deg(),C.MTX())] = (self.CochainToChainmap(C.deg(),C.MTX()), n_max)

    def exportAction(self):
        """
        Internally used: Save list of `G`-action matrices in a file.

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, coho_logger
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.exportAction()
            sage: load(os.path.join(res_folder,'A8gp3'))
            [
            [1 0 0 0 0 0 0 0]  [0 1 0 0 0 0 0 0]  [0 0 1 0 0 0 0 0]
            [0 1 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]  [0 0 0 1 0 0 0 0]
            [0 0 1 0 0 0 0 0]  [0 0 0 0 1 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 1 0 0 0 0]  [0 0 0 0 0 1 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 1 0 0 0]  [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 1 0]
            [0 0 0 0 0 1 0 0]  [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 1]
            [0 0 0 0 0 0 1 0]  [0 0 0 0 0 0 0 1]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 1], [0 0 0 0 0 0 0 0], [0 0 0 0 0 0 0 0],
            <BLANKLINE>
            [0 0 0 1 0 0 0 0]  [0 0 0 0 1 0 0 0]  [0 0 0 0 0 1 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 1 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 1 0]  [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 1]
            [0 0 0 0 0 0 0 1]  [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 1]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0], [0 0 0 0 0 0 0 0], [0 0 0 0 0 0 0 0],
            <BLANKLINE>
            [0 0 0 0 0 0 1 0]  [0 0 0 0 0 0 0 1]
            [0 0 0 0 0 0 0 1]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]  [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0], [0 0 0 0 0 0 0 0]
            ]

        The G-action matrices are used to compute the autolift data, and *only* there.
        Hence, the action matrices will be imported if the autolift data are computed,
        and exported if this is finished::

            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.global_options('info')
            sage: R.makeAutolift(2)
            Resolution of GF(2)[8gp3]:
                      Make degree 2 autolift data
            sage: CohomologyRing.reset()

        """
        if self.Action:
            if not self._Action_saved:
                import os
                coho_logger.debug('> export action matrices',self)
                try:
                    safe_save(self.Action,os.path.join(self.res_folder,'A'+self.gstem+'.sobj'))
                    self._Action_saved = 1
                except (IOError, OSError, RuntimeError): # could be that it is a link to a write protected file
                    coho_logger.warn("> action matrices can't be saved", self)
                    self._Action_saved = 0
                    # although this costs memory, we don't delete
                    # the matrices, for otherwise they need to be
                    # expensively reconstructed.
            if self._Action_saved:
                self.Action = []

    def importAction(self):
        """
        Reload list of `G`-action matrices that have been exported using :meth:`exportAction`.

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, coho_logger
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.global_options('sparse')
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.exportAction()
            sage: R.nextDiff()
            sage: R.nextDiff()

        In the documentation of :meth:`exportAction`, it is shown that
        usually the action matrices are imported by :meth:`makeAutolift`.
        But it is alright to do it manually; it can be seen in the log
        that the matrices will not be imported twice (and note that
        the action is to be imported only since we use the non-default
        ``sparse`` option)::

            sage: CohomologyRing.global_options('debug')
            sage: R.importAction()
            Resolution of GF(2)[8gp3]:
                      > import action matrices
            sage: R.makeAutolift(2)
                      Make degree 2 autolift data
            sage: CohomologyRing.reset()

        """
        if not self.Action:
            coho_logger.debug('> import action matrices', self)
            try:
                self.Action = load(os.path.join(self.res_folder,'A'+self.gstem+'.sobj'))  # realpath here?
                self._Action_saved = 1
            except (IOError, OSError, RuntimeError), msg:
                self.Action = [ self.G_Alg.r_action(baseMTX(self.G_Alg.Data.p, 1,self.G_Alg.Data.nontips, 0,i)) for i in range(self.G_Alg.Data.nontips)]
                self._Action_saved = 0

    def exportLifts(self):
        """
        Save cached lifts into files.

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import COCH
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3, from_scratch=True, options='sparse')
            sage: C = COCH(H,1,'C',[0,1])
            sage: print(C*C)
            2-Cocycle in H^*(D8; GF(2)),
            represented by
            [0 1 0]
            sage: R = H.resolution()

        Since we use the non-default ``sparse`` option, some of the data
        is stored in a file::

            sage: sorted(R.getLifts().items())
            [((1, 1),
              {'file': '.../8gp3/dat/L8gp3n1d1'}),
             ((2, 1),
              {[0 1]: ((
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 1 0 0 0]
            2, 1, [0 0 0 0 0 0 0 0]
            ),
                2)})]
            sage: R.exportLifts()

        Now, both lifts are stored on disk::

            sage: sorted(R.getLifts().items())
            [((1, 1), {'file': '.../8gp3/dat/L8gp3n1d1'}),
             ((2, 1), {'file': '.../8gp3/dat/L8gp3n2d1'})]
            sage: CohomologyRing.reset()

        """
        self.Lifts.export()

    def free_ugb(self):
        """
        Deallocate the currently loaded Urbild Groebner basis.

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import COCH
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: R = H.resolution()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: CohomologyRing.global_options('debug','nosparse')
            sage: C = COCH(H,1,'C',[1,0])
            sage: D = C*C
            Resolution of GF(2)[D8]:
                      Compute C*C
                      Compose chain maps R_2 -> R_1 -> R_0
                      Lift with Urbild Groebner basis in degree 1
                      load Urbild Groebner basis

        Now, the Urbild Groebner basis is allocated. Since we use the option
        ``'nosparse'``, it is not automatically deallocated, and is used to lift
        further cochains::

            sage: C = COCH(H,1,'C',[0,1])
            sage: D = C*C
                      Compute C*C
                      Compose chain maps R_2 -> R_1 -> R_0
                      Lift with Urbild Groebner basis in degree 1

        Now we deallocate it manually. In the subsequent computation, it
        is reloaded again::

            sage: R.free_ugb()
                      deallocate Urbild Groebner basis
            sage: C = COCH(H,1,'C',[1,1])
            sage: D = C*C
                      Compute C*C
                      Compose chain maps R_2 -> R_1 -> R_0
                      Lift with Urbild Groebner basis in degree 1
                      load Urbild Groebner basis

        Finally, let us reset the machinery, in order to not break other
        doctests in this module.

            sage: CohomologyRing.reset()

        """
        if self.ugb_deg:
            coho_logger.debug("deallocate Urbild Groebner basis", self)
            freeNRgs(self.nRgs)
        self.ugb_deg = 0

    def load_ugb(self, int d):
        """
        Load Urbild Groebner basis for lifts from degree `d-1` to `d`.

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import COCH
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: R = H.resolution()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: CohomologyRing.global_options('debug','nosparse')
            sage: C = COCH(H,1,'C',[0,1])

            Now, we load the Urbild Groebner basis for lifts to degree 1. Hence,
            it is not needed to load it again in the subsequent computation.
            ::

                sage: R.load_ugb(1)
                Resolution of GF(2)[D8]:
                          load Urbild Groebner basis
                sage: D=C*C
                          Compute C*C
                          Compose chain maps R_2 -> R_1 -> R_0
                          Lift with Urbild Groebner basis in degree 1

            But if we load the Urbild Groebner basis in a different degree, the
            correct one will be automatically reloaded when necessary::

                sage: R.load_ugb(2)
                          load Urbild Groebner basis
                sage: C = COCH(H,1,'C',[1,0])
                sage: D=C*C
                          Compute C*C
                          Compose chain maps R_2 -> R_1 -> R_0
                          Lift with Urbild Groebner basis in degree 1
                          load Urbild Groebner basis

            Finally, let us reset the machinery, in order to not break other
            doctests in this module.

                sage: CohomologyRing.reset()

        """
        if d<1:
            raise ValueError("Degree must be at least 1")
        if self.ugb_deg != d:
            if coho_options['sparse']:
                self.exportLifts()
            coho_logger.debug("load Urbild Groebner basis", self)
            if self.ugb_deg:
                freeNRgs(self.nRgs)
            self.nRgs = loadUrbildGroebnerBasis(self.Data, d)
            self.ugb_deg = d

#########################
# ==, <, >
    def __richcmp__(RESL self, RESL S, int x):
        """
        ``R <= S`` if and only if ``R`` coincides with the first terms of ``S``.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: S = copy(R)
            sage: S.nextDiff()
            sage: R==S   # indirect doctest
            False
            sage: R<S
            True
            sage: S>=R
            True

        """
        # < 0, <= 1, == 2, != 3, > 4, >= 5
        if x==0:
            return (self.G_Alg<=S.G_Alg) and (self.Diff<S.Diff)
        if x==1:
            return (self.G_Alg<=S.G_Alg) and (self.Diff<=S.Diff)
        if x==2:
            return (self.G_Alg==S.G_Alg) and (self.Diff==S.Diff)
        if x==3:
            return (self.G_Alg!=S.G_Alg) or (self.Diff!=S.Diff)
        if x==4:
            return (self.G_Alg>=S.G_Alg) and (self.Diff>S.Diff)
        return (self.G_Alg>=S.G_Alg) and (self.Diff>=S.Diff)


#########################
# Construct the resolution
    def firstDiff(self):
        """
        Make first differential for ``self``.

        This function is usually called from nextDiff().

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.firstDiff()
            sage: print(R)
            Resolution:
            0 <- GF(2) <- GF(2)[8gp3] <- rank 2

        An error is raised if it is attempted to compute the first term again.
        ::

            sage: R.firstDiff()
            Traceback (most recent call last):
            ...
            IndexError: First differential is already computed

        """
        FfSetField(self.G_Alg.Data.p)
        FfSetNoc(self.G_Alg.Data.nontips)
        cdef MTX M
        if len(self.Diff):
            raise IndexError("First differential is already computed")
        M = makeMTX(makeFirstDifferential(self.Data))
        M.set_immutable()
        self.Diff = [M]

    def nextDiff(self):
        """
        Compute next unknown differential of the resolution.

        EXAMPLES:

        The examples produce files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R
            Resolution of GF(2)[8gp3]

        So far, only term number zero of the resolution was created. We compute up to term
        number four::

            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: print(R)
            Resolution:
            0 <- GF(2) <- GF(2)[8gp3] <- rank 2 <- rank 3 <- rank 4 <- rank 5
            sage: R[3]
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 1 0]
            [0 0 0 0 0 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 1 0 0]
            [0 0 1 0 0 0 0 0]

        """
        ct=cputime()
        wt=walltime()
        FfSetField(self.G_Alg.Data.p)
        FfSetNoc(self.G_Alg.Data.nontips)
        cdef group_t *G
        G = self.Data.group
        # kind of "loadDifferential":
        cdef nRgs_t *nRgs
        cdef MTX M
        cdef Matrix_t *pres
        n=len(self.Diff)+1 # n-th differential is to be computed
        if n==1:
            self.firstDiff()
            return
        try:
            M = MTX(differentialFile(self.Data, n),mutable=False)
        except OSError:
            M = None
        if M is not None: # if the differential was computed before
            assert M.Data != NULL and M.Data.Data != NULL, "Stored differential was empty"
            if coho_options['sparse']:
                self.Diff.append(str(differentialFile(self.Data, n)))
            else:
                self.Diff.append(M)
            setRankProj(self.Data, n, int(M.Data.Nor/self.Data.projrank[n-1]))
            coho_logger.info("Differential reloaded", self)
            coho_logger.info("> rk P_%02ld = %3ld"%(n, self.Data.projrank[n]), self)
            return
        # we have to construct the next differential from scratch
        coho_logger.info("Computing next term", self)
        sig_on()
        M = self[n-1]
        nRgs = nRgsStandardSetup(self.Data, n-1, M.Data.Data)
        cdef nFgs_t *ker
        ker = nRgs.ker
        nRgsBuchberger(nRgs, G)
        setRankProj(self.Data, n, numberOfHeadyVectors(ker.ngs))
        sig_off()
        coho_logger.info("> rk P_%02ld = %3ld"%(n, self.Data.projrank[n]), self)
        M = makeMTX(getMinimalGenerators(ker, G))
        M.set_immutable()
        saveUrbildGroebnerBasis(nRgs, urbildGBFile(self.Data, n-1), G)
        MatSave(M.Data, differentialFile(self.Data, n))
        if coho_options['sparse']:
            self.Diff.append(str(differentialFile(self.Data, n)))
        else:
            self.Diff.append(M)
        freeNRgs(nRgs)

    def makeAutolift(self, d):
        """
        Produce internal data that allow to quickly lift chain maps to one degree.

        INPUT:

        d -- the degree into which it shall be lifted

        EXAMPLE:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.cochain import COCH
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3, from_scratch=True)
            sage: R = H.resolution()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: CohomologyRing.global_options('debug')
            sage: C = COCH(H,1,'C',[0,1])

        For computing a cup product, the necessary lift of a chain map is done
        with the so-called autolift method, provided it is available. This is
        not yet the case, so a different, but much slower method (Urbild Groebner
        bases) is used::

            sage: D=C*C
            Resolution of GF(2)[D8]:
                      Compute C*C
                      Compose chain maps R_2 -> R_1 -> R_0
                      Lift with Urbild Groebner basis in degree 1
                      load Urbild Groebner basis

        Now we create the data. And by consequence, a method is used that
        usually is a bit faster (but the time spent with computing the
        autolift data should be taken into account as well)::

            sage: R.makeAutolift(1)
                      Make degree 1 autolift data
                      > import action matrices
            sage: C = COCH(H,1,'C',[1,0])
            sage: D=C*C
                      Compute C*C
                      Compose chain maps R_2 -> R_1 -> R_0
                      > Lift with the autolift method

        Finally, let us reset the machinery, in order to not break other
        doctests in this module.

            sage: CohomologyRing.reset()

        """
        coho_logger.info('Make degree %d autolift data'%(d), self)
        cdef int i,j,k
        ct=cputime()
        wt=walltime()
        self.importAction()
        cdef int rk  = self.Data.projrank[d-1]
        cdef int RK  = self.Data.projrank[d]
        cdef long fl  = self.G_Alg.Data.p
        cdef long nt  = self.G_Alg.Data.nontips
        cdef int maxK = rk*nt
        cdef MTX D   = self[d]
        cdef dict Autolift = {}
        if not self.Action: # which should never happen...
            return
        cdef list D_G = [D*self.Action[i] for i in range(nt)]

        # determine a triangular GF(fl) basis for the image of the d-th differential,
        # keeping track of the pre-images of basis elements
        cdef list L
        cdef Matrix0 M
        cdef MTX Mmtx
        baseK = GF(fl)

        if coho_options['useMTX']:
            Mmtx = makeMTX(MatAlloc(fl, RK*nt, (rk+RK)*nt))
            FfSetField(fl)
            FfSetNoc(Mmtx.Data.Noc)
            for i from 0 <= i < RK: # "long rows" of M
                for j from 0 <= j < nt: # "short rows" within a long row of M
                    L = D_G[j]._rowlist_(i*rk,(i+1)*rk-1)
                    assert len(L)==maxK
                    for k from 0 <= k < maxK:
                        FfInsert(FfGetPtr(Mmtx.Data.Data,i*nt+j), k, FfFromInt(L[k]))
                        #Mmtx.set_unsafe_int(i*nt+j, k, L[k])
                    Mmtx[i*nt+j, maxK+i*nt+j] = 1
            M = Mmtx
        else:
            M = Matrix(baseK, RK*nt, (rk+RK)*nt, 0)  # we begin with zero.
            for i from 0 <= i < RK: # "long rows" of M
                for j from 0 <= j < nt: # "short rows" within a long row of M
                    L = D_G[j]._rowlist_(i*rk,(i+1)*rk-1)
                    assert len(L)==maxK
                    for k from 0 <= k < maxK:
                        M.set_unsafe(i*nt+j, k, baseK(L[k]))
                    M[i*nt+j, maxK+i*nt+j] = 1
        M.echelonize()

        # extract preimages
        cdef tuple Piv = M.pivots()
        cdef int lenPiv = len(Piv)
        cdef long rknt = rk*nt
        cdef MTX M2
        for i from 0 <= i < lenPiv:
            if Piv[i]<rknt: # otherwise we got something in the kernel
                if coho_options['useMTX']:
                    Mmtx = M
                    L = Mmtx._rowlist_(i)[rknt:]
                else:
                    L = list(M[i])[rknt:]
                M2 = makeMTX(MatMulScalar(rawMatrix(fl, [L[k*nt:(k+1)*nt] for k in range(RK)]), mtx_tmultinv[M[i,Piv[i]]]))
                M2.set_immutable()
                Autolift[Piv[i]] = [()] + [M2._mul_long(ff+1) for ff in range(fl-1)]
        Autolift['Piv'] = tuple(sorted(X for X in Piv if X<rknt))
        self.Autolift[d] = Autolift
        self.exportAction()

##################
# Yoneda complex
    def _get_yoneda_liftdata(self, n):
        """
        INPUT:

        ``n``: integer

        OUTPUT:

        ``P,K,D``: Data that allow for the fast computation of a Yoneda `(n-1)`-cochain that cobounds
        a given Yoneda `n` cocycle. Compare :meth:`yoneda_coboundary` and :meth:`~pGroupCohomology.cochain.YCOCH.find_cobounding_yoneda_cochain`.

        This method should only be of internal use. The output is cached on disk.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: P,K,D = H.resolution()._get_yoneda_liftdata(2)

        Now, ``P`` is a list of pivots, ``K`` is a list of pairs of :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense`
        matrices defining some Yoneda cocycle (hence, the coboundary vanishes), and
        ``D`` is a dictionary whose keys are the given pivot, and whose values are pairs of
        :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrices defining some Yoneda cochain whose coboundary
        realizes a certain pivot.

            sage: P
            [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23]
            sage: print(K[0][0])
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: print(K[0][1])
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 1 0 0 0 0]
            sage: print(D[12][0])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: print(D[12][1])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]

        """
        import os
        try:
            return load(os.path.join(self.res_folder,'Y'+self.gstem+'d%d.sobj'%n)) # realpath here?
        except (IOError, OSError):
            pass
        coho_logger.info('Compute Yoneda lift data', self)
        cdef int i,j,k,l
        ct=cputime()
        wt=walltime()
        self.importAction()
        while self.deg() < n:
            self.nextDiff()
        cdef int RK  = self.Data.projrank[n]
        cdef int Rk  = self.Data.projrank[n-1]
        cdef int rk  = self.Data.projrank[1]

        cdef long fl  = self.G_Alg.Data.p
        cdef long nt  = self.G_Alg.Data.nontips
        cdef int maxK = RK*nt
        # We choose the signs according to Borge's PhD thesis:
        cdef MTX Dn   = self[n]
        cdef MTX D1
        if n%2:
            D1 = -self[1]
        else:
            D1 = self[1]
        cdef dict Autolift = {}
        if not self.Action: # which should never happen...
            return
        cdef list Dn_G = [Dn*self.G_Alg.l_action(baseMTX(self.G_Alg.Data.p, 1,self.G_Alg.Data.nontips, 0,i)) for i in range(nt)] # Here we have to choose the left action, since we compose FIRST Dn, then some other map.
        cdef list D1_G = [D1*self.Action[i] for i in range(nt)] # This is right action, since we have FIRST another map and then D1.

        # determine a triangular GF(fl) basis for the image of the n-th Yoneda differential
        #
        # keeping track of the pre-images of basis elements
        cdef list L
        cdef MTX Mmtx
        cdef Matrix0 M
        baseK = GF(fl)
        if coho_options['useMTX']:
            Mmtx = makeMTX(MatAlloc(fl, (RK+RK*rk)*nt, (RK+Rk+RK*rk)*nt))
            M = Mmtx
        else:
            M = Matrix(baseK, (RK+RK*rk)*nt, (RK+Rk+RK*rk)*nt, 0)  # we begin with zero.
        # Organization of the rows of M:
        #  Image  ||  Y:P_{n-1}->P_0             Z: P_n -> P_1      # Meaning: We consider bases of these guys.
        #                              <               RK                    >
        #    RK           Rk           { rk }         { rk }            { rk }
        # |nt|nt|..|  |nt|nt|..|nt|  |nt|nt|..|nt||nt|nt|..|nt|  ... |nt|nt|..|nt|
        if coho_options['useMTX']:
            FfSetField(Mmtx.Data.Field)
            FfSetNoc(Mmtx.Data.Noc)
        for i from 0 <= i < Rk:  # "long rows" of M, part 1
            for j from 0 <= j < nt: # "short rows" within a long row of M
                # The following collects all RK short rows of Dn_G[j] that correspond to short row number i
                L = []
                for k from 0 <= k < RK:
                    L.extend(Dn_G[j]._rowlist_(k*Rk+i,k*Rk+i) )
                if coho_options['useMTX']:
                    for k from 0 <= k < maxK:
                        FfInsert(FfGetPtr(Mmtx.Data.Data,i*nt+j), k, FfFromInt(L[k]))
                else:
                    for k from 0 <= k < maxK:
                        M.set_unsafe(i*nt+j, k, baseK(L[k]))
                M[i*nt+j, maxK+i*nt+j] = 1
        cdef int offset
        # "long rows" of M, part 2, which are given by basis vectors for the set of maps Z:P_n->P_1
        for l from 0 <= l < rk: # i counts the long rows of Z, l counts the short rows within a long row of Z
            for j from 0 <= j < nt: # "short rows" within a long row of M
                # most of the first nt*RK colums in this part of M will be zero,
                # since only the following nt values are to be inserted (in the right place)
                L = D1_G[j]._rowlist_(l,l)
                for i from 0 <= i < RK:
                    offset = (Rk + i*rk+l)*nt + j
                    # This may be rather slow. Optimizations?
                    # However, it is just nt elements, not nt*RK or so.
                    for k from 0 <= k < nt:
                        M[offset, i*nt+k] = baseK(L[k])
                    M[offset, maxK+offset] = 1
        coho_logger.debug('Computing echelon form of a %dx%d matrix'%(M.nrows(),M.ncols()), self)
        M.echelonize()
        # We will use these lift data for the Massey products. In particular, we are interested in the
        # case where the map Y:P_{n-1}->P_0 gives rise to a non-zero cohomology element.
        # The kernel elements give rise to different choices of a defining system for the Massey
        # products, provided that these kernel elements are no coboundaries.
        # The return value is a pair (P,K,D), where P is a list of pivots, K is a basis (list of
        # elements) of a complement of the coboundary in the kernel ("element" means a pair (Y,Z)
        # of matrices describing maps as above that are in the kernel of the Yoneda coboundary),
        # and D is a dictionary so that D[i] is an "element" whose Yoneda coboundary has i as pivot.

        cdef tuple Piv = M.pivots()
        cdef int lenPiv = len(Piv)
        cdef list K = []
        cdef dict D = {}
        cdef MTX Y,Z
        cdef long RKnt = RK*nt
        for i from 0 <= i < lenPiv:
            if Piv[i]<RKnt: # not in the kernel
                if coho_options['useMTX']:
                    L = M._rowlist_(i)[RKnt:]
                else:
                    L = list(M[i])[RKnt:]
                # pair Y,Z, where Y:P_{n-1}->P_0 is encoded in the second block of M (rows RKnt,...,RKnt+Rk*nt)
                # and Z:P_n->P_1 is encoded in the third block of M (rows RKnt+RK*nt,...,RKnt+Rk*nt+RK*rk*nt)
                LY = L[:Rk*nt]
                LZ = L[Rk*nt:]
                Y = makeMTX(MatMulScalar(rawMatrix(fl, [LY[k*nt:(k+1)*nt] for k in range(Rk)]), mtx_tmultinv[M[i,Piv[i]]]))
                Y.set_immutable()
                Z = makeMTX(MatMulScalar(rawMatrix(fl, [LZ[k*nt:(k+1)*nt] for k in range(RK*rk)]), mtx_tmultinv[M[i,Piv[i]]]))
                Z.set_immutable()
                D[Piv[i]] = (Y, Z)
            else: # kernel
                relevant = False
                k = Rk+RK*rk
                for j from 0 <= j < k:
                    if M[i, RKnt + j*nt]:
                        relevant = True
                        break
                if relevant:
                    if coho_options['useMTX']:
                        L = M._rowlist_(i)[RKnt:]
                    else:
                        L = list(M[i])[RKnt:]
                    # pair Y,Z, where Y:P_{n-1}->P_0 is encoded in the second block of M (rows RKnt,...,RKnt+Rk*nt)
                    # and Z:P_n->P_1 is encoded in the third block of M (rows RKnt+RK*nt,...,RKnt+Rk*nt+RK*rk*nt)
                    LY = L[:Rk*nt]
                    LZ = L[Rk*nt:]
                    Y = makeMTX(MatMulScalar(rawMatrix(fl, [LY[k*nt:(k+1)*nt] for k in range(Rk)]), mtx_tmultinv[M[i,Piv[i]]]))
                    Y.set_immutable()
                    Z = makeMTX(MatMulScalar(rawMatrix(fl, [LZ[k*nt:(k+1)*nt] for k in range(RK*rk)]), mtx_tmultinv[M[i,Piv[i]]]))
                    Z.set_immutable()
                    K.append((Y, Z))

        self.exportAction()
        OUT = ([k for k in Piv if k<RKnt], K, D)
        safe_save(OUT, os.path.join(self.res_folder,'Y'+self.gstem+'d%d'%n))
        return OUT


##################
# Arithmetic
    def applyDiff(self, long n,MTX x):
        r"""
        Apply `n`-th differential map to an element `x` of the `n`-th term of ``self``.

        INPUT:

        - n -- integer, determining a term of self
        - x -- `(r \times |G|)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix, where `r` is
          the projective rank of the `n`-th term of self, and `G` is the group upon which
          `R` is defined.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.rank(2)
            3
            sage: R.rank(3)
            4

        We will verify that the composition of the third differential with the second
        differential vanishes. Since the rank of the second term of the resolution is
        3, the four blocks of 3 rows of the matrix R[3] correspond to generators of
        the image of the differntial::

            sage: R.applyDiff(2,R[3].get_slice(0,3))
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: R.applyDiff(2,R[3].get_slice(3,6))
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: R.applyDiff(2,R[3].get_slice(6,9))
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: R.applyDiff(2,R[3].get_slice(9,12))
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]

        """
        if (n<1) or (n>len(self.Diff)):
            raise IndexError("{} differential is not computed".format(Integer(n).ordinal_str()))
        if (x.nrows()!=self.Data.projrank[n]) or (x.ncols()!=self.G_Alg.Data.nontips):
            raise TypeError("Elements of the {} term of the resolution must be presented\nby ({} x {}) MTX matrices".format(Integer(n).ordinal_str(),self.Data.projrank[n],self.G_Alg.Data.nontips))
        return self.G_Alg.kG_map(self[n],x)

    def find_bounding_chain(self, long n, MTX M, check=False):
        r"""
        Find a chain that yields a given `n-1` chain under the `n`-th differential.

        INPUT:

        - ``n`` -- integer, determining a term of self
        - ``M`` -- `(r \times |G|)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense`
          matrix, where `r` is the projective rank of the `(n-1)`-th
          term of self, and `G` is the group upon which `R` is defined.
          ``M`` represents a chain.
        - ``check`` (optional bool) -- if ``True``, verify whether the
          input is in the kernel of the `(n-1)`-th boundary map.

        OUTPUT:

        A `n`-chain, represented by a `(s \times |G|)`
        :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix, where `s`
        is the projective rank of the `n`-th term of self.

        EXAMPLES:

        The example produces files. For safety reasons, we choose
        files in a temporary directory; it will be removed as soon
        as Sage is quit.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: R = H.resolution()
            sage: M1 = R.find_bounding_chain(1, MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,1,1,0,1]]))
            sage: print(M1)
            [1 0 0 0 1 0 0 0]
            [1 1 0 0 0 1 0 0]
            sage: print(R.applyDiff(1,M1))
            [0 1 1 0 1 1 0 1]
            sage: M2 = R.find_bounding_chain(2, MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[0,1,0,1,0,0,1,0],[0,0,0,0,0,1,0,0]]))
            sage: print(M2)
            [1 0 1 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            sage: print(R.applyDiff(2,M2))
            [0 1 0 1 0 0 1 0]
            [0 0 0 0 0 1 0 0]

        Note that by default it is not verified whether the input
        is in the image of the `n`-th boundary map. In this case,
        the output would be nonsense. So, in case of doubt, one may
        use the optional parameter ``check``::

            sage: FOO =  R.find_bounding_chain(2, MTX(MatrixSpace(GF(2), 2,8, implementation=MTX), [[0,1,0,1,0,0,1,0],[0,1,1,0,0,1,0,0]]))
            sage: print(FOO)
            [1 0 1 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            sage: print(R.applyDiff(2,FOO))
            [0 1 0 1 0 0 1 0]
            [0 0 1 0 0 1 0 0]
            sage: print(R.find_bounding_chain(2, MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[0,1,0,1,0,0,1,0],[0,1,1,0,0,1,0,0]]), check=True))
            Traceback (most recent call last):
            ...
            ValueError: The given chain is no cycle

        """
        if (n<1):
            raise IndexError('positive integer expected')
        while (n>=len(self.Diff)):
            self.nextDiff()
        if (M.nrows()!=self.Data.projrank[n-1]) or (M.ncols()!=self.G_Alg.Data.nontips):
            raise TypeError("Elements of the {} term of the resolution must be presented\nby ({} x {}) MTX matrices".format(Integer(n-1).ordinal_str(),self.Data.projrank[n-1],self.G_Alg.Data.nontips))
        coho_logger.info("Find bounding %d-cochain", self, n)
        cdef dict Autolift = self.Autolift.get(n,{})
        cdef int rk  = self.Data.projrank[n]
        cdef int rk_1= self.Data.projrank[n-1]
        cdef long fl  = self.G_Alg.Data.p
        cdef long nt  = self.G_Alg.Data.nontips
        cdef MTX  TMP, DUMMY
        cdef list Z
        cdef int k
        ##########################
        TMP = makeMTX(MatAlloc(fl, rk, nt))
        Z = M._rowlist_(0, rk_1-1)

        if check or (Autolift=={}):
            if n==1:
                if M[0,0]!=0:
                    raise ValueError("The given chain is no cycle")
            else:
                if self.applyDiff(n-1,M)._rowlist_(0,self.Data.projrank[n-2]-1).count(0)!=self.Data.projrank[n-2]*nt:
                    raise ValueError("The given chain is no cycle")
        if Autolift == {}:
            self.load_ugb(n)
            if (self.nRgs.ngs.r!=rk_1) or (self.nRgs.ngs.s != rk):
                raise ArithmeticError("Theoretical error")
            # in coho.c: innerPreimages(nRgs, images->Data, s, resol->group, this->Data),
            innerPreimages(self.nRgs, M.Data.Data, 1, self.G_Alg.Data, TMP.Data.Data)
            if check:
                coho_logger.info("Checking the result", self)
                if self.applyDiff(n,TMP)!=M:
                    raise ArithmeticError("lifting failed")
            return TMP
        cdef tuple Piv = tuple(Autolift['Piv'])
        for j in Piv:
            if Z[j]:
                DUMMY = Autolift[j][Z[j]]
                MatAdd(TMP.Data, DUMMY.Data)
        if check:
            coho_logger.info("Checking the result", self)
            if self.applyDiff(n,TMP)!=M:
                raise ArithmeticError("lifting failed")
        return TMP

    #################################
    # compose Chain Maps

    def composeChainMaps(self, MTX M1, MTX M2, long s, long r, long q):
        r"""
        Compose chain maps `M1: P_s \to P_r` with `M2: P_r\to P_q`, where `P` is ``self``.

        INPUT:

        - ``M1``, ``M2``  -- :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrices defining morphisms from
          the `s`-th to the `r`-th respectively from the `r`-th to the `q`-th term of self
        - ``s, r, q``  -- integers, refering to terms of self

        OUTPUT:

        A :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing the composition of ``M1`` with ``M2``,
        a chain map from the s-th to the q-th term of self.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()

        We verify that the composition of two differentials vanishes::

            sage: print(R.composeChainMaps(R[2],R[1],2,1,0))
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: print(R.composeChainMaps(R[3],R[2],3,2,1))
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]

        """
        if (s>len(self.Diff)) or (r>len(self.Diff)) or (q>len(self.Diff)) or (q<0) or (r<0) or (s<0):
            raise IndexError("Index out of range")
        if (M1._ncols != self.G_Alg.Data.nontips) or \
               (M2._ncols != self.G_Alg.Data.nontips):
            raise ValueError("Matrices representing chain maps must have |G|=%d columns"%(self.G_Alg.Data.nontips))
        if (M1._nrows != self.Data.projrank[s]*self.Data.projrank[r]):
            raise ValueError("Matrix representing the first chain map must have %d rows"%(self.Data.projrank[s]*self.Data.projrank[r]))
        if (M2._nrows != self.Data.projrank[r]*self.Data.projrank[q]):
            raise ValueError("Matrix representing the second chain map must have %d rows"%(self.Data.projrank[r]*self.Data.projrank[q]))
        if (M1.Data.Field != self.G_Alg.Data.p) or (M2.Data.Field != self.G_Alg.Data.p):
            raise ValueError("Matrices representing chain maps must be defined over GF(%d)"%(self.G_Alg.Data.p))
        coho_logger.info('Compose chain maps R_%d -> R_%d -> R_%d', self, s,r,q)
        cdef MTX OUT
        OUT = makeMTX(MatAlloc(self.G_Alg.Data.p, self.Data.projrank[s]*self.Data.projrank[q],self.G_Alg.Data.nontips))
        cdef Matrix_t *L
        cdef int i,j,k
        cdef int RK = self.Data.projrank[s]
        cdef int Rk = self.Data.projrank[r]
        cdef int rk = self.Data.projrank[q]
        cdef long nontips = self.G_Alg.Data.nontips
        FfSetNoc(nontips)
        cdef PTR M2_ji = M2.Data.Data
        # line ik of OUT is the sum of line ij of M1 times line jk of M2.
        for j from 0 <= j < Rk:
            for i from 0 <= i < rk:
                sig_on()
                L = leftActionMatrix(self.G_Alg.Data, M2_ji)
                for k from 0 <= k < RK:
                    FfAddMapRow(FfGetPtr(M1.Data.Data,k*Rk+j), L.Data, nontips, FfGetPtr(OUT.Data.Data,k*rk+i))
                M2_ji += FfCurrentRowSize
                MatFree(L)
                sig_off()
        OUT.set_immutable()
        return OUT

    def composeListOfMaps(self, MTX M1, long s, list L2):
        """
        Compose one chain map with a list of chain maps.

        INPUT:

        - ``M1``  -- :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix defining a morphism from
          the `s`-th to the `r`-th term of self
        - ``s``   -- an integer, referring to a term of self
        - ``L``   -- a list/tuple whose elements are triples ``(r, q_i, M_i)``, where
          ``M_i`` is a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix describing a morphism
          from the `r`-th to the `q_i`-th term of self

        OUTPUT:

        A list of triples ``[s,q_i,N_i]``, where ``N_i`` is a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense`
        matrix representing a morphism from the `s`-th to the `q_i`-th term of self, namely the
        composition of ``M`` with ``M_i``

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]])
            sage: c = R.CochainToChainmap(2,C)
            sage: c
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            2, 0, [1 0 0 0 0 0 0 0]
            )
            sage: L = [(2,1,R[2]), c]
            sage: Comp = R.composeListOfMaps(R[3],3,L)
            sage: R.composeChainMaps(R[3],L[0][2],3,2,1) == Comp[0][2]
            True
            sage: R.composeChainMaps(R[3],c[2],3,2,0) == Comp[1][2]
            True

        """
        # test input data
        r = L2[0][0]
        if (s>len(self.Diff)) or (r>=s):
            raise IndexError("Index out of range")
        if (M1._ncols != self.G_Alg.Data.nontips):
            raise ValueError("Matrices representing the first chain map must have |G|=%d columns"%(self.G_Alg.Data.nontips))
        if (M1._nrows != self.Data.projrank[s]*self.Data.projrank[r]):
            raise ValueError("Matrix representing the first chain map must have %d rows"%(self.Data.projrank[s]*self.Data.projrank[r]))
        if (M1.Data.Field != self.G_Alg.Data.p):
            raise ValueError("Matrices representing the first chain map must be defined over GF(%d)"%(self.G_Alg.Data.p))
        cdef tuple X
        for X in L2:
            ## make some tests implicit
            if  (X[1]>=r) or (X[1]<0):
                raise IndexError("Index out of range")
            if (X[2].ncols()!=self.G_Alg.Data.nontips):
                raise ValueError("Matrices representing chain maps must have |G|=%d columns"%(self.G_Alg.Data.nontips))
            if (X[2].nrows()!=self.Data.projrank[r]*self.Data.projrank[X[1]]):
                raise ValueError("Matrix representing a second chain map is of wrong size")

        cdef MTX IN1
        cdef MTX OUT1
        cdef Matrix_t *R
        cdef int i,j,k,a
        cdef int RK = self.Data.projrank[s]
        cdef int Rk = self.Data.projrank[r]
        cdef int loc_rk
        cdef int lenL2 = len(L2)
        cdef list rk = [self.Data.projrank[L2[a][1]] for a in range(len(L2))]
        cdef long nontips = self.G_Alg.Data.nontips
        cdef PTR IN1d, OUT1d, M1d
        FfSetNoc(nontips)
        # line ik of OUT[a] is the sum over j of line ij of M1 times line jk of L2[a][2].
        OUT = [[s, L2[a][1], makeMTX(MatAlloc(self.G_Alg.Data.p, self.Data.projrank[s]*rk[a],self.G_Alg.Data.nontips))] for a in range(len(L2))]
        M1d = M1.Data.Data
        for k from 0 <= k < RK:
            for j from 0 <= j < Rk:
                R = rightActionMatrix(self.G_Alg.Data, M1d)
                M1d += FfCurrentRowSize
                for a from 0 <= a < lenL2:
                    IN1 = L2[a][2]
                    OUT1 = OUT[a][2]
                    loc_rk = rk[a]
                    IN1d = FfGetPtr(IN1.Data.Data,j*loc_rk)
                    OUT1d = FfGetPtr(OUT1.Data.Data,k*loc_rk)
                    for i from 0 <= i < loc_rk:
                        FfAddMapRow(IN1d, R.Data, nontips, OUT1d)
                        IN1d += FfCurrentRowSize
                        OUT1d += FfCurrentRowSize
                MatFree(R)
        return OUT

    ################################################################
    ## Lift of Chain Maps

    def liftListOfMaps(self, list L):
        """
        Lift list of Chain Maps by one degree.

        INPUT:

        - ``L`` -- a list whose elements ``L[i]`` are triples ``(n,d_i,M_i)``, where the :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix ``M_i``
          represents a morphism from the `n`-th to the `(d_i)`-th term of self, `d_i<n`.

        OUTPUT:

        The function returns another list of triples, lifting the input to morphisms from
        the `(n+1)`-th to the `(d_i+1)` term of self.

        NOTE:

        Uses the autolift method, if possible. See :class:`pGroupCohomology.resolution.RESL`
        for an explanation of the notion 'lift' and of the autolift method.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]])
            sage: c = R.CochainToChainmap(2,C)
            sage: L = [(2,1,R[2]), c]
            sage: O = R.liftListOfMaps(L)
            sage: O
            [(
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
                  [0 0 0 0 0 0 0 0]
            3, 2, [0 0 0 0 0 0 0 0]
            ),
             (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 1 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            3, 1, [1 0 0 0 0 0 0 0]
            )]

        """
        coho_logger.info('Lift list of %d chain maps'%len(L), self)
        if L==[]:
            return []
        # n is the known degree, must be lifted to n+1
        cdef int n = L[0][0]
        cdef list OUT
        if (n>=len(self.Diff)):
            raise IndexError("Index %d bigger than known degree %d"%(n,self.deg()))
        cdef tuple X
        cdef MTX MX
        cdef int Indi = 0
        cdef int X0,X1
        for X0,X1,MX in L:
            if (X0!=n):
                raise ValueError("All chain maps in the list must have the same source")
            if (X1>=n) or (X1<0):
                raise IndexError("Index out of range")
            if (MX.Data.Noc!=self.G_Alg.Data.nontips):
                raise ValueError("Matrices representing chain maps must have |G|=%d columns"%(self.G_Alg.Data.nontips))
            if (MX.Data.Nor!=self.Data.projrank[X0]*self.Data.projrank[X1]):
                raise ValueError("Matrix representing input chain map must have %d*%d rows"%(self.Data.projrank[X0],self.Data.projrank[X1]))
            Indi += MX.Data.Nor
        ######################
        # If separate lifts appear to be better
        if Indi<self[n+1].nrows():
            OUT = [self.liftChainMap((n,X1,MX)) for X0,X1,MX in L]
            return OUT
        ######################
        # Otherwise:
        coho_logger.debug('> Compose list of %d Chain Maps with Differential'%(len(L)), self)
        COMPOS = self.composeListOfMaps(self[n+1],n+1,L)
        cdef int RK  = self.Data.projrank[n+1]
        cdef int fl  = self.G_Alg.Data.p
        cdef int nt  = self.G_Alg.Data.nontips
        OUT = [(n+1,X1+1, makeMTX(MatAlloc(fl, RK*self.Data.projrank[X1+1], nt))) for X0,X1,MX in L]
        cdef MTX Compos1
        cdef MTX Out1
        cdef MTX  TMP,DUMMY
        cdef int a,i,j, projrk
        cdef int lenCOMPOS = len(COMPOS)
        cdef list Z
        cdef tuple Piv
        cdef dict Autolift
        sig_on()
        for a from 0 <= a < lenCOMPOS:
            Out1 = OUT[a][2]
            Compos = COMPOS[a] # this is a list: low degree, high degree,matrix
            Compos1 = Compos[2] # this is the matrix
            Autolift = self.Autolift.get(Compos[1]+1,{})
            if Autolift:
                coho_logger.debug('> Lift with the autolift method', self)
                Piv = tuple(Autolift['Piv'])
                ##########################
                # Lift each "long row"
                for i from 0 <= i < RK:
                    # Z is the list of coefficients of Compos1,
                    # hence, we look up the pivots and add up the Autolift matrices
                    Z = Compos1._rowlist_(i*self.Data.projrank[Compos[1]], (i+1)*self.Data.projrank[Compos[1]]-1)
                    projrk = self.Data.projrank[Compos[1]+1]
                    TMP = makeMTX(MatAlloc(fl, projrk, nt))
                    for j in Piv:
                        if Z[j]:
                            DUMMY = Autolift[j][Z[j]]
                            MatAdd(TMP.Data, DUMMY.Data)
                    memcpy(MatGetPtr(Out1.Data, i*projrk), TMP.Data.Data, FfCurrentRowSize*projrk)
            else:
                coho_logger.debug('> Lift with Urbild Groebner basis', self)
                self.load_ugb(Compos[1]+1)
                if (self.nRgs.ngs.r!=self.Data.projrank[Compos[1]]) or (self.nRgs.ngs.s != self.Data.projrank[Compos[1]+1]):
                    sig_off()
                    raise ArithmeticError("Theoretical error")
                ## in coho.c: innerPreimages(nRgs, images->d, s, resol->group, this->d),
                coho_logger.debug('> Compute preimages in degree %d'%(Compos[1]+1), self)
                innerPreimages(self.nRgs, Compos1.Data.Data, RK, self.G_Alg.Data, Out1.Data.Data)
        sig_off()
        return OUT


    def liftChainMap(self, X):
        """
        Lift Chain Map.

        INPUT:

        ``(n,d,M)`` -- a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix ``M`` representing a morphism from
        the `n`-th to the `d`-th term of self, with `d<n`.

        OUTPUT:

        ``(n+1,d+1,N)`` -- A :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix ``N`` representing the lift of
        ``M`` to a morphism from the `(n+1)`-th to the `(d+1)`-th term of self.

        NOTE:

        Uses the autolift method, if possible. See :class:`~pGroupCohomology.resolution.RESL` for an
        explanation of the notion 'lift' and of the autolift method.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]])
            sage: c = R.CochainToChainmap(2,C)
            sage: c
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            2, 0, [1 0 0 0 0 0 0 0]
            )
            sage: cLift = R.liftChainMap(c)
            sage: cLift
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 1 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            3, 1, [1 0 0 0 0 0 0 0]
            )

        """
        if not (isinstance(X,tuple) or isinstance(X,list)):
            raise TypeError("Chain map must be presented by a tuple or list")
        if len(X)!=3:
            raise ValueError("Chain map must be presented by a tuple or list of length 3")
        cdef int n,d
        cdef MTX M
        (n,d,M)=X
        if (d>=n) or (d<0):
            raise IndexError("Index out of range")
        if (M.Data.Noc!=self.G_Alg.Data.nontips):
            raise ValueError("Matrices representing chain maps must have |G|=%d columns"%(self.G_Alg.Data.nontips))
        while (n>=len(self.Diff)):
            self.nextDiff()
        if (M.Data.Nor!=self.Data.projrank[n]*self.Data.projrank[d]):
            raise ValueError("Matrix representing the input chain map must have %d rows"%(self.Data.projrank[n]*self.Data.projrank[d]))
        cdef dict Autolift = self.Autolift.get(d+1,{})
        if not Autolift:
            return (n+1,d+1,self.ugb_liftChainMap(n+1,d+1,M))
        cdef MTX Compos
        Compos = self.composeChainMaps(self[n+1],M, n+1,n,d)
        coho_logger.debug('> Lift with the autolift method', self)
        cdef int RK  = self.Data.projrank[n+1]
        cdef int rk  = self.Data.projrank[d+1]
        cdef int rk_1= self.Data.projrank[d]
        cdef long fl  = self.G_Alg.Data.p
        cdef long nt  = self.G_Alg.Data.nontips
        cdef MTX OUT = makeMTX(MatAlloc(fl, RK*rk, nt))
        cdef MTX  TMP, DUMMY
        cdef list Z
        cdef int i,k
        FfSetNoc(nt)
        cdef tuple Piv = tuple(Autolift['Piv'])
        ##########################
        # Lift each "long row"
        for i from 0 <= i < RK:
            Z = Compos._rowlist_(i*rk_1, (i+1)*rk_1-1)
            TMP = makeMTX(MatAlloc(fl, rk, nt))
            for j in Piv:
                if Z[j]:
                    DUMMY = Autolift[j][Z[j]]
                    MatAdd(TMP.Data, DUMMY.Data)
            memcpy(MatGetPtr(OUT.Data, i*rk), TMP.Data.Data, FfCurrentRowSize*rk)
    ##################
        return (n+1,d+1,OUT)

    def ugb_liftChainMap(self, long n, long d, MTX M):
        """
        Lift a chain map using Urbild Groebner bases.

        INPUT:

        - n, d -- integers, `d<n`
        - M    -- a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing a morphism from
          the `(n-1)`-th to the `(d-1)`-th term of self.

        OUTPUT:

        A :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing the lift to a morphism
        from the `n`-th to the `d`-th term of self.

        NOTE:

        See :class:`~pGroupCohomology.resolution.RESL` for an explanation of the notion
        'lift'. It certainly is odd that the syntax of this method differs from the syntax
        of :meth:`liftChainMap`. Sorry.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]])
            sage: c = R.CochainToChainmap(2,C)
            sage: c
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            2, 0, [1 0 0 0 0 0 0 0]
            )
            sage: cLift = R.ugb_liftChainMap(3,1,c[2])
            sage: cLift
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 0 1 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]

        """
        if (n>len(self.Diff)) or (d>=n) or (d<1):
            raise IndexError("Index out of range")
        if (M.ncols()!=self.G_Alg.Data.nontips):
            raise ValueError("Matrices representing chain maps must have |G|=%d columns"%(self.G_Alg.Data.nontips))
        if (M.nrows()!=self.Data.projrank[n-1]*self.Data.projrank[d-1]):
            raise ValueError("Matrix representing the input chain map must have %d rows"%(self.Data.projrank[n-1]*self.Data.projrank[d-1]))
        cdef MTX Compos
        Compos = self.composeChainMaps(self[n],M, n,n-1,d-1)
        coho_logger.debug('Lift with Urbild Groebner basis in degree %d'%(d), self)
        # from cohring.c: resolutionPreimages(resol, d, projrank[n], compos)
        # in coho.c, this corresponds to determinePreimagesConventionally(resol, d, projrank[n], compos, this)
        # which, in turn, unfolds to:
        cdef MTX OUT
        sig_on()
        OUT = makeMTX(MatAlloc(self.G_Alg.Data.p, self.Data.projrank[d]*self.Data.projrank[n], self.G_Alg.Data.nontips))
        sig_off()
        self.load_ugb(d)
        if (self.nRgs.ngs.r!=self.Data.projrank[d-1]) or (self.nRgs.ngs.s != self.Data.projrank[d]):
            raise ArithmeticError("Theoretical error")
        # in coho.c: innerPreimages(nRgs, images->d, s, resol->group, this->d),
        sig_on()
        innerPreimages(self.nRgs, Compos.Data.Data, self.Data.projrank[n], self.G_Alg.Data, OUT.Data.Data)
        sig_off()
        OUT.set_immutable()
        return OUT

    #############################################
    # Yoneda complex

    def yoneda_coboundary(self, MTX X, MTX Y, int n, int i):
        r"""
        INPUT:

        - ``X, Y``: :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrices representing the terms `\phi_n^i: P_n\to P_{n-i}`
          and `\phi_{n+1}^i: P_{n+1}\to P_{n-i+1}` of an element `\phi^i` of degree `i` in the
          Yoneda complex, where `P_\ast` is the underlying resolution.
        - ``n, i``: integers, `i \le n`.

        OUTPUT:

        ``Z``: :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing the term
        `(\partial \phi^i)_{n+1}: P_{n+1}\to P_{n-i}` representing the Yoneda coboundary of `\phi^i`.

        NOTE:

        This method is mainly of internal use.

        THEORY:

        If `d_\ast: P_\ast \to P_{\ast-1}` denotes the boundary maps of `P_\ast` then
        `(\partial \phi^i)_{n+1} = \phi_n\circ d_{n+1} - (-1)^i d_{n-i+1}\circ \phi_{n+1}^i`.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: YC = (H.2.yoneda_cocycle()*H.3.yoneda_cocycle()).find_cobounding_yoneda_cochains()
            sage: [H.resolution().yoneda_coboundary(Y[0],Y[1],Y.deg(),Y.deg())==Y.coboundary()[0] for Y in YC]
            [True, True, True, True]

        """
        if i>n:
            raise ValueError("The second integer argument must not exceed the first integer argument")
        if i%2:
            return self.composeChainMaps(self[n+1],X, n+1,n,n-i) + self.composeChainMaps(Y,self[n-i+1], n+1,n-i+1,n-i)
        return self.composeChainMaps(self[n+1],X, n+1,n,n-i) - self.composeChainMaps(Y,self[n-i+1], n+1,n-i+1,n-i)

    #############################################
    # Conversion Chain Map <-> Cochain

    cpdef tuple CochainToChainmap(self, long n, MTX Coc):
        """
        Represent a cochain (given by a matrix) by a chain map to the zeroeth term of ``self``

        INPUT:
        - n -- an integer
        - C -- a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix with only one row, representing a `n`-cochain

        OUTPUT:

        ``(n,0,M)``, where the :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix ``M`` represents the lowest term
        of a chain map of degree `n`.

        NOTE:

        By our choice of basis for modules over the group algebra, the matrix ``M`` is zero
        except in the first column, which is given by the transpose of ``C``.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]])
            sage: c = R.CochainToChainmap(2,C)
            sage: c
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            2, 0, [1 0 0 0 0 0 0 0]
            )

        """
        if (n>len(self.Diff)) or (n<0):
            raise IndexError("Index out of range")
        if (Coc._ncols != self.Data.projrank[n]) or (Coc._nrows != 1):
            raise ValueError("expect (%d x %d) MTX matrix, got %s"%(1,self.Data.projrank[n],str(Coc)))
        if (Coc.Data.Field != self.G_Alg.Data.p):
            raise ValueError("Matrix must be defined over GF(%d)"%(self.G_Alg.Data.p))
        cdef MTX OUT
        cdef FEL Coc_f
        OUT = makeMTX(MatAlloc(self.G_Alg.Data.p, self.Data.projrank[n], self.G_Alg.Data.nontips))
        cdef int i
        cdef int projrk = self.Data.projrank[n]
        FfSetField(OUT.Data.Field)
        FfSetNoc(OUT.Data.Noc)
        for i from 0 <= i < projrk:
            Coc_f = FfExtract(Coc.Data.Data, i)
            if Coc_f != FF_ZERO:
                FfInsert(FfGetPtr(OUT.Data.Data,i), 0, Coc_f)
        OUT.set_immutable()
        return (n,0,OUT)

    def ChainmapToCochain(self, object X):
        r"""
        Represent a chain map of degree `n` by a `n`-cochain.

        INPUT:

        ``(n,0,M)`` -- ``M`` is a `\operatorname{rank}(P_n) \times |G|` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix,
        where `P_n` is the `n`-th term of self and `G` is the finite `p`-group under consideration.

        OUTPUT:

        A `1 \times |G|` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing a `n`-cochain.

        NOTE:

        By our choice of bases of modules over the group algebra, the result only
        depends on the first column of ``M``.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]])
            sage: print(R.ChainmapToCochain(R.CochainToChainmap(2,C)))
            [1 0 1]

        """
        if not (isinstance(X,tuple) or isinstance(X,list)):
            raise TypeError("Chain map must be given by a list or tuple")
        if len(X)!=3:
            raise ValueError("Chain map must be given by a list or tuple of length 3")
        n=X[0]
        if (n>len(self.Diff)) or (n<0) or (X[1]!=0):
            raise IndexError("Index out of range")
        if not (isinstance(X[2],MTX)):
            raise TypeError("Chain map must be described by an {} matrix".format(MTX))
        cdef MTX CM, OUT
        cdef Py_ssize_t i,nr
        CM = X[2]
        if (CM._nrows != self.Data.projrank[n]) or (CM._ncols != self.G_Alg.Data.nontips):
            raise ValueError("expect (%d x %d) matrix"%(self.Data.projrank[n],self.G_Alg.Data.nontips))
        if (CM.Data.Field != self.G_Alg.Data.p):
            raise ValueError("Matrix must be defined over GF(%d)"%(self.G_Alg.Data.p))
        OUT = makeMTX(MatAlloc(self.G_Alg.Data.p, 1, CM._nrows))
        FfSetField(OUT.Data.Field)
        FfSetNoc(OUT.Data.Noc)
        for i from 0 <= i < CM._nrows:
            FfInsert(FfGetPtr(OUT.Data.Data,0), i, FfExtract(MatGetPtr(CM.Data,i), 0))
        OUT.set_immutable()
        return OUT


#####################################################################
#####################################################################
## Container for Lifts of cochains
#####################################################################
#####################################################################

cdef class LIFTcontainer:
    """
    An extension class whose purpose is to cache the lifts of chain maps of a resolution to itself.

    A typical use case is the computation of cohomology rings. One
    frequently has to compute cup products of `m`- and `n`-cochains.
    To that purpose, the cochains are transformed into chain maps
    of degree `m` and `n`. Then, the two chain maps are composed,
    and the result is transformed into a `(m+n)`-cochain. For
    computing the composition, the `m`-th lift of the second chain
    map needs to be known.

    Now, if many cup products have to be computed, it is reasonable
    to cache previously computed lifts.

    NOTE:

    Internally, any :class:`~pGroupCohomology.resolution.RESL`
    instance has a member that is a
    :class:`~pGroupCohomology.resolution.LIFTcontainer` instance,
    and if the cup product of cochains is computed (see
    :class:`~pGroupCohomology.cochain.COCH` for more details),
    caching is automatically done.

    EXAMPLE::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]], mutable=False)
            sage: C3 = R.liftChainMap(R.CochainToChainmap(2,C))
            sage: C3
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 1 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            3, 1, [1 0 0 0 0 0 0 0]
            )
            sage: L[3,2,C] = C3[2]
            sage: L.out()
            {(3, 2): {[1 0 1]: [1 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]
              [0 0 0 1 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]}}
            sage: L[3,2,C]
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 0 1 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]

    """
    ####################
    # init, dealloc, repr
    def __init__(self,R):
        """
        INPUT:

        A resolution of a finite `p`-group (:class:`RESL`).

        TEST::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)   #indirect doctest
            sage: L.out()
            {}

        """
        if not isinstance(R,RESL):
            raise TypeError("argument of type {} expected".format(RESL))
        cdef RESL tmp
        tmp=R
        self.Parent = R
        self.Data = {}

    def out(self):
        """
        Return the dictionary of cached lifts.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)
            sage: L.out()
            {}

        In principle, any data can be stored in a LIFTcontainer.
        ::

            sage: L[1,2,3] = 4
            sage: L.out()
            {(1, 2): {3: 4}}

        """
        return self.Data

    ####################
    # get/set item
    def __getitem__(self,key):
        """
        Return one cached object.

        INPUT:

        - n -- integer
        - d -- integer
        - M -- A :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix with a
          single row, representing a `d`-cochain

        OUTPUT:

        - A :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing a
          morphism from the `n`-th to the `(n-d)`-th term of a
          resolution, corresponding to the chain map defined by `M`
          ("lift to degree `n`")
        - None, if the requested lift was not cached.

        NOTE:

        The situation described in the INPUT and OUTPUT sections is
        the intended use case. In principle, *anything* can be stored
        in a LIFTcontainer.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]], mutable=False)
            sage: C3 = R.liftChainMap(R.CochainToChainmap(2,C))
            sage: C3
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 1 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            3, 1, [1 0 0 0 0 0 0 0]
            )
            sage: L[3,2,C] = C3[2]
            sage: L.out()
            {(3, 2): {[1 0 1]: [1 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]
              [0 0 0 1 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]}}
            sage: print(L[3,2,C])   # indirect doctest
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]
            [0 0 0 1 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [1 0 0 0 0 0 0 0]

        """
        if len(key)!=3:
            raise KeyError("key must be a list or tuple of three items")
        if coho_options['sparse']:
            self.Parent.free_ugb()
        cdef int n,d
        n=key[0]
        d=key[1]
        cdef dict D = self.Data.get((n,d),{})
        s = D.pop('file','')
        if (not s) and isinstance(D.get(1,None), tuple):
            # Problem: the number 1 evaluates equal to
            # the MTX matrix [1]. That hasn't been the
            # case in the past. Now we have to deal with
            # it, since in old data it is assumed that
            # they aren't equal.
            s = ''
        else: # That's old exported data
            s = D.pop(1,'')
        if s:
            try:
                if s.endswith('.sobj'):
                    D.update(load(s))  # realpath here?
                else:
                    D.update(load(s+'.sobj')) # realpath here?
            except (OSError, IOError), msg:
                pass
            self.Data[(n,d)] = D
        return self.Data.get((n,d),{}).get(key[2],None)

    def __setitem__(self,key,v):
        """
        Cache some lift of a cochain.

        INPUT:

        - n,d -- integers
        - M   -- M is a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix with
          a single row, representing a `d`-cochain.
        - N   -- a morphism from the `n`-th to the `(n-d)`-the term of
          a resolution, obtained by considering the `d`-cochain given
          by `M` as a chain map of degree `d`.

        NOTE:

        The situation described in the INPUT section is the intended use case.
        In principle, anything can be stored in a LIFTcontainer.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]], mutable=False)
            sage: C3 = R.liftChainMap(R.CochainToChainmap(2,C))
            sage: C3
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 1 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            3, 1, [1 0 0 0 0 0 0 0]
            )
            sage: L[3,2,C] = C3[2]   # indirect doctest
            sage: L.out()
            {(3, 2): {[1 0 1]: [1 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]
              [0 0 0 1 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]}}

        """
        if len(key)!=3:
            raise KeyError("key must be a list or tuple of three items")
        cdef int n,d
        n=key[0]
        d=key[1]
        if not self.Data.has_key((n,d)):
            self.Data[(n,d)] = {}
        cdef dict D = self.Data[(n,d)]
        s = D.pop('file','')
        if (not s) and isinstance(D.get(1,None), tuple):
            # Problem: the number 1 evaluates equal to
            # the MTX matrix [1]. That hasn't been the
            # case in the past. Now we have to deal with
            # it, since in old data it is assumed that
            # they aren't equal.
            s = ''
        else: # That's old exported data
            s = D.pop(1,'')
        if s:
            try:
                if s.endswith('.sobj'):
                    D.update(load(s))  # realpath here?
                else:
                    D.update(load(s+'.sobj'))  # realpath here?
            except Exception, msg:
                pass
            self.Data[(n,d)] = D
        self.Data[(n,d)][key[2]] = v

    def __delitem__(self,key):
        """
        Delete the cache for one lift.

        INPUT:

        - n, d -- integers
        - M   -- M is a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix with a single row, representing a `d`-cochain

        NOTE:

        The situation described in the INPUT section is the intended use case.
        In principle, anything can be stored in a LIFTcontainer.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]], mutable=False)
            sage: C3 = R.liftChainMap(R.CochainToChainmap(2,C))
            sage: C3
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 1 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            3, 1, [1 0 0 0 0 0 0 0]
            )
            sage: L[3,2,C] = C3[2]
            sage: L.out()
            {(3, 2): {[1 0 1]: [1 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]
              [0 0 0 1 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]}}
            sage: del L[3,2,C]
            sage: L.out()
            {(3, 2): {}}

        """
        if len(key)!=3:
            raise KeyError("key must be a list or tuple of three items")
        cdef int n,d
        n=key[0]
        d=key[1]
        cdef dict D = self.Data.get((n,d),{})
        s = D.pop('file','')
        if (not s) and isinstance(D.get(1,None), tuple):
            # Problem: the number 1 evaluates equal to
            # the MTX matrix [1]. That hasn't been the
            # case in the past. Now we have to deal with
            # it, since in old data it is assumed that
            # they aren't equal.
            s = ''
        else: # That's old exported data
            s = D.pop(1,'')
        if s:
            try:
                if s.endswith('.sobj'):
                    D.update(load(s))  # realpath here?
                else:
                    D.update(load(s+'.sobj'))  # realpath here?
            except Exception, msg:
                raise msg
        D.pop(key[2],None)
        self.Data[(n,d)]=D

    def parent(self):
        """
        Return the resolution for which ``self`` was defined.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)
            sage: R is L.parent()
            True

        """
        return self.Parent

    ###################
    ## exporting
    def export(self):
        """
        Store cached lifts on disk. The file names are determined by the parent of ``self``.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, RESL, LIFTcontainer
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: res_folder=os.path.join(gps_folder,'dat')
            sage: R=RESL(gstem,gps_folder,res_folder)
            sage: L = LIFTcontainer(R)
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: R.nextDiff()
            sage: C = MTX(MatrixSpace(GF(2),1,3, implementation=MTX), [[1,0,1]], mutable=False)
            sage: C3 = R.liftChainMap(R.CochainToChainmap(2,C))
            sage: C3
            (
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
                  [1 0 0 0 0 0 0 0]
                  [0 0 0 1 0 0 0 0]
                  [0 0 0 0 0 0 0 0]
            3, 1, [1 0 0 0 0 0 0 0]
            )
            sage: L[3,2,C] = C3[2]
            sage: L.out()
            {(3, 2): {[1 0 1]: [1 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]
              [0 0 0 1 0 0 0 0]
              [0 0 0 0 0 0 0 0]
              [1 0 0 0 0 0 0 0]}}
            sage: L.export()
            sage: L.out()
            {(3, 2): {'file': '.../8gp3/dat/L8gp3n3d2'}}

        Here are the saved contents::

            sage: E = load(L.out()[(3,2)][1])
            sage: E
            [(
                     [1 0 0 0 0 0 0 0]
                     [0 0 0 0 0 0 0 0]
                     [0 0 0 0 0 0 0 0]
                     [0 0 0 0 0 0 0 0]
                     [1 0 0 0 0 0 0 0]
                     [0 0 0 1 0 0 0 0]
                     [0 0 0 0 0 0 0 0]
            [1 0 1], [1 0 0 0 0 0 0 0]
            )]
            sage: E[0][0] == C
            True
            sage: E[0][1] == C3[2]
            True

        """
        cdef dict D
        import os
        for X,D in self.Data.items():
            s = D.pop('file','')
            if (not s) and isinstance(D.get(1,None), tuple):
                # Problem: the number 1 evaluates equal to
                # the MTX matrix [1]. That hasn't been the
                # case in the past. Now we have to deal with
                # it, since in old data it is assumed that
                # they aren't equal.
                s = ''
            else: # That's old exported data
                s = D.pop(1,'')
            if s:
                if len(D)>1:
                    if s.endswith('.sobj'):
                        D.update(load(s))  # realpath here?
                    else:
                        D.update(load(s+'.sobj'))  # realpath here?
                    try:
                        del D['file']
                    except KeyError:
                        coho_logger.debug("updating old data", self.Parent)
                        try:
                            del D[1]
                        except KeyError:
                            pass
                    safe_save(D.items(),s)
                    D = {'file':s}
            else:
                safe_save(D.items(),os.path.join(self.Parent.res_folder,'L'+self.Parent.gstem+'n'+str(X[0])+'d'+str(X[1])))
                self.Data[X] = {'file':os.path.join(self.Parent.res_folder,'L'+self.Parent.gstem+'n'+str(X[0])+'d'+str(X[1]))}

#####################################################################
#####################################################################
## Group-Algebra extension type ( kG, G a finite p-group, k=GF(p)
#####################################################################
#####################################################################

cdef class G_ALG:
    """
    A wrapper for David Green's C-type for group algebras of finite `p`-groups.

    NOTE:

    This extension class is internally used in :class:`~pGroupCohomology.resolution.RESL`.
    Its purpose is simply to provide a couple of very basic methods
    around the underlying C-type.

    **The user is warned not to use this class independently!**

    When an instance of :class:`~pGroupCohomology.resolution.G_ALG` is attribute of an
    instance of :class:`~pGroupCohomology.resolution.RESL`, they share some C-data. So,
    when deallocating them, it has to be taken care that the shared data are not freed
    twice (which would result in a segmentation fault). Our solution is that these C-data
    are freed when the :class:`~pGroupCohomology.resolution.RESL` instance is deallocated,
    but are usually *not* freed if the :class:`~pGroupCohomology.resolution.G_ALG` instance
    is deallocated.

    Hence, if one would create a :class:`~pGroupCohomology.resolution.G_ALG` instance
    independent from a :class:`~pGroupCohomology.resolution.RESL` instance, the C-data
    would not be freed, resulting in a memory leak. Our solution for this second problem
    is to provide an optional argument 'dependent'. If it is ``True`` (which is default)
    then the :class:`~pGroupCohomology.resolution.G_ALG` instance behaves like being part
    of a :class:`~pGroupCohomology.resolution.RESL` instance, and the C-data are not
    deallocated when the instance is deleted.

    In the following examples, we define ``dependent=False``, and then the C-data will
    be properly deallocated.

    An instance of :class:`~pGroupCohomology.resolution.G_ALG` can be created using
    files that are created with :func:`~pGroupCohomology.resolution.makeGroupData` or
    :func:`~pGroupCohomology.resolution.makeSpecialGroupData`.

    EXAMPLES:

    The example produces files. For safety reasons, we choose files
    in a temporary directory; it will be removed as soon as Sage is quit.
    First, we create the basic data for the dihedral group of order 8
    (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

        sage: tmp_root = tmp_dir()
        sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
        sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
        sage: makeGroupData(8,3,folder=tmp_root)
        sage: gstem='8gp3'
        sage: gps_folder=os.path.join(tmp_root,gstem)
        sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
        sage: G
        GF(2)[8gp3]

    """
    ####################
    # init, dealloc, repr
    def __init__(self,gstem,folder=None,dependent=True,groupname = None):
        """
        INPUT:

        - ``gstem`` -- string that identifies a group
          and determines the file name under which group data
          are stored.
        - ``folder`` -- optional string that determines a folder
          in which data are stored.
        - ``dependent`` -- optional bool, default ``True``. If
          it is ``True``, it is assumed that this instance is
          a member of a :class:`~pGroupCohomology.resolution.RESL`
          instance. This information is used when deallocating
          the underlying C-data.
        - ``groupname`` -- another string that identifies the group in
          a more human-readable way. Note that it is ignored when pickling.

        TEST::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)    #indirect doctest
            sage: G
            GF(2)[8gp3]

        """
        if folder is None:
            folder = ''
        if not (isinstance(gstem,str) and isinstance(folder,str)):
            raise TypeError("string expected")
        if gstem=='':
            self.Data = newGroupRecord()
        else:
            self.gstem=gstem
            f = os.path.join(folder,gstem)
            self.Data = fullyLoadedGroupRecord(f)
        self.groupname = groupname
        self.dependent=dependent

    def __dealloc__(self):
        """
        Deallocate C-data for a :class:`~pGroupCohomology.resolution.G_ALG` instance.

        The instance must *not* be member of a :class:`~pGroupCohomology.resolution.RESL` instance!

        See :class:`~pGroupCohomology.resolution.G_ALG` for a more detailed account.

        TEST::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
            sage: G
            GF(2)[8gp3]
            sage: del G       #indirect doctest

        """
        if self.dependent:
            return
        if self.Data:
            freeGroupRecord(self.Data)

    def __repr__(self):
        """
        Return a brief description of the group algebra.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        First, we create the basic data for the dihedral group of order 8
        (compare :func:`~pGroupCohomology.resolution.makeGroupData`)::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
            sage: G   # indirect doctest
            GF(2)[8gp3]

        A nicer print representation is obtained by either providing the ``groupname``
        keyword argument on initialisation, or obtaining the resolution from
        a cohomology ring, which internally provides the group name as well::

            sage: G_ALG(gstem,folder=gps_folder,dependent=False, groupname="D_8")
            GF(2)[D_8]
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(64,82)
            sage: H.resolution().G_ALG()
            GF(2)[Syl2(Sz(8))]

        """
        if self.Data.p:
            return "GF(%d)[%s]"%(self.Data.p,self.groupname or self.gstem)
        else:
            return "Unspecified group algebra"
    ######################
    # ==, <,> etc
    def __richcmp__(self, other, x):
        """
        Compare two instances of G_ALG.

        NOTE:

        It is only tested whether the underlying finite prime field is
        the same and whether the given "gstem" (group stem name) coincides.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: makeGroupData(8,2,folder=tmp_root)
            sage: gstem1='8gp3'
            sage: gstem2='8gp2'
            sage: gps_folder1=os.path.join(tmp_root,gstem1)
            sage: gps_folder2=os.path.join(tmp_root,gstem2)
            sage: G = G_ALG(gstem1,folder=gps_folder1,dependent=False)
            sage: G2 = G_ALG(gstem1,folder=gps_folder1,dependent=False)
            sage: H = G_ALG(gstem2,folder=gps_folder2,dependent=False)
            sage: H == G   # indirect doctest
            False
            sage: H != G
            True
            sage: G == G2
            True
            sage: G is G2
            False

        Of course, ``<`` or ``>`` really makes no sense. The ordering
        is obtained from the group stem name and the field characteristic.

            sage: G > H
            True

        """
        # < 0, <= 1, == 2, != 3, > 4, >= 5
        cdef G_ALG SELF, OTHER
        if x==2:
            if not (isinstance(self, G_ALG) and isinstance(other, G_ALG)):
                return False
            SELF = self
            OTHER = other
            return (SELF.gstem, SELF.Data.p) == (OTHER.gstem, OTHER.Data.p)
        if x==3:
            if not (isinstance(self, G_ALG) and isinstance(other, G_ALG)):
                return True
            SELF = self
            OTHER = other
            return (SELF.gstem, SELF.Data.p) != (OTHER.gstem, OTHER.Data.p)
        if x==1:
            if not (isinstance(self, G_ALG) and isinstance(other, G_ALG)):
                return type(self) <= type(other)
            SELF = self
            OTHER = other
            return (SELF.gstem, SELF.Data.p) <= (OTHER.gstem, OTHER.Data.p)
        if (x==5):
            if not (isinstance(self, G_ALG) and isinstance(other, G_ALG)):
                return type(self) >= type(other)
            SELF = self
            OTHER = other
            return (SELF.gstem, SELF.Data.p) >= (OTHER.gstem, OTHER.Data.p)
        if x==0:
            if not (isinstance(self, G_ALG) and isinstance(other, G_ALG)):
                return type(self) < type(other)
            SELF = self
            OTHER = other
            return (SELF.gstem, SELF.Data.p) < (OTHER.gstem, OTHER.Data.p)
        if not (isinstance(self, G_ALG) and isinstance(other, G_ALG)):
            return type(self) > type(other)
        SELF = self
        OTHER = other
        return (SELF.gstem, SELF.Data.p) > (OTHER.gstem, OTHER.Data.p)

    ######################
    ## structural parts
    def order(G_ALG self):
        """
        Return order of the group.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
            sage: G.order()
            8

        """
        return self.Data.nontips

    def coef(G_ALG self):
        """
        Return the characteristic of the base field.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
            sage: G.coef()
            2

        """
        return self.Data.p

    ######################
    ## group actions
    def r_action(self, MTX M):
        r"""
        Return matrix for right action on kG by the element represented by a vector.

        INPUT:

        M -- a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix with a single row and `|G|` columns, representing
        an element of the group algebra of a finite `p`-group `G`

        OUTPUT:

        A `|G|\times |G|` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix describing the right action of the
        given element on the group algebra. The result of the action is obtained by matrix multiplication
        from the right side.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
            sage: print(G.r_action(MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[1,0,0,1,0,1,1,0]])))
            [1 0 0 1 0 1 1 0]
            [0 1 0 0 0 0 0 1]
            [0 0 1 0 0 0 1 1]
            [0 0 0 1 0 0 0 1]
            [0 0 0 0 1 0 0 0]
            [0 0 0 0 0 1 0 0]
            [0 0 0 0 0 0 1 0]
            [0 0 0 0 0 0 0 1]
            sage: MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,0,0,0,0]])*G.r_action(MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,1,0,0,0]]))
            [0 0 0 1 1 1 0 0]
            sage: G.kG_map(MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,0,0,0,0]]), MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,1,0,0,0]]))
            [0 0 0 1 1 1 0 0]

        """
        if not self.Data.p:
            raise ValueError("Modulus is not specified")
        if (M._nrows != 1) or (M._ncols != self.Data.nontips):
            raise ValueError("Parameter must be a row vector of size %d"%(self.Data.nontips))
        if (M.Data.Field != self.Data.p):
            raise ValueError("Matrix must be defined over GF(%d)"%(self.Data.p))
        cdef MTX OUT
        OUT  = makeMTX(MatAlloc(self.Data.p, self.Data.nontips,self.Data.nontips))
        innerRightActionMatrix(self.Data, M.Data.Data, OUT.Data.Data)
        OUT.set_immutable()
        return OUT

    def l_action(self, MTX M):
        r"""
        Return matrix for left action on `kG` by the element represented by a vector.

        INPUT:

        M -- a :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix with a single row and `|G|` columns, representing
        an element of the group algebra of a finite `p`-group `G`

        OUTPUT:

        A `|G|\times |G|` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix describing the left action of the
        given element on the group algebra. The result of the left action is obtained by matrix
        multiplication from the *right* side.

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
            sage: G.l_action(MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[1,0,0,1,0,1,1,0]]))
            [1 0 0 1 0 1 1 0]
            [0 1 0 0 0 1 0 1]
            [0 0 1 0 0 0 0 1]
            [0 0 0 1 0 0 0 1]
            [0 0 0 0 1 0 0 0]
            [0 0 0 0 0 1 0 0]
            [0 0 0 0 0 0 1 0]
            [0 0 0 0 0 0 0 1]
            sage: MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,0,0,0,0]])*G.l_action(MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,1,0,0,0]]))
            [0 0 0 1 1 0 1 0]
            sage: G.kG_map(MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,1,0,0,0]]),MTX(MatrixSpace(GF(2),1,8, implementation=MTX), [[0,1,1,0,0,0,0,0]]))
            [0 0 0 1 1 0 1 0]

        """
        if not self.Data.p:
            raise ValueError("Modulus is not specified")
        if (M._nrows != 1) or (M._ncols != self.Data.nontips):
            raise ValueError("Parameter must be a row vector of size %d"%(self.Data.nontips))
        if (M.Data.Field != self.Data.p):
            raise ValueError("Matrix must be defined over GF(%d)"%(self.Data.p))
        cdef MTX OUT
        OUT  = makeMTX(MatAlloc(self.Data.p, self.Data.nontips,self.Data.nontips))
        innerLeftActionMatrix(self.Data, M.Data.Data, OUT.Data.Data)
        OUT.set_immutable()
        return OUT

    def kG_map(self, MTX M, MTX x):
        r"""
        Image of an element of a right `\mathbb F_pG`-module under a `\mathbb F_pG`-module morphism.

        INPUT:

        - M -- `((s\cdot r) \times |G|)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix, representing a
          right-`\mathbb F_pG`-module morphism from a free right `\mathbb F_pG`-module of rank `r`
          to a free right `\mathbb F_pG`-module of rank `s`, where `G` is a finite `p`-group.
          The data of ``M`` are organized in `s` blocks of `r` rows.
        - x -- `(r \times |G|)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing an element
          of a free right `\mathbb F_pG`-module of rank `r`

        OUTPUT:

        A `(s \times |G|)` :class:`~sage.matrix.matrix_gfpn_dense.Matrix_gfpn_dense` matrix representing the image of ``x``
        under the map represented by ``M``

        EXAMPLES:

        The example produces files. For safety reasons, we choose files
        in a temporary directory; it will be removed as soon as Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology.resolution import makeGroupData, G_ALG
            sage: from sage.matrix.matrix_gfpn_dense import Matrix_gfpn_dense as MTX
            sage: makeGroupData(8,3,folder=tmp_root)
            sage: gstem='8gp3'
            sage: gps_folder=os.path.join(tmp_root,gstem)
            sage: G = G_ALG(gstem,folder=gps_folder,dependent=False)
            sage: M = MTX(MatrixSpace(GF(2),4,8, implementation=MTX), [[1,0,0,0,0,0,0,0],[0,1,0,1,0,1,0,1],[1,0,0,0,0,0,0,0],[1,0,1,0,1,0,1,0]])
            sage: G.kG_map(M,MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,0,1,0,1,0,1,0],[0,1,0,1,0,1,0,1]]))
            [1 1 1 1 1 1 1 1]
            [0 0 0 1 1 1 1 0]
            sage: G.kG_map(M,MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[0,1,0,1,0,1,0,1],[1,0,1,0,1,0,1,0]]))
            [1 1 1 1 1 1 1 1]
            [1 0 0 0 0 1 1 0]

        The image of the sum is the sum of the images::

            sage: G.kG_map(M, MTX(MatrixSpace(GF(2),2,8, implementation=MTX), [[1,1,1,1,1,1,1,1],[1,1,1,1,1,1,1,1]]))
            [0 0 0 0 0 0 0 0]
            [1 0 0 1 1 0 0 0]
        """
        if not M.Data:
            raise ValueError("homomorphism can't be described by an empty matrix")
        if not x.Data:
            return x
        if (x.ncols()!=self.Data.nontips) or (M.ncols()!=self.Data.nontips):
            raise ValueError("matrices must be of size |G|=%d"%(self.Data.nontips))
        r=x.nrows()
        if (M.nrows()%r):
            raise ValueError("matrix size incompatible (row number must be multiple of %d)"%(r))
        if (M.Data.Field!=self.Data.p) or (x.Data.Field!=self.Data.p):
            raise ValueError("matrices must be defined over GF(%d)"%(self.Data.p))
        s = int(M.nrows()/r)

        cdef MTX OUT
        OUT = makeMTX(MatAlloc(self.Data.p, s,self.Data.nontips))
        cdef PTR scratch
        scratch = FfAlloc(self.Data.nontips+1)
        innerRightCompose(self.Data, x.Data.Data, M.Data.Data, 1,r,s, scratch, OUT.Data.Data)
        sig_free(scratch)
        OUT.set_immutable()
        return OUT


#################################################################################
#################################################################################
####                                                                         ####
####     A tool for computing Massey products                                ####
####                                                                         ####
#################################################################################
#################################################################################

from pGroupCohomology.cochain import YCOCH
class MasseyDefiningSystems:
    # Main attribute: States, a list of length len(inputdata)
    # entry number i is a list describing the states at level i, corresponding to the left upper corner (i+2)x(i+2) submatrix.
    # Each state at level i eventually is a pair formed by
    #   - list [m_0,m_1,...,m_i], where m_k provides one choice for entry D[i-k,i+1], which is a list of lifts of chain maps, and
    #   - a pointer to one state at level i-1 (given by the index).
    #
    # When computing the last level, it is not tried to find a cobounding Yoneda cochain at position m_i. Then, m_i contains one possible value.
    """
    A tool for computing defining systems for Massey products.

    NOTE:

    This class is used behind the scenes in :meth:`~pGroupCohomology.cohomology.COHO.massey_products`.

    INPUT:

    ``Y_1,Y_2,...``: Yoneda cochains (:class:`~pGroupCohomology.cochain.YCOCH`) over a common resolution


    The method :meth:`value` returns a list of all possible values (given by Yoneda cochains) for defining
    systems of the Massey products of ``Y_1,Y2,...``.

    EXAMPLES:

    The example produces files. For safety reasons, we choose files
    in a temporary directory; it will be removed as soon as Sage is quit::

        sage: from pGroupCohomology import CohomologyRing
        sage: from pGroupCohomology.resolution import MasseyDefiningSystems
        sage: tmp_root = tmp_dir()
        sage: CohomologyRing.set_user_db(tmp_root)
        sage: H = CohomologyRing(8,3)
        sage: H.make()
        sage: H.rels()
        ['b_1_0*b_1_1']

    Since the product of the two degree one generators of ``H`` vanish, it makes sense to compute
    Massey products::

        sage: Y1 = H.2.yoneda_cocycle()
        sage: Y2 = H.3.yoneda_cocycle()
        sage: M = MasseyDefiningSystems(Y1,Y2,Y1)
        sage: P = M.values()
        sage: len(P)
        16
        sage: print(P[0][0])
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 1 0 0 0 0 0]
        sage: print(P[0][1])
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 1 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        sage: print(P[1][0])
        [1 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 1 0 0 0 0 0]
        sage: print(P[1][1])
        [1 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 1 0 1 0 0 0 0]
        [0 0 0 0 0 0 0 0]
        [0 0 0 0 0 0 0 0]

    Hence, there are both trivial and non-trivial cocycles in the Massey product of ``H.2``, ``H.3``, ``H.2``.

    """
    def __init__(self, *L, all=True):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.resolution import MasseyDefiningSystems
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: Y1 = H.2.yoneda_cocycle()
            sage: Y2 = H.3.yoneda_cocycle()
            sage: M = MasseyDefiningSystems(Y1,Y2,Y1)   # indirect doctest
            sage: P = M.values()
            sage: len(P)
            16
            sage: print(P[0][0])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            sage: print(P[0][1])
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            sage: print(P[1][0])
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 1 0 0 0 0 0]
            sage: print(P[1][1])
            [1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 1 0 1 0 0 0 0]
            [0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0]

        """
        if not L:
            raise ValueError("At least one Yoneda cochain expected")
        cdef int i = 0
        self.States = []
        self._all = all
        cdef RESL R = L[0].resolution()
        self.R = R
        self.len = len(L)
        for i from 0 <= i < self.len:
            # Of course there is no choice for our starting values.
            # When applying the "make" method, the list that now only contains one item will be longer
            # and the list that now only contains (n,m,M) will contain further lifts.
            if not (isinstance(L[i], YCOCH) and (L[i].resolution() is R)):
                raise TypeError("The input must be Yoneda cochains defined over the same resolution")
            if i==0:
                self.States.append( [ [ [       L[i]             ]  ,         None         ]   ] )  # the level i starts just with one state
                #                       - Value list for state --    there is no level i-1
                #                     ------------------ one state ------------------------
                #                    ------- List of states at one level ----------------------
            else:
                self.States.append( [ [ [       L[i]            ]  ,       0              ]   ] )  # the level i starts just with one state
                #                       - Value list for state --    pointer to level i-1
                #                     ------------------ one state ------------------------
                #                    ------- List of states at one level ----------------------


    def _make(self, int i):
        """
        Make all states out to level `i`.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.resolution import MasseyDefiningSystems
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.make()
            sage: Y1 = H.2.yoneda_cocycle()
            sage: Y2 = H.3.yoneda_cocycle()
            sage: M = MasseyDefiningSystems(Y1,Y2,Y1)
            sage: M._make(1)
            sage: len(M.States[1])
            4
            sage: len(M.States[2])
            1
            sage: M._make(2)
            sage: len(M.States[1])
            4
            sage: len(M.States[2])
            16

        """
        if i==0:
            return
        if i<1 or i>self.len-1:
            raise IndexError("Index must be an integer between 1 and %d"%(self.len-1))
        if len(self.States[i][0][0]) == i+1: # level i has at least one state, and it is checked whether all i+1 values are already available
            return
        if i>1:
            self._make(i-1)
        # Now we can assume that the states to the left of i are known.
        # Plan: We start with a list of states at state i that refer to each of the
        # states out to degree i-1, but only has the given value. Then, we go "upwards"
        # and compute all possible choices for the next value; each choice gives rise
        # to a new state. If the last value is computed, it is put on the list of
        # "done" states, otherwise it is still "todo".
        cdef list done = []
        cdef list todo = [[self.States[i][0][0], j] for j in range(len(self.States[i-1]))]
        cdef int k
        cdef YCOCH Value
        cdef RESL R = self.R
        while todo:
            S  = todo.pop(0)
            j  = len(S[0])
            if j==i+1:
                done.append(S)
            else:
                # the degree of the next to be computed chain map.
                d = S[0][0].deg() + self.States[i-1][S[1]][0][j-1].deg()
                S_ = self.States[i-1][S[1]]
                if S[0][0].deg()%2:
                    Value = - S[0][0]*S_[0][j-1]
                else:
                    Value = S[0][0]*S_[0][j-1]
                for k from 0 < k < j:
                    S_ = self.States[i-k-1][S_[1]]
                    if S[0][k].deg()%2:
                        Value = Value - S[0][k]*S_[0][j-k-1]
                    else:
                        Value = Value + S[0][k]*S_[0][j-k-1]
                # Now we have the value. If it is in the upright corner of the matrix,
                # then we have to insert it; otherwise, we try to find a Yoneda cochain whose
                # coboundary is the value, and insert this.
                if (i==self.len-1) and (i==j):
                    S[0].append( Value )
                    done.append(S)
                else:
                    # CoValue, the return of find_cobounding_yoneda_cochains,
                    # is a set of pairs (tuple) of triples (tuple)
                    for CoValue in Value.find_cobounding_yoneda_cochains(all=self._all):
                        todo.append([S[0]+[ CoValue ],S[1]])
        self.States[i] = done

    def values(self):
        """
        Return all possible values (Yoneda cochains) of defining systems of Massey products.

        EXAMPLES:

        We use an example with a non-commutative cohomology ring. The example
        produces files. For safety reasons, we choose files in a temporary
        directory; it will be removed as soon as Sage is quit::

            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.resolution import MasseyDefiningSystems
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(9,2)
            sage: H.make()
            sage: H.3
            a_1_0: 1-Cocycle in H^*(SmallGroup(9,2); GF(3))
            sage: Y = H.3.yoneda_cocycle()
            sage: M = MasseyDefiningSystems(Y,Y,Y)
            sage: P = M.values()
            sage: len(P)
            81
            sage: print(P[0][0])
            [0 0 0 0 0 0 0 0 0]
            [2 0 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            sage: print(P[1][0])
            [0 0 0 0 0 0 0 0 0]
            [2 1 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]
            sage: print(P[2][0])
            [0 0 0 0 0 0 0 0 0]
            [2 2 0 0 0 0 0 0 0]
            [0 0 0 0 0 0 0 0 0]

        Hence, in this case, the Massey product only contains different non-trivial cocycles.
        """
        self._make(self.len-1)
        return [S[0][-1] for S in self.States[self.len-1]]


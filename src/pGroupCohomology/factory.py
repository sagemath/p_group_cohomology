#*****************************************************************************
#
#    Sage Package "Modular Cohomology Rings of Finite Groups"
#
#    Copyright (C) 2009/2010
#         Simon A. King  <simon.king@nuigalway.ie> and
#         David J. Green <david.green@uni-jena.de>
#    Copyright (C) 2013 Simon A. King <simon.king@uni-jena.de>
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
r"""
Modular Cohomology Rings of Finite Groups

AUTHORS:

- Simon King  <simon.king@uni-jena.de>
- David Green <david.green@uni-jena.de>

This module provides a constructor for modular cohomology rings of
finite groups, that takes care of caching. The constructor is an
instance :func:`~pGroupCohomology.CohomologyRing` of the class
:class:`CohomologyRingFactory`.

"""

from sage.all import SAGE_ROOT, DOT_SAGE, load
from sage.all import Integer
from sage.all import singular
from pGroupCohomology.cohomology import COHO
from pGroupCohomology.resolution import OPTION, print_protocol, safe_save, _gap_init
from pGroupCohomology import barcode
import re,os

import urllib2
import tarfile

##########
## A little regular expression that transforms any string into a valid GStem

_GStemMaker = re.compile(r'[^0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ]')

##########
## Transformation into latex
_index_match = re.compile('(_\d+)+')
_exp_match = re.compile('\^\d')
_name2latex = lambda t: _exp_match.sub(lambda m: '^{'+m.group()[1:]+'}', _index_match.sub(lambda m:'_{%s}'%','.join(m.group().split('_')[1:]),t).replace('**','^')).replace('*',' ')


##########
## A rather long unit test: Groups of order 64

def unit_test_64(D={}):
    """
    Compare computation from scratch with data in the database.

    The cohomology rings for all groups of order 64 are computed
    from sratch and the results are compared with the data that
    are shipped with this package.

    NOTE:

    This test is likely to take 30 - 60 minutes, depending on the
    computer.

    INPUT:

    ``D`` -- dictionary (default ``{}``), yields keyword arguments
    for the creation of cohomology rings.

    OUTPUT:

    - A list of integers, giving the address of groups of order 64
      in the Small Groups library for which a cohomology computation
      yields (with the given keyword arguments) a Poincare series
      different from the database. So, this list should be empty.
    - A list of four real numbers, giving the total computation time
      (wall time), the Python CPU-time, the Singular CPU-time and the
      GAP CPU-time, in seconds.

    During the computation, there is some information on the progress
    of the test.

    TEST::

        sage: from pGroupCohomology.factory import unit_test_64

    In order to have a test that takes less than two minutes, we allow
    to retrieve the data from the public database. By consequence, the
    cohomology rings are not computed from scratch but simply reloaded.
    By default, i.e., without providing an explicit value ``False`` for
    ``from_scratch``, the rings are computed from scratch, using a
    temporary directory created by the test function (this can be
    overwritten by providing an explicit value for ``root`` in the
    input dictionary). This provides a serious test, which should take
    20-60 minutes.
    ::

        sage: L,t = unit_test_64(D={'from_scratch':False})
        #  1: Walltime   ... min
              CPU-time   ... min
              Singular   ... min
              Gap-time   ... min
        ...
        #267: Walltime   ... min
              CPU-time   ... min
              Singular   ... min
              Gap-time   ... min
        sage: L
        []

    """
    L = []
    from sage.all import tmp_dir, walltime, cputime, singular, gap
    if D.has_key('root'):
        CohomologyRing.set_user_db(D['root'])
        D.__delitem__('root')
    else:
        CohomologyRing.set_user_db(tmp_dir())
    wt0 = walltime()
    ct0 = cputime()
    st = int(singular.eval('timer'))
    gt = int(gap.eval('Runtime()'))
    Method = {}
    Defect = {}
    if not D.has_key('from_scratch'):
        D['from_scratch'] = True
    for i in range(1,268):
        H = CohomologyRing(64,i, **D)
        H.make()
        H_db = CohomologyRing(64,i)
        if H.degvec!=H_db.degvec or H.poincare_series() != H_db.poincare_series():
            print "Example",i,"fails"
            L.append(i)
        if H.knownDeg < H_db.knownDeg:
            print "###########################################"
            print "####### Improvement:",i
            print "###########################################"
        elif H.knownDeg > H_db.knownDeg:
            print "###########################################"
            print "####### Regression:",i
            print "###########################################"
        wt = walltime(wt0)
        ct = cputime(ct0)
        print "#%3d: Walltime %3d:%02d.%02d min"%(i, int(wt/60), int(wt%60),int((wt%1)*100))
        print  "      CPU-time %3d:%02d.%02d min"%(int(ct/60), int(ct%60),int((ct%1)*100))
        ST = (int(singular.eval('timer'))-st)/1000.0
        print  "      Singular %3d:%02d.%02d min"%(int(ST/60), int(ST%60),int((ST%1)*100))
        GT = (int(gap.eval('Runtime()'))-gt)/1000.0
        print  "      Gap-time %3d:%02d.%02d min"%(int(GT/60), int(GT%60),int((GT%1)*100))
        print
        #if not Method.has_key(H._method):
        #    Method[H._method] = []
        #Method[H._method].append(i)
        #defect = H.knownDeg-H.last_interesting_degree()
        #if defect:
        #    if not Defect.has_key(defect):
        #        Defect[defect] = []
        #    Defect[defect].append(i)
    return L,[wt,ct,ST,GT] #,Method, Defect

############
##  An auxiliary function that creates symbolic links to data
##  in a potentially write protected database

def _symlink_to_database(publ, priv):
    """
    INPUT:

    - ``publ`` -- string, folder for a cohomology ring in a database
      that may be write protected.
    - ``priv`` -- string

    ASSUMPTIONS:

    - ``publ`` exists and is a readable folder.
    - It is permitted to create a folder ``priv``. It is assumed
      that this folder does not exist yet.

    OUTPUT:

    Create symbolic links in ``priv`` pointing to data in ``publ``.

    EXAMPLES:

    We link to an entry of the public database.
    ::

        sage: from pGroupCohomology import CohomologyRing
        sage: tmp = tmp_dir()
        sage: from pGroupCohomology.factory import _symlink_to_database
        sage: os.mkdir(os.path.join(tmp,'8gp3'))
        sage: _symlink_to_database(os.path.join(CohomologyRing.get_public_db(),'8gp3'), os.path.join(tmp,'8gp3'))
        sage: L = os.listdir(os.path.join(tmp, '8gp3'))
        sage: '8gp3.nontips' in L
        True
        sage: 'H8gp3.sobj' in L
        True
        sage: L = os.listdir(os.path.join(tmp,'8gp3','dat'))
        sage: 'A8gp3.sobj' in L
        True
        sage: 'Res8gp3d02.bin' in L
        True

    """
    #print "_symlink_to_database",publ,priv
    priv = os.path.realpath(priv)
    publ = os.path.realpath(publ)
    if not (os.access(publ,os.R_OK) and os.path.isdir(publ)):
        raise ValueError, "%s is supposed to be a readable folder"%publ
    if priv==publ:
        raise ValueError, "Can not symlink %s to itself"%priv
    if not os.path.isdir(priv):
        # priv should be a folder. If it is anything else, then unlink it.
        if os.access(priv, os.F_OK) or os.path.islink(priv):
            os.unlink(priv)
        os.makedirs(priv)

    # We use a recursive routine to create the symbolic links.
    L0 = os.listdir(publ) # these are potentially write-protected files
    for d in L0:
        publd = os.path.realpath(os.path.join(publ,d))
        if os.path.islink(os.path.join(priv,d)):
            if os.path.realpath(os.path.join(priv,d)) == publd:
                # the link has already been established
                #print os.path.join(priv,d),"already points to",publd
                continue
            else:
                os.unlink(os.path.join(priv,d))
        privd = os.path.join(priv,d) # realpath here?
        if os.path.isdir(publd):
            _symlink_to_database(publd, privd)
        else:
            if os.path.isdir(privd):
                # This should not happen.
                # Anyway, clean it up.
                os.rmdir(privd)
            elif os.access(privd, os.F_OK):
                os.unlink(privd)
            os.symlink(publd, privd)


############
## A framework for working with different cohomology databases

class CohomologyRingFactory:
    r"""
    A factory for creating modular cohomology rings of finite p-groups as unique parent structures

    Please use :func:`~pGroupCohomology.CohomologyRing`, which is an
    instance of this class, and is provided with a documentation of
    the available options.
    
    TESTS::
    
        sage: from pGroupCohomology import CohomologyRing
        sage: H0 = CohomologyRing(8,3)   #indirect doctest
        sage: print H0
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
    def __init__(self):
        """
        EXAMPLE::

            sage: from pGroupCohomology.factory import CohomologyRingFactory
            sage: CR = CohomologyRingFactory()   #indirect doctest
            sage: H = CR(8,3)
            sage: print H
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
        ###########
        ## Cohomology rings will be unique parent structures
        from weakref import WeakValueDictionary
        self._cache = WeakValueDictionary({})
        self._use_public_db = False

    def get_public_db(self):
        """
        Return the location of the currently used public database.

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: try:
            ....:     from sage.env import SAGE_SHARE
            ....: except ImportError:
            ....:     try:
            ....:         from sage.misc.misc import SAGE_SHARE
            ....:     except ImportError:
            ....:         from sage.misc.misc import SAGE_DATA as SAGE_SHARE
            sage: CohomologyRing.get_public_db().startswith(os.path.realpath(SAGE_SHARE))
            True
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_public_db(tmp)
            sage: CohomologyRing.get_public_db().startswith(os.path.realpath(tmp))
            True

        """
        return COHO.public_db

    def get_private_db(self):
        """
        Return the location of the current private database.

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.get_private_db().startswith(os.path.realpath(DOT_SAGE))
            True
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp)
            sage: CohomologyRing.get_private_db().startswith(os.path.realpath(tmp))
            True

        """
        return COHO.user_db

    def set_public_db(self, folder=True):
        """
        Choose a public database to be used.

        INPUT:

        ``folder`` - (optional, default ``True``) a bool or a string

        OUTPUT:

        - If ``folder`` is a non-empty string, it will be used as the root
          directory of a public database in subsequent cohomology computations.
        - If the user has write permissions in this folder, it is actually
          used to create rings. Otherwise, it is only used to read existing
          cohomology data, but all new computations will still be done in
          the private database.
        - If ``folder`` is ``True`` then the default location of the public
          database is reset; this is a sub-directory of ``SAGE_SHARE``.
        - If ``bool(folder)`` is ``False`` then the private database will
          be used to create new data in subsequent computations, even if
          the user has write permission for the public database.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_priv = tmp_dir()
            sage: tmp_publ = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_priv)

        If the public database is set, then it is used
        for creating a cohomology ring::

            sage: CohomologyRing.set_public_db(tmp_publ)
            sage: H1 = CohomologyRing(8,3)
            sage: H1.root.startswith(os.path.realpath(tmp_publ))
            True

        After unsetting it, the private database is used instead::

            sage: CohomologyRing.set_public_db(False)
            sage: H2 = CohomologyRing(8,3)
            sage: H2.root.startswith(os.path.realpath(tmp_priv))
            True

        Here is how to reset the default location::

            sage: CohomologyRing.set_public_db()
            sage: try:
            ....:     from sage.env import SAGE_SHARE
            ....: except ImportError:
            ....:     try:
            ....:         from sage.misc.misc import SAGE_SHARE
            ....:     except ImportError:
            ....:         from sage.misc.misc import SAGE_DATA as SAGE_SHARE
            sage: CohomologyRing.get_public_db().startswith(os.path.realpath(SAGE_SHARE))
            True

        """
        if folder:
            self._use_public_db = True
            if not isinstance(folder,basestring):
                try:
                    from sage.env import SAGE_SHARE
                except ImportError:
                    try:
                        from sage.misc.misc import SAGE_SHARE
                    except ImportError:
                        from sage.misc.misc import SAGE_DATA as SAGE_SHARE
                folder = os.path.realpath(os.path.join(SAGE_SHARE,'pGroupCohomology'))
            else:
                folder = os.path.realpath(folder)
            if os.path.exists(folder):
                if os.path.isdir(folder):
                    if not os.access(folder,os.W_OK):
                       #print_protocol("WARNING: '%s' is not writeable"%folder)
                       self._use_public_db = False 
                else:
                    raise OSError, "'%s' is no folder"%folder
            else:
                os.makedirs(folder)  # may produce an error
            COHO.public_db = folder
        else:
            self._use_public_db = False

    def public_db(self, *args, **kwds):
        """
        Retrieve/create a cohomology ring in the public database

        NOTE:

        - The public database can be chosen using :meth:`set_public_db`.
        - Write permissions to the public database are required.
        - Subsequent computations will use the public database as well,
          until ``CohomologyRing.set_public_db(False)`` is used.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_priv = tmp_dir()
            sage: tmp_publ = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_priv)

        If the public database is set, then it is used
        for creating a cohomology ring::

            sage: CohomologyRing.set_public_db(tmp_publ)
            sage: H1 = CohomologyRing(8,3)
            sage: H1.root.startswith(os.path.realpath(tmp_publ))
            True

        After unsetting it, the private database is used instead::

            sage: CohomologyRing.set_public_db(False)
            sage: H2 = CohomologyRing(8,4)
            sage: H2.root.startswith(os.path.realpath(tmp_priv))
            True

        But it is possible to access the public database directly::

            sage: H3 = CohomologyRing.public_db(8,2)
            sage: H3.root.startswith(os.path.realpath(tmp_publ))
            True

        """
        if not self._use_public_db:
            self.set_public_db(self.get_public_db())
        return self(*args,**kwds)

    def gstem(self, G, GStem=None, GroupName=None, GroupId=None):
        """
        Return a group identifier that is used to create file names.

        INPUT:

        - ``G`` -- A list, either containing a single group in GAP
          or two integers providing an address in the SmallGroups
          library.
        - ``GStem`` -- (optional string) if provided, it will be used.
        - ``GroupName`` -- (optional string) if provided, if ``G``
          contains a single group and no other optional arguments
          are provided, it is used.
        - ``GroupId`` -- (optional pair of integers) If ``G`` contains
          a single group, ``GroupId`` is supposed to be its address
          in the SmallGroups library.

        OUTPUT:

        - A normalised version of ``GStem``, if it is provided.
        - ``<q>gp<n>``, if the SmallGroups address is provided by
          either ``G`` or ``GroupId``.
        - A normalised version of ``GroupName``, if it is provided.
        - If ``G`` contains a single group that has been given a
          custom name in GAP, a normalised version of this Name
          is returned.
        - Otherwise, an error is raised.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.gstem([8,3])
            '8gp3'
            sage: CohomologyRing.gstem([8,3],GStem='DihedralGroup(8)')
            'DihedralGroup_8_'
            sage: CohomologyRing.gstem([gap('DihedralGroup(8)')],GroupName='DG(8)')
            'DG_8_'
            sage: CohomologyRing.gstem([gap('DihedralGroup(8)')],GroupName='DG(8)',GroupId=[8,3])
            '8gp3'
            sage: G = gap('DihedralGroup(8)')
            sage: G.SetName('"DG_8"')
            sage: CohomologyRing.gstem([G])
            'DG_8'
            sage: CohomologyRing.gstem([gap('DihedralGroup(8)')])
            Traceback (most recent call last):
            ...
            ValueError: Please provide the optional arguments ``GStem`` or ``GroupName``

        """
        # Explicitly provided gstem has the highest rank.
        if GStem:
            return _GStemMaker.sub('_',GStem)
        # A small group has a canonical gstem
        if len(G)==2:
            return "%dgp%d"%(G[0],G[1])
        if GroupId:
            return "%dgp%d"%(GroupId[0],GroupId[1])
        # If there is no proper gstem, derive one from the groupname
        if GroupName:
            return _GStemMaker.sub('_',GroupName)
        try:
            g = G[0]
            gap = g.parent()
            if g.HasName():
                return _GStemMaker.sub('_',repr(g.Name()))
        except (AttributeError,IndexError):
            pass
        raise ValueError, "Please provide the optional arguments ``GStem`` or ``GroupName``"

    def group_name(self, G, GroupName=None):
        """
        Determine a name for the given group.

        NOTE:

        This is just an auxiliary method and could as well be directly
        written in the code.

        INPUT:

        - ``G`` -- a list, either comprised by two integers that form the
          address of a group in the SmallGroups library, or by a group in
          the GAP interface.
        - ``GroupName`` -- an optional string, a name provided by the user.

        If ``GroupName`` is provided, it will be used. Otherwise, if the
        group is given by its SmallGroup address, ``None`` is returned.
        Otherwise, if the group is provided with a custom name in GAP,
        it will be used. Otherwise, ``None`` is returned.

        NOTE:

        This package has a list of custom names for certain groups in
        the SmallGroups library. However, this list is only used in the
        initialisation of :class:`~pGroupCohomology.cohomology.COHO`.

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: G = gap('DihedralGroup(8)')
            sage: CohomologyRing.group_name((8,3))
            sage: CohomologyRing.group_name((8,3),'D8')
            'D8'
            sage: CohomologyRing.group_name([G],'D8')
            'D8'
            sage: CohomologyRing.group_name([G])
            sage: G.SetName('"DihedralGroup_8"')
            sage: CohomologyRing.group_name([G])
            '"DihedralGroup_8"'
            sage: CohomologyRing.group_name([G],'D8')
            'D8'

        """
        if GroupName:
            return GroupName
        if len(G)==2:
            return None  # "SmallGroup(%d,%d)"%(G[0],G[1])
        try:
            g = G[0]
            gap = g.parent()
            if g.HasName():
                return gap.eval('Name(%s)'%g.name())
        except (AttributeError, IndexError):
            pass
        # It is not always needed to have a group name, so, we do not
        # raise an error but return None

    def create_group_key(self, G, GroupId=None, GroupDefinition=None):
        """
        Return data that allow to determine a given group up to equivalence.

        NOTE:

        For our package, a group is always supposed to be provided with
        a fixed list of generators. Two groups are *equivalent* if there
        exists a group homomorphism that sends the list of generators
        of one group to an initial segment of the list of generators of
        the other group. The ring presentation of a cohomology ring of
        a group, as computed with this package, only depends on the group's
        equivalence class.

        This is nothing more than an auxiliary method.

        INPUT:

        - ``G`` - a list, either formed by two integers representing an
          address in the SmallGroups library, or formed by a group in
          the GAP interface.
        - ``GroupId`` - optional list of two integers, that is supposed
          to provide the address of a group in the SmallGroups library
          equivalent to the group given by ``G``.
        - ``GroupDefinition`` - optional string, that is supposed to be
          evaluated in the GAP interface, yielding a group that is
          equivalent to the group given by ``G``

        OUTPUT:

        - If ``GroupDefinition`` is provided, it is returned.
        - If the given group is equivalent to a group in the SmallGroups
          library whose address is either given or can be determined by
          GAP, then this address (a pair of integers) is returned.
        - Otherwise, if the group is not a permutation group, it is
          transformed into an equivalent permutation group (using the
          regular permutation action). Then, a string representation of
          that permutation group is returned.

        EXAMPLES::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp)
            sage: H = CohomologyRing(8,3)
            sage: H.group()
            Group( [ (1,2)(3,8)(4,6)(5,7), (1,3)(2,5)(4,7)(6,8) ] )
            sage: CohomologyRing.create_group_key([H.group()])
            (8, 3)

        By consequence, the cohomology rings of ``SmallGroup(8,3)`` and
        the permutation group above are identic::

            sage: H is CohomologyRing(gap('SmallGroup(8,3)'))
            True
            sage: H is CohomologyRing(H.group())
            True

        However, defining the dihedral group differently, we
        obtain a different equivalence class, and thus a different
        result::

            sage: CohomologyRing.create_group_key([gap('DihedralGroup(8)')])
            ('Group([(1,2)(3,8)(4,6)(5,7),(1,3,4,7)(2,5,6,8),(1,4)(2,6)(3,7)(5,8)])',)

        So, the given group is transformed into an equivalent
        permutation group. If we start with a big transformation
        group, a string representation obtained from its list of
        generators is returned::

            sage: CohomologyRing.create_group_key([gap('SymmetricGroup(8)')])
            ('Group([(1,2,3,4,5,6,7,8),(1,2)])',)

        It is possible to provide a reasonable string representation
        or a SmallGroups address. However, it is the user's responsibility
        to choose values that match the given group - this is not
        verified, as can be seen in the final example::

            sage: CohomologyRing.create_group_key([gap('SymmetricGroup(8)')],GroupDefinition='SymmetricGroup(8)')
            'SymmetricGroup(8)'
            sage: CohomologyRing.create_group_key([gap('SymmetricGroup(8)')],GroupId=[20,2])
            (20, 2)

        TEST:

        It is important that the group key is not formed by two integers in
        the GAP interface. Namely, when storing the resulting ring, it could
        not easily been unpickled (actually it *can* be unpickled, but this
        involves some trickery, and it is certainly better to not rely on
        trickery). Here, we demonstrate that the given keys are correctly converted::

            sage: CohomologyRing.set_user_db(tmp_dir())
            sage: X = CohomologyRing(gap(8),gap(3), from_scratch=True)
            sage: type(X._key[0][0])
            <type 'sage.rings.integer.Integer'>

        """
        if GroupDefinition:
            return GroupDefinition
        if len(G)==2:
            return (Integer(G[0]),Integer(G[1]))
        if GroupId:
            return (Integer(GroupId[0]),Integer(GroupId[1]))
        # Try to determine a key from GAP
        g = G[0]
        if not (hasattr(g,'parent') and repr(g.parent())=='Gap'):
            raise ValueError, "First argument should describe a group in GAP"
        gap = g.parent()
        # test if we can look g up in the Small Groups library
        try:
            gId = g.IdGroup().sage()
            gs = gap.SmallGroup(gId)
            if gap.eval('canonicalIsomorphism(%s,%s)'%(g.name(),gs.name()))!='fail':
                return Integer(gId[0]),Integer(gId[1])
        except (RuntimeError,TypeError):
            pass
        if g.IsPermGroup():
            KEY = ('Group('+repr(g.GeneratorsOfGroup())+')',)
            # there might be line breaks or blanks. Remove them
            KEY = (''.join([t.strip() for t in KEY[0].split()]),)
        else:
            print_protocol("Computing regular permutation action")
            KEY = (repr(gap('regularPermutationAction(%s: forceDefiningGenerators)'%g.name())),)
            KEY = (''.join([t.strip() for t in KEY[0].split()]),)
        return KEY

    def check_arguments(self, args, minimal_generators=None, GroupId=None):
        """
        Return group order and a group in GAP with generating set suitable for the computations

        INPUT:

        - ``args``: A list, either formed by a group in GAP or by two integers,
          providing an address in the SmallGroups library.
        - ``minimal_generators``: (optional bool) If it is true, it is asserted
          by the user that an initial segment of the given list of generators
          of the group froms a minimal generating set.
        - ``GroupId``: (optional) Pair of numbers, providing the address of the
          given group in the SmallGroups library, if this happens to be known
          to the user.

        OUTPUT:

        - The group order, and 

        NOTE:

        - It only matters in the case of prime power groups whether or not the
          given list of generators starts with a minimal generating set.
        - If the optional argument ``GroupId`` is provided, it is verified
          whether the group from the SmallGroups library is equivalent to the
          given group.

        EXAMPLE::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.check_arguments([8,3])
            (8, Group( [ f1, f2, f3 ] ))
            sage: CohomologyRing.check_arguments([gap('DihedralGroup(8)')])
            (8, Group( [ (1,2)(3,8)(4,6)(5,7), (1,3,4,7)(2,5,6,8) ] ))
            sage: CohomologyRing.check_arguments([gap('DihedralGroup(8)')],GroupId=[8,3])
            Traceback (most recent call last):
            ...
            ValueError: The given group generators are not canonically isomorphic to SmallGroup(8,3)

        """
        if len(args)<1 or len(args)>2:
            raise ValueError, "The p-Group must be described by one or two parameters"
        if len(args)==2:
            q,n = args
            if (GroupId is not None) and ((q,n)!=GroupId):
                raise ValueError,"``GroupId=(%d,%d)`` incompatible with the given SmallGroups entry (%d,%d)"%(GroupId[0],GroupId[1],q,n)
            from sage.all import gap
            _gap_init(gap)
            try:
                max_n = Integer(gap('NumberSmallGroups(%d)'%q))
            except RuntimeError:
                raise ValueError, "SmallGroups library not available for order %d"%q
            if not 1 <= n <= max_n:
                raise ValueError, "Second argument must be between 1 and %d"%max_n
            return Integer(q), gap('SmallGroup(%d,%d)'%(args[0],args[1]))
        g = args[0]
        if not (hasattr(g,'parent') and repr(g.parent())=='Gap'):
            raise ValueError, "Group in GAP expected"
        gap = g.parent()
        _gap_init(gap)
        if GroupId and gap.eval('canonicalIsomorphism(%s,SmallGroup(%d,%d))'%(g.name(),GroupId[0],GroupId[1]))=='fail':
            raise ValueError,"The given group generators are not canonically isomorphic to SmallGroup(%d,%d)"%(GroupId[0],GroupId[1])
        if GroupId: # compatibility was already checked
            q = Integer(GroupId[0])
        else:
            print_protocol( "Computing group order")
            q = Integer(gap.eval('Order(%s)'%(g.name())))
        print_protocol("The group is of order %d"%q)
        if q==1:
            raise ValueError, "We don't consider the trivial group"
        if minimal_generators or not q.is_prime_power():
            return Integer(q), g
        else:
            # we require that the generating set starts with a minimal
            # generating set.
            print_protocol("Trying to test that the generator list starts with a minimal generating set")
            PhiP = g.admissibleGroup()
            if repr(PhiP)!='fail':
                return q, PhiP.Range()
            else:
                raise ValueError, "The first generators of the group must form a minimal generating set"

    def _check_compatibility(self, CacheKey, R):
        """
        Test whether a given expression is essentially equivalent to the cache key of a given cohomology ring.

        INPUT:

        - ``CacheKey``: an expression that is supposed to be a key for
          the cache of cohomology rings.
        - ``R``: a cohomology ring.

        OUTPUT:

        If the group description yield by ``CacheKey`` is compatible
        with the group description of ``R`` then ``R`` is returned. In
        protocol mode, a warning is printed if ``CacheKey`` and ``R``
        provide different (yet equivalent) group descriptions. An
        error is raised if the two groups are not equivalent.

        NOTE:

        It is not verified whether the locations of data storage yield by
        the two arguments coincide.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp)
            sage: H = CohomologyRing(8,3)
            sage: H.option('prot')
            sage: CohomologyRing._check_compatibility(H._key,H)
            H^*(D8; GF(2))
            sage: CohomologyRing._check_compatibility(((repr(H.group()),),H._key[1]), H)
              WARNING: The given key and ring describe different groups, but they are equivalent
            H^*(D8; GF(2))
            sage: CohomologyRing._check_compatibility(((8,4),H._key[1]), H)
            Traceback (most recent call last):
            ...
            ValueError: The ring H^*(D8; GF(2)) does not match the given key
            sage: H.option('noprot')
        
        """
        if not isinstance(R, COHO):
            raise ValueError, 'The second argument %s is no Cohomology ring'%repr(R)
        if self._use_public_db:
            root_user_db = COHO.public_db # SAGE_SHARE+'pGroupCohomology'
        else:
            root_user_db = COHO.user_db #DOT_SAGE+'pGroupCohomology/db/'
        ## DELETE?
        ##if R.root != root_user_db:
        ##    R.setprop('_need_new_root',root_user_db)
        # test if R is compatible with the key CacheKey.
        # May print a warning or raise an error,
        # and if it succeeds, return R
        similarity = _IsKeyEquivalent(CacheKey,R._key)
        if similarity == 1:
            print_protocol('WARNING: The given key and ring describe different groups, but they are equivalent')
            return R
        elif similarity == 0:
            raise ValueError, 'The ring %s does not match the given key'%repr(R)
        return R

    def _get_p_group_from_cache_or_db(self, GStem, KEY, **kwds):
        """
        Try to find a certain cohomology ring of a `p`-group either in the cache or in a database.

        INPUT:

        - ``GStem``, a string that determines the filename for data associated with
          the cohomology ring of a finite `p`-group.
        - ``KEY``, a descriptor for the equivalence class of a group (see :meth:`create_group_key`)
        - ``from_scratch`` -- (optional bool) If ``True``, it is not attempted to
          copy data from a public database or web repository, and an error is raised
          if the requested cohomology ring is not in the cache but already exists
          in the private database.
        - ``websource`` -- (optional) provides the location of an alternative cohomology
          repository from which data will be downloaded if they can not be found in the cache,
          the private database or the public database.

        OUTPUT:

        The cohomology ring associated with the given arguments, or ``None``, if it can
        not be found in the cache, the private database, the public database or the web
        repository.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp)

        Since the cohomology of the dihedral group of order 8 is shipped with this
        package, it can be taken from the public database::
        
            sage: H = CohomologyRing._get_p_group_from_cache_or_db('8gp3',(8,3)); H
            H^*(D8; GF(2))

        Even when we request a computation from scratch, the ring is now taken from
        the cache::

            sage: H is CohomologyRing._get_p_group_from_cache_or_db('8gp3',(8,3), from_scratch=True)
            True

        However, if we remove the ring from the cache and request a computation from
        scratch again, an error is raise because the data for ``H`` can still be found
        in the private database::

            sage: for k,r in CohomologyRing._cache.items():
            ...     if r is H:
            ...         CohomologyRing._cache.__delitem__(k)
            sage: CohomologyRing._get_p_group_from_cache_or_db('8gp3',(8,3), from_scratch=True)
            Traceback (most recent call last):
            ...
            RuntimeError: You requested a computation from scratch. Please remove .../8gp3

        But of course it is possible to take the cohomology ring from the private database
        without the option ``from_scratch``. To demonstrate this, we disable the use of the
        private database (by setting it to a non-existing folder) and disallow the use of
        a web repository::

            sage: CohomologyRing.set_public_db(tmp_dir())

        If the location of the public database is explicitly set and write permission
        is granted (which is the case here), it is attempted to get the data from there.
        Since this is impossible, ``None`` is returned::
        
            sage: CohomologyRing._get_p_group_from_cache_or_db('8gp3',(8,3), websource=False)

        However, if we disable the use of the public database, then the private database
        is looked up, and indeed the requested ring can be found::

            sage: CohomologyRing.set_public_db(False)
            sage: CohomologyRing._get_p_group_from_cache_or_db('8gp3',(8,3), websource=False)
            H^*(D8; GF(2))

        """
        # If data for the given GStem and KEY are available,
        # they are returned, otherwise None.
        ####################
        ## Since v2.1, we insist on always using the private database,
        ## but it may be that we have to link to the public database
        from exceptions import RuntimeError
        root_public_db = COHO.public_db
        if self._use_public_db:
            root_user_db = COHO.public_db # SAGE_SHARE+'pGroupCohomology'
        else:
            root_user_db = COHO.user_db #DOT_SAGE+'pGroupCohomology/db/'
        file_name = os.path.join(GStem,'H%s.sobj'%GStem)
        OUT = None
        from_scratch = kwds.get('from_scratch')
        
        ## 1. Cache
        CacheKey = (KEY, os.path.join(root_user_db,GStem,'dat','State'))
        if self._cache.has_key(CacheKey):
            OUT = self._cache[CacheKey]
        ## 2. Directly load from private db
        elif os.access(os.path.join(root_user_db,file_name), os.R_OK):
            if from_scratch:
                from exceptions import RuntimeError
                raise RuntimeError, "You requested a computation from scratch. Please remove %s"%(os.path.join(root_user_db,GStem))
            try:
                OPTION.opts['@use_this_root@'] = root_user_db
                OUT = load(os.path.join(root_user_db,file_name)) # realpath here?
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
            except BaseException:
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
                raise IOError, "Saved data at %s are not readable"%(os.path.join(root_user_db,file_name))
        ## 3. Link with public db and load from there
        elif os.access(os.path.join(root_public_db,file_name), os.R_OK) and not from_scratch:
            try:
                print_protocol('Creating symbolic links from %s to %s'%(os.path.join(root_user_db,GStem), os.path.join(root_public_db,GStem)))
                _symlink_to_database(os.path.join(root_public_db,GStem), os.path.join(root_user_db,GStem))
            except BaseException:
                raise ValueError, "Can not create a symbolic link to the public database. Please remove %s"%(os.path.join(root_user_db,GStem))
            # now try to load from the new entry in the database
            try:
                OPTION.opts['@use_this_root@'] = root_user_db
                OUT = load(os.path.join(root_user_db,file_name)) # realpath here?
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
            except BaseException:
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
                raise IOError, "Saved data at %s are not readable"%(os.path.join(root_public_db,file_name))
        ## 4. Search web repository
        elif kwds.get('websource')!=False and (not from_scratch):
            try:
                if isinstance(kwds.get('websource'), basestring):
                    OUT = self.web_db(GStem, websource=kwds.get('websource'))
                else:
                    OUT = self.web_db(GStem)
            except urllib2.URLError:
                print_protocol("Websource is not available.")
            except (ValueError, RuntimeError):
                print_protocol("Cohomology ring can not be found in web repository.")
            except KeyboardInterrupt:
                print_protocol("Access to websource was interrupted.")
        if OUT is not None:
            gap = OUT.group().parent()
            _gap_init(gap)
            try:
                OUT.GenS._check_valid()
            except ValueError:
                OUT.reconstruct_singular()
            if len(KEY)==2:
                print_protocol('Checking compatibility of SmallGroup library and stored cohomology ring')
                if gap.eval('canonicalIsomorphism(%s,SmallGroup(%d,%d))'%(OUT.group(),KEY[0],KEY[1]))=='fail':
                    raise ValueError("Stored group data for SmallGroup(%d,%d) incompatible with data in the SmallGroup library"%(KEY[0],KEY[1]))
        return OUT

    def _get_p_group_from_scratch(self, KEY, q, GStem, GroupName, **kwds):
        """
        Initialise the cohomology ring of a finite `p`-group.

        INPUT:

        - ``KEY``: the identifier using which the group will be known
          in the cache.
        - ``q``: The order (integer) of the group
        - ``GStem``: A string that determines filenames for storing data
          associated with the cohomology ring
        - GroupName: A string, used as the name of the group.
        - optional arguments that will be passed to the init method
          of :class:`~pGroupCohomology.cohomology.COHO` or
          :class:`~pGroupCohomology.modular_cohomology.MODCOHO`.

        OUTPUT:

*        A cohomology ring for the given data.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp)
            sage: H1 = CohomologyRing._get_p_group_from_scratch((8,3), 8, '8gp3', 'Group1'); H1
            H^*(Group1; GF(2))
            sage: H2 = CohomologyRing._get_p_group_from_scratch(('DihedralGroup(8)',), 8, 'D8', 'Group2'); H2
            H^*(Group2; GF(2))
            sage: H2._key
            (('DihedralGroup(8)',), '.../D8/dat/State')
            sage: CohomologyRing._cache[H2._key] is H2
            True
            sage: H1 is CohomologyRing(8,3)
            True

        """
        from sage.all import gap
        print_protocol('Computing from scratch')
        if self._use_public_db:
            root_user_db = COHO.public_db # SAGE_SHARE+'pGroupCohomology'
        else:
            root_user_db = COHO.user_db #DOT_SAGE+'pGroupCohomology/db/'
        CacheKey = (KEY, os.path.join(root_user_db,GStem,'dat','State'))
        extras = {}
        for k in kwds.items():
            extras[k[0]] = k[1]
        extras['GroupName'] = GroupName
        extras['GStem'] = GStem
        extras['key'] = CacheKey
        extras['root'] = root_user_db
        if len(KEY)==1:
            extras['gap_input'] = q # we must specify the group order
            OUT = COHO(gap(KEY[0]), **extras)
        else:
            OUT = COHO(KEY[0],KEY[1], **extras)
        _gap_init(OUT.group().parent())
        return OUT

    def _get_non_p_group_from_db(self, GStem, pr, **kwds):
        """
        Try to find a certain cohomology ring of a non-primepower group in a database.

        INPUT:

        - ``GStem``: A string that determines the filename under which the cohomology
          ring is stored
        - ``pr``: A prime number, the modulus of the cohomology ring
        - ``from_scratch``: (optional bool) If ``True``, raise a ``RuntimeError`` if
          data for that ring are already stored in the private database.
        - ``websource``: (optional string or ``False``) Determines the location of a
          web repository of cohomology rings, or disables the use of a web repository.

        OUTPUT:

        The cohomology ring for the given data, or ``None`` if that ring can not be found.

        NOTE:

        It is not attempted to directly search the cohomology cache, since the computation
        of the key associated with the cohomology ring of a non-primepower group involves
        the computation of certain subgroups and can be very difficult.

        However, *if* data for that ring are in the cache, then they are usually in the
        private database as well. Since the file in the database provides the information
        needed to create the key, caching is possible, as seen in the examples below.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp)
            sage: H1 = CohomologyRing(18,3,prime=2)
            sage: H1.make(); H1
            H^*(SmallGroup(18,3); GF(2))
            sage: CohomologyRing._get_non_p_group_from_db('18gp3',2) is H1
            True

        Just for fun, we create a ring in such a way that it can not be loaded from
        a file, and demonstrate that the method under consideration does not use
        the cohomology cache::

            sage: H2 = CohomologyRing(18,4,prime=2,from_scratch=True, options='nosave')
            sage: H2.make(); H2
            H^*(SmallGroup(18,4); GF(2))
            sage: print CohomologyRing._get_non_p_group_from_db('18gp4',2)
            None

        """
        root_public_db = COHO.public_db
        if self._use_public_db:
            root_user_db = COHO.public_db # SAGE_SHARE+'pGroupCohomology'
        else:
            root_user_db = COHO.user_db #DOT_SAGE+'pGroupCohomology/db/'
        file_name = 'H%smod%d.sobj'%(GStem,pr)
        OUT = None
        from_scratch = kwds.get('from_scratch')

        ## 1. Directly load from private db
        if os.access(os.path.join(root_user_db,file_name), os.R_OK):
            if from_scratch:
                raise RuntimeError, "You requested a computation from scratch. Please remove %s"%(os.path.join(root_user_db,file_name))
            try:
                OPTION.opts['@use_this_root@'] = root_user_db
                OUT = load(os.path.join(root_user_db,file_name)) # realpath here?
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
            except BaseException:
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
                raise IOError, "Saved data at %s are not readable"%(os.path.join(root_user_db,file_name))
        ## 2. Link with public db and load from there
        elif os.access(os.path.join(root_public_db,file_name), os.R_OK) and not from_scratch:
            os.symlink(os.path.join(root_public_db,file_name), os.path.join(root_user_db,file_name))
            # now try to load from the new entry in the database
            try:
                OPTION.opts['@use_this_root@'] = root_user_db
                OUT = load(os.path.join(root_user_db,file_name))  # realpath here?
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
            except BaseException, msg:
                if OPTION.opts.has_key('@use_this_root@'):
                    OPTION.opts.__delitem__('@use_this_root@')
                raise IOError, "%. Saved data at %s are not readable"%(msg, os.path.join(root_public_db,file_name))
        # 3. Unless the user forbids it, try to obtain it from some web source
        elif kwds.get('websource')!=False and not kwds.get('from_scratch'):
            try:
                if isinstance(kwds.get('websource'), basestring):
                    OUT = self.web_db(GStem, websource=kwds.get('websource'))
                else:
                    OUT = self.web_db(GStem)
            except:
                print_protocol("No cohomology ring found in web repository.")
        if OUT is not None:
            _gap_init(OUT.group().parent())
            try:
                OUT.GenS._check_valid()
            except ValueError:
                OUT.reconstruct_singular()
        return OUT

    def __call__ (self, *args, **kwds):
        """
        Create the mod-p cohomology ring of a finite groups

        Of course, isomorphic p-Groups have isomorphic cohomology
        rings.  However, the presentation of the cohomology rings as
        obtained by our package depends on the choice of a minimal
        generating set of the p-group.
        
        If a `p`-group `G` is given by its position in the SmallGroups
        library, then this position, perhaps together with a custom
        name provided by the user, forms a unique key for the
        cohomology ring.
        
        If `G` is given as a group in the Gap interface, then it is
        required that the first items on the list of generators of `G`
        forms a minimal generating set. If this is not the case, an
        error is raised. We transform `G` into a permutation group
        whose generators correspond to a minimal generating set of
        `G`. The description of that permutation group, perhaps
        together with a custom name, forms a unique key for the
        cohomology ring.
        
        The unique key also depends on the chosen folders containing
        data of the ring.

        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.set_user_db(tmp_dir())

        Since the cohomology of the dihedral group of order 8 is
        part of the public database, the ring is complete::

            sage: H0 = CohomologyRing(8,3) # indirect doctest
            sage: print H0
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        Choosing a different root directory results in another copy
        of the same ring::

            sage: CohomologyRing.set_user_db(tmp_dir())
            sage: H1 = CohomologyRing(8,3)
            sage: H0 is H1
            False
            sage: H0 == H1
            True

        Creating a third location, we can ask that the ring will
        not be loaded from the public database or a web repository.
        By consequence, the returned ring is not complete yet and
        is therefor not equal to the previous rings, unless we
        complete it::

            sage: CohomologyRing.set_user_db(tmp_dir())
            sage: H2 = CohomologyRing(8,3,from_scratch=True)
            sage: H0 == H2
            False
            sage: H2.make()
            sage: H0 == H2
            True

        """
        from pGroupCohomology.cohomology import COHO
        from pGroupCohomology.modular_cohomology import MODCOHO
        from pGroupCohomology.resolution import OPTION
        import os
        root_public_db = COHO.public_db
        if self._use_public_db:
            root_user_db = COHO.public_db # SAGE_SHARE+'pGroupCohomology'
        else:
            root_user_db = COHO.user_db #DOT_SAGE+'pGroupCohomology/db/'
        # Basic idea: 
        # The key shall both be a unique pointer to the data in the file 
        # system and a descriptor of the group-with-minimal-generators.
        # Hence, it is the root directory plus the stem name plus [either
        # the position in the SmallGroups library or a permutation group
        # presentation].
        # The GroupName and other properties are extra arguments


        # If cohomology options are required, they are provided now.
        # Note that these are valid for any subsequent computations with
        # any cohomology ring: The options are not associated with the
        # ring that we are returning below.
        if kwds.has_key('root'):
            raise ValueError, "The syntax for ``CohomologyRing`` has changed. Don't provide the ``root`` keyword, but use the ``set_user_db`` method instead"
        from pGroupCohomology.cohomology import COHO_option
        if kwds.has_key('options'):
            if isinstance(kwds['options'], basestring):
                COHO_option(kwds['options'])
            else:
                COHO_option(*kwds['options'])

        # CHECK ADMISSIBILITY OF THE INPUT
        from pGroupCohomology.resolution import OPTION
        # _gap_init is done inside check_arguments
        GapName = None
        if len(args)==1 and args[0].HasName():
            GapName = repr(args[0].Name())
        q, Hfinal = self.check_arguments(args,minimal_generators=kwds.get('minimal_generators'),GroupId=kwds.get('GroupId'))
        KEY = self.create_group_key(args, GroupId=kwds.get('GroupId'), GroupDefinition=kwds.get('GroupDefinition'))
        gap = Hfinal.parent()
        if len(KEY) == 2:
            args = [KEY[0],KEY[1]]
        else:
            args = [Hfinal]

        # In the non prime power case, we need to be provided
        # with a prime modulus.
        pr = None
        if not q.is_prime_power():
            pr = kwds.get('prime')
            if pr is None:
                raise ValueError, "The parameter `prime` must be provided"
            try:
                pr = Integer(pr)
                if not pr.is_prime():
                    raise ValueError
            except:
                raise ValueError, "The parameter `prime=%s` must provide a prime number"%repr(pr)
            if not pr.divides(q):
                raise ValueError, "The parameter `prime=%d` must divide the group order %d"%(pr,q)

        ## Do we have the non-commutative case? If Singular is less
        ## than 3-1-0, raise an error.
        if ((pr is not None) and pr>2) or q%2:
            SingVer = tuple([int(x) for x in singular.eval('system("version")')])
            if SingVer < (3,1,0):
                raise NotImplementedError, ("""There is only Singular %s installed.
We need at least Singular 3-1-0 in the non-commutative Case."""%('-'.join(len(SingVer)*['%d'])))%SingVer

        ############
        # Take care of GStem and GroupName.
        GStem = self.gstem(args, GStem=kwds.get('GStem'), GroupName=kwds.get('GroupName') or GapName, GroupId=kwds.get('GroupId'))
        GroupName = self.group_name(args, GroupName=kwds.get('GroupName'))

        # KEY now either provides the coordinates (q,n) of a group in the small
        # groups library, or is of the form (s,) with a string s such
        # that gap(s) defines a group with an appropriate generating set.
        # It can be hashed.
        # Moreover the stem name (GStem) is set up, and we may have
        # a different GroupName (or None).
        extras ={}
        for k,v in kwds.items():
            if k not in ['pr','GStem','KEY','GroupName','q']:
                extras[k] = v

        if q.is_prime_power():
            CacheKey = (KEY, os.path.join(root_user_db,GStem,'dat','State'))
            OUT = self._check_compatibility(CacheKey, self._get_p_group_from_cache_or_db(GStem, KEY, **extras) or self._get_p_group_from_scratch(KEY, q, GStem, GroupName, **extras))
            return OUT

        # For non prime power groups, we need a sufficiently large subgroup.
        # Hfinal is available (even if KEY==(q,n))
        ## 1. Try to load the result, knowing GStem and KEY The KEY
        ## does not contain information on the subgroup, and can thus
        ## not be used to directly access the _cache. But *IF* it
        ## can be loaded then the _cache is used, if possible. So,
        ## this will work, unless the user did not want to save the
        ## cohomology ring on disk.
        OUT = self._get_non_p_group_from_db(GStem, pr, **extras)
        if OUT is not None:
            # Test if the group is OK
            if gap.eval('canonicalIsomorphism(%s,%s)'%(Hfinal.name(),OUT.group().name()))=='fail':
                raise ValueError, "The stored cohomology ring %s does not match the given group"%repr(OUT)

        ## If a subgroup or its cohomology is given, test consistency
        Subgroup = kwds.get('Subgroup')
        SubgpId = kwds.get('SubgpId')
        HP = kwds.get('SubgpCohomology')
        SylowSubgroup = kwds.get('SylowSubgroup')
        HSyl = kwds.get('SylowSubgpCohomology')
        ## 1. consistency with OUT, the stored ring
        if OUT is not None:
            # consistency vs. subgroup
            if (HP is not None) and (HP is not OUT._HP):
                raise ValueError, "The stored cohomology ring %s is not defined as a subring of %s"%(repr(OUT),repr(HP))
            if (Subgroup is not None) and gap.eval('canonicalIsomorphism(%s,%s)'%(Subgroup.name(),OUT.subgroup().name()))=='fail':
                raise ValueError, "The stored cohomology ring %s is not computed using the given subgroup"%repr(OUT)
            # consistency vs. Sylow subgroup
            if (HSyl is not None) and (HSyl is not OUT._HSyl):
                raise ValueError, "The stored cohomology ring %s is not defined as a subring of %s"%(repr(OUT),repr(HP))
            if (SylowSubgroup is not None) and (gap.eval('canonicalIsomorphism(%s,%s)'%(SylowSubgroup.name(),OUT.sylow_subgroup().name()))=='fail'):
                raise ValueError, "The stored cohomology ring %s is not computed using the given Sylow subgroup"%repr(OUT)
            ## These were enough consistency checks!
            return OUT

        ## At this point, we need to do the hard work and compute the
        ## cohomology from scratch. The given subgroups may help,
        ## but have to be consistent.
        # 1. check HP and HSyl
        if HP is not None: 
            if not isinstance(HP,COHO):
                raise TypeError, "`SubgpCohomology` must be %s"%COHO
            HSyl = HP._HSyl or HP # ignore the keyword argument for HSyl
        if HSyl is not None:
           if not isinstance(HSyl,COHO):
               raise ValueError, "The given cohomology of a Sylow subgroup is not a cohomology ring"
           if isinstance(HSyl,MODCOHO):
               raise ValueError, "The given cohomology of a Sylow subgroup does in fact not belong to a prime power group"
        # 2. check subgroup
        if Subgroup is not None:
            if not Hfinal.IsSubgroup(Subgroup):
                raise ValueError, "The given subgroup is in fact not a subgroup"
            if pr.divides(Integer(gap.eval('Index(%s,%s)'%(Hfinal.name(),Subgroup.name())))):
                raise ValueError, "The given subgroup must contain a Sylow %d-subgroup"%pr
##            if HP is not None:
##                if gap.eval('canonicalIsomorphism(%s,%s)'%(Subgroup.name(),HP.group().name()))=='fail':
##                    raise ValueError, "The given subgroup does not match its given cohomology ring"
        ## 3. check Sylow subgroup
        if SylowSubgroup is not None:
            if not Hfinal.IsSubgroup(SylowSubgroup):
                raise ValueError, "The given Sylow subgroup is in fact not a subgroup"
            if pr.divides(Integer(gap.eval('Index(%s,%s)'%(Hfinal.name(),SylowSubgroup.name())))):
                raise ValueError, "The index of the given Sylow %d-subgroup is not coprime to %d"%(pr,pr)
            if not pr.divides(Integer(gap.eval('Order(%s)'%SylowSubgroup.name()))):
                raise ValueError, "The given Sylow subgroup's order is indivisible by %d"%pr
            if Subgroup is not None:
                if not Subgroup.IsSubgroup(SylowSubgroup):
                    raise ValueError, "The given subgroup must contain the given Sylow subgroup"
##            if HSyl is not None:
##                if gap.eval('canonicalIsomorphism(%s,%s)'%(SylowSubgroup.name(),HSyl.group().name()))=='fail':
##                    raise ValueError, "The given subgroup does not match its given cohomology ring"

        ##################################
        # Begin to construct the basic data
        # First step: Get the (Sylow) subgroup related with the given cohomology
        phiSub = None
        phiSyl = None
        SubgroupTested = False
        SylowTested = False
        # 1a) Try to match with a given cohomology ring
        if Subgroup is None:
            if HP is not None:
                try:
                    phiSub=gap('IsomorphicSubgroups(%s,%s:findall:=false)'%(HP.group().name(),Hfinal.name()))[1]
                    Subgroup = gap('Group(List([1..Length(GeneratorsOfGroup(%s))], x -> Image(%s, GeneratorsOfGroup(%s)[x])))'%(HP.group().name(),phiSub.name(),HP.group().name()))
                except:
                    raise ValueError, "Unable to find a subgroup compatible with the argument `SubgpCohomology`"
                SubgroupTested = True
        else:
            if HP is not None:
                phiSub = HP.group().canonicalIsomorphism(Subgroup)
                if repr(phiSub)=='fail':
                    raise ValueError, "The arguments `Subgroup` and `SubgpCohomology` don't match"
                SubgroupTested=True
        # 1b) dito for the Sylow subgroup
        if SylowSubgroup is None:
            if (HP is not None) and (phiSub is not None):
                SylowSubgroup = gap('Group(List([1..Length(GeneratorsOfGroup(%s))], x -> Image(%s, GeneratorsOfGroup(%s)[x])))'%((HP.sylow_subgroup or HP.group)().name(),phiSub.name(),(HP.sylow_subgroup or HP.group)().name()))
                SylowTested = True
            elif HSyl is not None:
                try:
                    SylowSubgroup = (Hfinal if Subgroup is None else Subgroup).SylowSubgroup(pr)
                    phiSyl = gap('IsomorphismGroups(%s,%s)'%(HSyl.group().name(),SylowSubgroup.name()))
                    SylowSubgroup = gap('Group(List([1..Length(GeneratorsOfGroup(%s))], x -> Image(%s, GeneratorsOfGroup(%s)[x])))'%(HSyl.group().name(),phiSyl.name(),HSyl.group().name()))
                except:
                    raise ValueError, "Unable to find a Sylow subgroup compatible with the given arguments `SubgpCohomology` or `SylowSubgpCohomology`"
                SylowTested = True
        else:
            if HSyl is not None:
                phiSub = HSyl.group().canonicalIsomorphism(SylowSubgroup)
                if repr(phiSub)=='fail':
                    raise ValueError, "The arguments `SylowSubgroup` and `SylowSubgpCohomology` don't match"
                SylowTested=True


        #####
        # Second step: Get the cohomology of the subgroups
        if SylowSubgroup is None:
            print_protocol( "Try to compute a Sylow %d-subgroup"%pr)
            SylowSubgroup = (Hfinal if Subgroup is None else Subgroup).SylowSubgroup(pr)
            # We are free in choosing generators, since apparently HSyl was not given
        if HSyl is None:
            try:
                print_protocol( "Try to find the SmallGroups address of the Sylow subgroup")
                SylowId = SylowSubgroup.IdGroup().sage()
            except BaseException, msg:
                if not ("group identification" in str(msg)):
                    raise msg
                print_protocol( "SmallGroups address not available. Compute the order")
                SylowId = [Integer(SylowSubgroup.Order()),0]            
            if SylowId[1]>0:
                phiSyl = gap('IsomorphismGroups(SmallGroup(%d,%d),%s)'%(SylowId[0],SylowId[1],SylowSubgroup.name()))
                SylowSubgroup = gap('Group(List([1..Length(GeneratorsOfGroup(Source(%s)))],x->Image(%s,GeneratorsOfGroup(Source(%s))[x])))'%(phiSyl.name(),phiSyl.name(),phiSyl.name()))
                HSyl = CohomologyRing(SylowId[0],SylowId[1], useElimination=kwds.get('useElimination'), auto=kwds.get('auto'), useFactorization=kwds.get('useFactorization'))
            else:
                print_protocol("Find a minimal generating set")
                SylowSubgroup = SylowSubgroup.MinimalGeneratingSet().Group()
                HSyl = CohomologyRing(SylowSubgroup,useElimination=kwds.get('useElimination'), auto=kwds.get('auto'), useFactorization=kwds.get('useFactorization'), GroupName='SylowSubgroup(%s,%d)'%(GroupName or GStem,pr))
        # By now, we have HSyl and SylowSubgroup

        if kwds.get('OneStep'):
            Subgroup = SylowSubgroup
            HP = HSyl
            SubgpComputedFromScratch = False
        if Subgroup is None:
            print_protocol("Compute intermediate subgroup")
            Subgroup = Hfinal.Normalizer(SylowSubgroup.Centre())
            qP = Integer(Subgroup.Order())
            if qP==q or qP.is_prime_power():
                # Subgroup=Hfinal or =SylowSubgroup
                # In both cases, we are reduced to the OneStep case
                Subgroup = SylowSubgroup
                HP = HSyl
                SubgpComputedFromScratch = False
            else:
                SubgpComputedFromScratch = True
        else:
            SubgpComputedFromScratch = False

        if HP is None:
            try:
                print_protocol( "Try to find the SmallGroups address of the intermediate subgroup")
                SubgpId = Subgroup.IdGroup().sage()
            except BaseException, msg:
                if not ("group identification" in str(msg)):
                    raise msg
                print_protocol( "SmallGroups address not available. Compute the order")
                SubgpId = [Integer(Subgroup.Order()),0]
            if SubgpId[1]>0: # SmallGroup name is better than my custom names
                #gap.eval('Reset(GlobalMersenneTwister,0)') #gap.RestoreStateRandom(0)
                phiSub = gap('IsomorphismGroups(SmallGroup(%d,%d),%s)'%(SubgpId[0],SubgpId[1],Subgroup.name()))
                Subgroup = gap('Group(List([1..Length(GeneratorsOfGroup(Source(%s)))],x->Image(%s,GeneratorsOfGroup(Source(%s))[x])))'%(phiSub.name(),phiSub.name(),phiSub.name()))
                HP = CohomologyRing(Subgroup,SubgpId=SubgpId,prime=pr,SylowSubgroup=SylowSubgroup,SylowSubgpCohomology=HSyl,GStem='%dgp%d'%(SubgpId[0],SubgpId[1]), useElimination=kwds.get('useElimination'),useFactorization=kwds.get('useFactorization')) # not from_scratch=kwds.get('from_scratch') 
            elif SubgpComputedFromScratch:
                # no minimal generating set needed
                SubgpId=None
                HP = CohomologyRing(Subgroup, prime=pr, SylowSubgpCohomology=HSyl, SylowSubgroup=SylowSubgroup, OneStep=True, GroupName='Normalizer(%s,Centre(SylowSubgroup(%s,%d)))'%(GroupName or GStem, GroupName or GStem,pr), useElimination=kwds.get('useElimination'),useFactorization=kwds.get('useFactorization'))
            else:
                HP = CohomologyRing(Subgroup, prime=pr, SylowSubgpCohomology=HSyl, SylowSubgroup=SylowSubgroup, OneStep=True, GroupName='IntermediateSubgroup(%s,%d)'%(GroupName or GStem,pr), useElimination=kwds.get('useElimination'),useFactorization=kwds.get('useFactorization'))

        ############
        # By now, we have both subgroups and their cohomology rings.
        if not HP.completed:
            HP.make()
        # not needed for HSyl, since it was computed when we
        # initialised HP

        ############
        # By now, SylowSubgroup is equal to HP.sylow_subgroup() under the canonical map from Subgroup to HP.group().
        # However, it is not necessarily true that their GENERATING SETS are related by the canonical map.
        # This will be taken care of in MODCOHO.__init__.            

        ##################################
        # 
        # Extending the group key, so that we can finally see if it is
        # cached.
        #
        # We try to find the cohomology ring in the cache.
        # It is already tested that it is not on disk

        CacheKey = (KEY, GStem, HP._key, pr)
        OUT = self._cache.get(CacheKey)

        if OUT is not None:
            if OUT._key != CacheKey:
                similarity = _IsKeyEquivalent(CacheKey,OUT._key)
                if similarity:
                    if similarity == 1:
                        print 'Warning: Stored cohomology data have a different group description, but they seem to be equivalent'
                    return OUT
                else:
                    raise ValueError, "Cohomology ring cache is broken for %s"%repr(OUT)
            else:
                return OUT
        # If we have no GroupId, we have already computed permutation representations
        if len(KEY)==1:
            if not Hfinal.IsPermGroup():
                GPerm = gap(KEY[0])
                tmpPhi = gap('GroupHomomorphismByImages(%s,%s,GeneratorsOfGroup(%s),GeneratorsOfGroup(%s))'%(Hfinal.name(),GPerm.name(),Hfinal.name(),GPerm.name()))
                PPerm = gap('Group(List([1..Length(GeneratorsOfGroup(%s))], x->Image(%s,GeneratorsOfGroup(%s)[x])))'%(Subgroup.name(),tmpPhi.name(),Subgroup.name()))
            else:
                GPerm = Hfinal
                PPerm = Subgroup
                tmpPhi = None

        if len(KEY)==1:
            OUT = MODCOHO(Hfinal, pr, HP, Subgroup, GroupName=GroupName, GStem=GStem, GroupDescr=kwds.get('GroupDescr'), SubgpId=SubgpId, SubgpPerm=PPerm, GPerm=GPerm, useElimination=kwds.get('useElimination'),useFactorization=kwds.get('useFactorization'))
        else:
            OUT = MODCOHO(Hfinal, pr, HP, Subgroup, GroupName=GroupName, GStem=GStem, GroupDescr=kwds.get('GroupDescr'), SubgpId=SubgpId, GroupId=KEY, useElimination=kwds.get('useElimination'),useFactorization=kwds.get('useFactorization'))
        if OUT._key != CacheKey:
            if len(OUT._key[0])==1:
                GKEY = ''.join([t.strip() for t in OUT._key[0][0].split()])
                tmpKey = list(OUT._key)
                tmpKey[0] = (GKEY,)
                OUT.setprop('_key',tuple(tmpKey))
            if OUT._key != CacheKey:
                raise RuntimeError, "Keys for caching are corrupted"
            else:
                print_protocol( "Trying to update data on disk", OUT)
                safe_save(OUT,OUT.autosave_name())
        #self._cache[CacheKey] = OUT # not necessary, since MODCOHO.__init__ inserts into the cache
        _gap_init(OUT.group().parent())
        return OUT

    def set_user_db(self, s = None):
        """
        Define the location of a user-dependent cohomology database

        INPUT:

        ``s``, a string providing a folder name, or ``None``.

        OUTPUT:

        If ``s`` is a string, a cohomology database in the folder
        ``s`` will be activated as the user's private cohomology data
        base. Write permission for that folder is required. If it
        is ``None``, a private database in a default location will
        be activated.

        NOTE:

        If necessary, the folder will be created as soon as data from
        ``s`` are requested.

        EXAMPLES:

        We create a cohomology ring, whose data files are rooted in a
        temporary directory; it will be removed as soon as Sage is
        quit.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing(8,3)
            sage: H.root.startswith(os.path.realpath(tmp_root))
            True

        """
        import os
        if s is None:
            s = os.path.realpath(os.path.join(DOT_SAGE,'pGroupCohomology','db'))
        if not isinstance(s,basestring):
            raise TypeError, "String (pathname) expected"
        if os.path.exists(s):
            if not os.path.isdir(s):
                raise OSError, "There is a file %s that we won't overwrite"%s
            if not os.access(s,os.W_OK):
                raise OSError, "The folder %s is not writeable"%s
        else:
            os.makedirs(s)
        COHO.user_db = s

    def user_db(self,*args, **kwds):
        """
        Retrieve a cohomology ring from a user-dependent cohomology database

        NOTE:

        By default, the currently activated private (user-dependent)
        cohomology database is hosting the computation anyway. However,
        if the user happens to have used :meth:`user_db`, the default
        has changed. So, this method is a convenient way to return to
        the original default.

        EXAMPLES:

        We create a cohomology ring, whose data files are rooted in a
        temporary directory; it will be removed as soon as Sage is
        quit. We use the optional parameter ``from_scratch=True`` in
        order to ensure that it is not loaded from the public database
        or downloaded from the web.
        ::

            sage: from pGroupCohomology import CohomologyRing
            sage: tmp_root = tmp_dir()
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: H = CohomologyRing.user_db(8,3, from_scratch=True)
            sage: print H
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computed up to degree 0
            Minimal list of generators:
            []
            Minimal list of algebraic relations:
            []

        """
        #kwds['root'] = COHO.user_db
        self.set_public_db(False)
        return self(*args, **kwds)

    def set_web_db(self, s = None):
        """
        Redefine the default location of a web source for cohomology rings

        INPUT:

        ``s``, a string providing a folder name, or ``None``.

        If ``s`` is a string, then cohomology rings will be searched
        in a web source named by ``s``. If it is ``None``, the web
        source is reset to some default location.
        
        EXAMPLES:

        The example produces files. For safety reasons, we choose
        files in a temporary directory; it will be removed as soon as
        Sage is quit.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.set_web_db('http://users.minet.uni-jena.de/cohomology/testdb/')

        During doctests, the access to the internet is usually not available::

            sage: H=CohomologyRing.web_db('8gp3')
            Traceback (most recent call last):
            ...
            RuntimeError: No web access during doctests
            sage: from pGroupCohomology.resolution import OPTION
            sage: OPTION('use_web_in_doctest')
            sage: H=CohomologyRing.web_db('8gp3') # needs internet access
            sage: OPTION('nouse_web_in_doctest')
            sage: print H
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
        from pGroupCohomology.cohomology import COHO
        if s is None:
            s = 'http://cohomology.uni-jena.de/db/'
        if isinstance(s,basestring):
            COHO.web_db = s
        else:
            raise ValueError, "String expected"    


    # TODO: non prime power groups
    def web_db(self, GStem, websource = None, prime=None):
        """
        Import a cohomology ring from a web source.

        NOTE:

        Usually this function would not be directly used. It is
        automatically called by
        :func:`~pGroupCohomology.CohomologyRing` if a cohomology ring
        can not be found in a local folder.

        INPUT:

        - ``GStem``, a string so that ``GStem+'.tar.gz'`` can be found
          in the web source, if it is a prime power group, or
          ``'H'+GStem+'mod%d.sobj'%prime`` otherwise.
        - ``websource``: If ``None`` (default), a default location
          (respectively the location provided by
          :meth:`~pGroupCohomology.factory.CohomologyRingFactory.set_web_db`)
          is chosen. Otherwise, it should be a web address.
        - ``prime``: An optional prime, the modulus of the cohomology
          ring. It must be provided if ond *only* if the group is not
          a prime power group.

        NOTE:

        During doctests, the web access is usually switched off, 

        EXAMPLES:

        The example produces files. For safety reasons, we choose
        files in a temporary directory; it will be removed as soon as
        Sage is quit. We use a protocol mode, so that it is visible
        what happens behind the scenes.
        ::

            sage: tmp_root = tmp_dir()
            sage: from pGroupCohomology import CohomologyRing
            sage: from pGroupCohomology.resolution import OPTION
            sage: CohomologyRing.set_user_db(tmp_root)
            sage: OPTION('prot')
            <BLANKLINE>
            sage: H=CohomologyRing.web_db('8gp3', websource='http://users.minet.uni-jena.de/cohomology/testdb/')
            Traceback (most recent call last):
            ...
            RuntimeError: No web access during doctests

        Apparently, during doctests, we usually disallow web access.
        But for this one test, we switch it on::

            sage: OPTION('use_web_in_doctest')
            <BLANKLINE>
            sage: H=CohomologyRing.web_db('8gp3', websource='http://users.minet.uni-jena.de/cohomology/testdb/') # needs internet access
            Press Ctrl-c to interrupt web access.
            Accessing http://users.minet.uni-jena.de/cohomology/testdb/8gp3.tar.gz
            Downloading and extracting archive file
            The state descriptor of the to-be-unpickled ring is expected to be provided at .../8gp3/dat/State.sobj
            sage: OPTION('nouse_web_in_doctest')
            sage: print H
            Cohomology ring of Dihedral group of order 8 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [c_2_2: 2-Cocycle in H^*(D8; GF(2)),
             b_1_0: 1-Cocycle in H^*(D8; GF(2)),
             b_1_1: 1-Cocycle in H^*(D8; GF(2))]
            Minimal list of algebraic relations:
            [b_1_0*b_1_1]

        In order to not break the other doc tests, we now switch the
        protocol mode off.
        ::
        
            sage: OPTION('noprot')
            <BLANKLINE>
              
        """
        import os
        from pGroupCohomology.resolution import OPTION
        if not OPTION.opts.get('use_web_in_doctest'):
            import inspect
            for stackline in inspect.stack():
                s = stackline[1]
                if isinstance(s,basestring) and 'doctest' in s:
                    raise RuntimeError("No web access during doctests")
        if self._use_public_db:
            root = COHO.public_db
        else:
            root = COHO.user_db
        if websource is None:
            websource = COHO.web_db
        if not websource.endswith('/'):
            websource = websource + '/'
        
        # First step: Download the tar file from the web and unpack it to root
        print_protocol("Press Ctrl-c to interrupt web access.")
        if prime is None:
            print_protocol( "Accessing "+websource + GStem + '.tar.gz')
            f = urllib2.urlopen(websource + GStem + '.tar.gz')
            print_protocol( "Downloading and extracting archive file")
            T = tarfile.open(fileobj=f, mode='r|*')
            T.extractall(path=root)
        else:
            if not (hasattr(prime,'is_prime') and prime.is_prime()):
                raise ValueError, '``prime`` must be a prime number'
            print_protocol( "Accessing "+websource + 'H'+GStem + 'mod%d.sobj'%prime)
            f = urllib2.urlopen(websource + 'H'+GStem + 'mod%d.sobj'%prime)
            OPTION.opts['@use_this_root@'] = root
            try:
                print_protocol( "Downloading and extracting cohomology ring")
                OUT = loads(f.read())
            except:
                OUT = None
            if isinstance(OUT,COHO):
                GStemList = GStem.split('gp')
                if len(GStemList)==2:
                    if GStemList[0].isdigit() and GStemList[1].isdigit():
                        q = int(GStemList[0])
                        n = int(GStemList[1])
                        if OUT.GroupNames.has_key((q,n)):
                            if OUT.GroupName!=OUT.GroupNames[q,n][0] or OUT.GroupDescr!=OUT.GroupNames[q,n][1]:
                                OUT.setprop('GroupName',OUT.GroupNames[q,n][0])
                                OUT.setprop('GroupDescr',OUT.GroupNames[q,n][1])
                safe_save(OUT,os.path.join(root,'H'+GStem + 'mod%d.sobj'%prime))
                _gap_init(OUT.group().parent())
                return OUT
            else:
                raise RuntimeError, "No cohomology ring found in "+websource + 'H'+GStem + 'mod%d.sobj'%prime            

        ## Second step: load the cohomology ring and return it
        ## It is now the prime power case.
        OPTION.opts['@use_this_root@'] = root
        try:
            OUT = load(os.path.join(root, GStem, 'H'+GStem))  # realpath here?
            r = OUT.root # this line may imply that the downloaded data are changed on disk in order to make them fit
        except:
            OUT = None
        if isinstance(OUT,COHO):
            GStemList = GStem.split('gp')
            if len(GStemList)==2:
                if GStemList[0].isdigit() and GStemList[1].isdigit():
                    q = int(GStemList[0])
                    n = int(GStemList[1])
                    if OUT.GroupNames.has_key((q,n)):
                        if OUT.GroupName!=OUT.GroupNames[q,n][0] or OUT.GroupDescr!=OUT.GroupNames[q,n][1]:
                            OUT.setprop('GroupName',OUT.GroupNames[q,n][0])
                            OUT.setprop('GroupDescr',OUT.GroupNames[q,n][1])
                            safe_save(OUT, OUT.autosave_name())
        else:
            raise RuntimeError, "No cohomology ring found in "+websource + GStem + '.tar.gz'
        _gap_init(OUT.group().parent())
        return OUT


def _IsKeyEquivalent(k1, k2):
    """
    Test equivalence of keys of cohomology rings

    INPUT:

    ``k1``, ``k1``: Keys of cohomology rings

    OUTPUT:
    
    - 0, if the keys are essentially different,
    - 1 if they are equivalent,
    - 2 if they are equal (up to file location)

    NOTE:

    If the keys are equivalent, the ring presentations of the cohomology ring
    should be equal.

    EXAMPLES::

        sage: from pGroupCohomology import CohomologyRing
        sage: from pGroupCohomology.factory import _IsKeyEquivalent
        sage: tmp_root = tmp_dir()
        sage: CohomologyRing.set_user_db(tmp_root)
        sage: G = gap('SymmetricGroup(6)')
        sage: G.IdGroup()
        [ 720, 763 ]
        sage: H1 = CohomologyRing(G,prime=2,GroupName='Sym6')
        sage: H2 = CohomologyRing(720,763,prime=2)
        sage: _IsKeyEquivalent(H1._key,H2._key)
        0

    In fact, mapping the generators of ``H1.group()`` to the generators
    of ``H2.group()`` does not result in a group isomorphism. This is tested as
    follows::

        sage: H1.group().canonicalIsomorphism(H2.group())
        fail

    So, we chose a different generating system for ``G``. In order to
    have a reproducible doc test, we choose an explicit group isomorphism::

        sage: phiG = gap('GroupHomomorphismByImages( Group([(1,2),(1,2,3,4,5,6)]), SymmetricGroup([ 1 .. 6 ]), [(1,2),(2,3,5,6,4)], [(5,6),(1,2,3,4,5)])')
        sage: Gnew = gap('Group(List([1..Length(GeneratorsOfGroup(%s))],x->Image(%s,GeneratorsOfGroup(%s)[x])))'%(H2.group().name(),phiG.name(),H2.group().name()))
        sage: H1new = CohomologyRing(Gnew,prime=2,GroupName='Sym6New')

    Now, the group keys are in fact essentially equal, since the
    program realises that the generators of Gnew correspond to those
    of ``SmallGroup(720,763)`` and thus identifies both rings::

        sage: _IsKeyEquivalent(H1new._key,H2._key)
        2
        sage: H2 is H1new
        True

    Now, we do the opposite and chose a generating set for
    ``SmallGroup(720,763)`` equivalent to the generating set for
    ``G``. Again, we define the isomorphism explicitly::

        sage: G2 = gap('SmallGroup(720,763)')
        sage: phiG2 = gap('GroupHomomorphismByImages( SymmetricGroup([ 1 .. 6 ]), Group([(1,2),(1,2,3,4,5,6)]), [(5,6),(1,2,3,4,5)], [(1,2),(2,6,3,4,5)])')
        sage: G2new = gap('Group(List([1..Length(GeneratorsOfGroup(%s))],x->Image(%s,GeneratorsOfGroup(%s)[x])))'%(G.name(),phiG2.name(),G.name()))
        sage: H2new = CohomologyRing(G2new,prime=2,GroupName='Sym6New2')

    Now the keys of the cohomology ring are equivalent, but not equal::

        sage: _IsKeyEquivalent(H2new._key,H1._key)
        1
        sage: H2new._key
        (('Group([(1,6,3,4,5,2),(3,6)])',), 'Sym6New2', ((16, 11), '.../16gp11/dat/State'), 2)
        sage: H1._key
        (('Group([(1,2,3,4,5,6),(1,2)])',), 'Sym6', ((16, 11), '.../16gp11/dat/State'), 2)

    """
    from pGroupCohomology.resolution import gap
    if len(k1)!=len(k2):
        return 0
    if k1[0]==k2[0]:
        similarity = 2
    else:
        if len(k1[0])==1:
            G1 = gap(k1[0][0])
        else:
            G1 = gap('SmallGroup(%d,%d)'%(k1[0][0],k1[0][1]))
        if len(k2[0])==1:
            G2 = gap(k2[0][0])
        else:
            G2 = gap('SmallGroup(%d,%d)'%(k2[0][0],k2[0][1]))
        if repr(G1.canonicalIsomorphism(G2))=='fail':
            return 0
        else:
            similarity = 1
    if len(k1)==3:
        return min(similarity, _IsKeyEquivalent(k1[-1],k2[-1]))
    return similarity

CohomologyRing = CohomologyRingFactory()
CohomologyRing.__doc__ = r"""
Constructor for modular cohomology rings of finite groups.

This constructor is an instance of
:class:`~pGroupCohomology.factory.CohomologyRingFactory`.  See there
and see :mod:`pGroupCohomology` for more examples.

The constructor can be called directly. Then, it is first checked
whether the completely computed cohomology ring of the given group is
part of some database, or whether it can be downloaded. If this is
not the case, a new cohomology ring is created, being part of a
user defined database.

Using :meth:`~pGroupCohomology.factory.CohomologyRingFactory.set_user_db`, the
location of the user defined database can be determined. By
:meth:`~pGroupCohomology.factory.CohomologyRingFactory.user_db`, one can
explicitly ask for taking data from the user defined database. The
input formats for calling :func:`~pGroupCohomology.CohomologyRing` and
for calling :meth:`~pGroupCohomology.factory.CohomologyRingFactory.user_db`
or :meth:`~pGroupCohomology.factory.CohomologyRingFactory.public_db` are the same.

INPUT:

**Parameters describing the group**

- A finite group `G` , either

  * given by an integer ``q`` and a positive number ``n``, determining
    an entry of the SmallGroups library, or
  * given as an object in the Gap interface  
- ``GroupName`` (optional string): a name for the group. If the 
  group `G` is given in the Gap interface and if it is not provided with
  a custom name (using Gap's ``SetName``) then ``GroupName`` *must* be
  provided.
- ``GroupDescr`` (optional string): a description of the group. This can be
  any string, and is used when printing the cohomology ring or creating a
  web-site for it.
- If the group is not of prime power order, the optional parameter ``prime``
  must be set to a prime number.

**Parameters describing the database**

- ``websource``: If it is ``False``, it is not attempted to download data
  from some database in the web. If it is a string providing the location
  of a database in the web, then it is attempted to download the data from
  there. If ``websource`` is not given then first it is tried to look up
  data in the local file system, and if this fails then it is attempted to
  download the data from some default location in the web.
- ``from_scratch`` (default ``False``): If it is ``True``, this cohomology
  ring may be taken from the cache or from the private database, but will
  not be taken from the public database nor from a web repository. Note that
  this will only take effect on this ring; cohomology rings of subgroups,
  occuring during the computation, will still be reloaded.

**Parameters modifying the algorithm**

- ``useElimination`` (optional, default ``None``): If ``True``, the 
  elimination method is used for trying to construct the Dickson classes.
  If ``False``, the linear algebra method is used for that purpose. By
  default, the linear algebra method is chosen, unless there is a Dickson
  class in degree greater than 18 (for prime power groups) or 20 (for non
  prime power groups).
- ``DicksonExp`` (optional integer, default = 3): If the elimination
  method for finding the Dickson classes is used, it is needed to set a
  bound for the power to which the Dickson classes might be raised: If
  `G` is a `p`-group and `n` is the given ``DicksonExp``, then the
  Dickson classes of the elementary abelian sub-groups of `G` are raised
  to the power of `p^0,p^1,...,p^n` before trying to simultaneously lift 
  them to `G`. We do not know any example in which the default value would
  not suffice.
- ``useFactorization`` (optional boolean, default True): Try to replace
  the Dickson classes of `G` by their minimal non-constant factors. This
  may simplify some computations, but there are rare examples in which the
  factorisation is a bigger problem than a high degree bound.
- ``auto`` (optional integer, default = 2 for abelian groups, and = 4
  otherwise): Only applies to the case of prime power groups. A quick but
  potentially memory consuming method for lifting chain maps will be 
  used in degree at most ``auto``. For prime power groups up to orders
  around 500, the default value seems to be heuristically best.
- ``useSlimgb`` / ``useStd`` (optinal boolean): Use Singular's ``slimgb``
  (resp. ``std``) for computing the Groebner basis of the relation ideal.
  If not specified, Singular's ``groebner`` method is chosen, which uses
  a heuristics to find the best algorithm for the computation of the
  Groebner basis.

**Global options**

``options`` (optional string or list of strings): set/unset global options.

There are various options, e.g. concerning protocol output, that apply to *all*
cohomology rings when set for one ring. Each option is set by a string, and unset
by prepending ``'no'`` to that string.

  **Available options**

  * ``'prot'`` [not default], display protocol
  * ``'timing'`` [not default], display timing
  * ``'useMTX'`` [default], use :class:`~pGroupCohomology.mtx.MTX`
    matrices for linear algebra over finite fields, when computing
    the ring structure. Note that the resolutions will always be
    computed using the Aachen
    `C MeatAxe <http://www.math.rwth-aachen.de/homes/MTX/>`_. By
    consequence, if ``useMTX`` is turned off, much time is spent
    on the conversion of different matrix types.
  * ``'save'`` [default], save intermediate results
  * ``'sparse'`` [default], remove temporarily unneeded data from
    memory 
  * ``'liftlist'`` [not default], try to lift a whole bunch of
    cochains at once

The options can also be (un)set later, by using the method 
:meth:`~pGroupCohomology.cohomology.COHO.option`.

The options ``'prot'`` and ``'timing'`` are useful to see the progress
of lengthy computations. If ``'save'`` is set, the ring will be saved
after each computed degree. This will come in handy if a long computation
was interrupted. Note, however, that many data, including a minimal
projective resolution for prime power groups, will *always* be saved on
disk.

The following options only apply to prime power groups, are somehow
experimental, and are not officially supported.

* If ``'useMTX'`` is unset, the computation time usually dramatically
  increases. So, we strongly recommend to not unset ``'useMTX'``.
* Using the option ``'sparse'`` not only allows for computation of rather
  big examples; it turns out that it improves the computation time in small 
  examples. So, it is strongly recommended to not unset ``'sparse'``.
* With the option ``'liftlist'``, some examples are faster, others are slower. 
  On the groups of order 64, it is slightly faster to not use this option, 
  therefore our default is to not use it.

"""

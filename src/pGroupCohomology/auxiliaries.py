#*****************************************************************************
#
#    Auxiliar functions for computations in modular group cohomology
#
#    Copyright (C) 2015 Simon A. King  <simon.king@uni-jena.de>
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
Auxiliary functions for the optional pGroupCohomology package.

AUTHORS:

- Simon King <simon.king@uni-jena.de>

"""

from __future__ import print_function, absolute_import
import os
from sage.env import SAGE_ROOT, DOT_SAGE

## All other modules will import this version of singular

from sage.all import singular

####################
## The SharedMeatAxe library needs initialisation, which is
## automatically done when importing from sage.libs.meataxe.
## Since the library is shared, it is enough to do this once
## per session, not in each individual module linked against
## libmtx.
import sage.libs.meataxe

##########
## Save data without following soft links
from sage.all import save
def safe_save(obj, path):
    """
    Save data after unlinking the target, if it is a symlink.

    EXAMPLES::

        sage: from pGroupCohomology.auxiliaries import safe_save
        sage: d = tmp_dir()
        sage: save(1, os.path.join(d, 'orig'))
        sage: os.symlink(os.path.join(d, 'orig.sobj'), os.path.join(d, 'copy.sobj'))

    By saving data to the symlink, we change the original data::

        sage: save(2, os.path.join(d, 'copy.sobj'))
        sage: load(os.path.join(d, 'orig.sobj'))
        2
        sage: load(os.path.join(d, 'copy.sobj'))
        2

    The function :func:`safe_save` protects the original data::

        sage: d = tmp_dir()
        sage: save(1, os.path.join(d, 'orig'))
        sage: os.symlink(os.path.join(d, 'orig.sobj'), os.path.join(d, 'copy.sobj'))
        sage: safe_save(2, os.path.join(d, 'copy.sobj'))
        sage: load(os.path.join(d, 'orig.sobj'))
        1
        sage: load(os.path.join(d, 'copy.sobj'))
        2

    """
    if not path.endswith('.sobj'):
        path = path + '.sobj'
    if os.path.islink(path):
        os.unlink(path)
    save (obj, path)

###################################
## Helper for unpickling old data

class unpickle_old_mtx:
    """
    Helper for old pickles of MTX matrices.

    It unpickles what was pickled with the old-style
    ``p_group_cohomology`` spkg. This holds, for example, for the
    data found in the database that is shipped with this optional
    package.
    """
    def __call__(self, *args, **kwds):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: print(CohomologyRing(64,12))  # indirect doctest
            Cohomology ring of Small Group number 12 of order 64 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [b_2_1: 2-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             c_2_2: 2-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             c_2_3: 2-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             b_1_1: 1-Cocycle in H^*(SmallGroup(64,12); GF(2))]
            Minimal list of algebraic relations:
            [a_1_0^2,
             a_1_0*b_1_1,
             b_2_1*a_1_0,
             b_2_1*b_1_1^2+b_2_1^2]

        """
        from sage.matrix.matrix_gfpn_dense import mtx_unpickle
        return mtx_unpickle(*args, **kwds)

class unpickle_old_resl:
    """
    Helper for old pickles of :class:`~pGroupCohomology.resolution.RESL`.

    It unpickles what was pickled with the old-style
    ``p_group_cohomology`` spkg.
    """
    def __call__(self, *args, **kwds):
        """
        TESTS::

            sage: from pGroupCohomology import CohomologyRing
            sage: print(CohomologyRing(64,12))  # indirect doctest
            Cohomology ring of Small Group number 12 of order 64 with coefficients in GF(2)
            <BLANKLINE>
            Computation complete
            Minimal list of generators:
            [b_2_1: 2-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             c_2_2: 2-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             c_2_3: 2-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             a_1_0: 1-Cocycle in H^*(SmallGroup(64,12); GF(2)),
             b_1_1: 1-Cocycle in H^*(SmallGroup(64,12); GF(2))]
            Minimal list of algebraic relations:
            [a_1_0^2,
             a_1_0*b_1_1,
             b_2_1*a_1_0,
             b_2_1*b_1_1^2+b_2_1^2]

        """
        from pGroupCohomology.resolution import resl_sparse_unpickle
        return resl_sparse_unpickle(*args, **kwds)

from sage.structure.sage_object import register_unpickle_override
register_unpickle_override('pGroupCohomology.mtx', 'MTX_unpickle_class', unpickle_old_mtx)
register_unpickle_override('pGroupCohomology.resolution', 'RESL_sparse_unpickle_class', unpickle_old_resl)

#######################################
## Options for cohomology computations
#######################################

default_options = (('useMTX',True),
                   ('reload',True),
                   ('save',True),
                   ('sparse',False),
                   ('autolift',1),
                   ('autoliftElAb',0),
                   ('SingularCutoff',70),
                   ('NrCandidates',1000),
                   ('use_web',True))

coho_options = dict(default_options)

################################################
##   Logging
################################################

import logging, weakref
_previous_slf = None
coho_logger = logging.getLogger("pGroupCohomology")
stream_handler = logging.StreamHandler()

class CohoFormatter(logging.Formatter):
    """
    Formatter that groups log messages.

    EXAMPLE::

        sage: from pGroupCohomology.auxiliaries import coho_logger
        sage: from pGroupCohomology import CohomologyRing
        sage: CohomologyRing.reset()
        sage: L = [ZZ, ZZ, ZZ['x'], ZZ['x'], ZZ['x'], ZZ, ZZ]
        sage: for i,P in enumerate(L):
        ....:     coho_logger.warn('warning %d', P, i)
        ....:
        Integer Ring:
                  warning 0
                  warning 1
        Univariate Polynomial Ring in x over Integer Ring:
                  warning 2
                  warning 3
                  warning 4
        Integer Ring:
                  warning 5
                  warning 6

    """
    def __init__(self, fmt=None, datefmt=None):
        """
        See :class:`logging.Formatter`.
        """
        logging.Formatter.__init__(self, fmt, datefmt)
        self._orig_fmt = self._fmt
        self.obj = weakref.ref(CohoFormatter)

    def reset(self):
        """
        Reset the formatter.

        By resetting, the next log message is guaranteed to be prepended
        by the string representation of the first argument of the
        log record.

        EXAMPLES::

            sage: from pGroupCohomology.auxiliaries import coho_logger
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.reset()
            sage: coho_logger.warn('message 1', ZZ)
            Integer Ring:
                      message 1

        When we now log a message that is associated to the integer ring
        as well, then we just see the message, not the integer ring::

            sage: coho_logger.warn('message 2', ZZ)
                      message 2

        But sometimes (in particular when other output has happened after
        logging the previous event), we want to see what object the log
        message belongs to::

            sage: CohomologyRing.reset()    # indirect doctest
            sage: coho_logger.warn('message 3', ZZ)
            Integer Ring:
                      message 3

        """
        self.obj = weakref.ref(CohoFormatter)

    def format(self, record):
        """
        INPUT:

        record, an instance of :class:`logging.LogRecord`.

        This formatter accesses ``obj=record.args[0]`` (the args
        must thus be non-empty) and tests whether it coincides with
        with the ``obj`` obtained from the previously obtained log
        record. If the differ, then the string representation is
        prepended to the log message, which also will be indented.

        In that way, the log messages are grouped in blocks, so that
        the human eye can more easily grasp what log message is
        associated with what object.

        ASSUMPTION:

        ``record.args[0]`` allows a weak reference.

        EXAMPLES::

            sage: from pGroupCohomology.auxiliaries import coho_logger
            sage: from pGroupCohomology import CohomologyRing
            sage: CohomologyRing.reset()
            sage: L = [ZZ, ZZ, ZZ['x'], ZZ['x'], ZZ['x'], ZZ, ZZ]
            sage: for i,P in enumerate(L):
            ....:     coho_logger.warn('warning %d', P, i)  # indirect doctest
            ....:
            Integer Ring:
                      warning 0
                      warning 1
            Univariate Polynomial Ring in x over Integer Ring:
                      warning 2
                      warning 3
                      warning 4
            Integer Ring:
                      warning 5
                      warning 6

        """
        # record.args[0] is the object (resolution, map cohomology ring)
        # that this log record belongs to.
        obj = record.args[0]
        if obj is None:
            self.obj = weakref.ref(CohoFormatter)
            self.objstr = ""
            objstr = ""
        elif isinstance(obj, basestring):
            if self.obj != obj:
                objstr = obj+': '
                self.obj = obj
                if len(objstr)>10:
                    objstr = objstr+os.linesep+10*" "
                    self.objstr = "          "
                else:
                    self.objstr = " "*len(objstr)
            else:
                objstr = self.objstr
        else:
            if isinstance(self.obj, basestring) or (self.obj() is not obj):
                objstr = "{}: ".format(repr(obj))
                self.obj = weakref.ref(obj)
                if len(objstr)>10:
                    objstr = objstr+os.linesep+10*" "
                    self.objstr = "          "
                else:
                    self.objstr = " "*len(objstr)
            else:
                objstr = self.objstr
        self._fmt = objstr + self._orig_fmt
        record.args = record.args[1:]
        return logging.Formatter.format(self, record)

stream_handler.setFormatter(CohoFormatter())
coho_logger.addHandler(stream_handler)
coho_logger.setLevel(logging.WARN)

########################
## Initialisation of Gap
## The other modules import gap from `auxiliaries`

from sage.libs.gap.libgap import libgap as gap

def _gap_init(seed=100):
    """
    Resets the random seed of GAP and (if necessary) reads three libraries.

    TEST:

    This function is automatically executed when the library is
    loaded.  Hence, the GAP functions and global variables are
    available right after the import statement::

        sage: from pGroupCohomology.auxiliaries import _gap_init
        sage: gap.eval('exportMTXLIB') == '"MTXLIB=%s; export MTXLIB; "'%os.environ['MTXLIB']
        True

    After a crash of GAP, the global variable ``exportMTXLIB`` is unknown. But it
    is again defined using ``_gap_init``.
    ::

        sage: gap.quit()
        sage: gap.eval('exportMTXLIB') == "MTXLIB=%s; export MTXLIB; "%os.environ['MTXLIB']
        Traceback (most recent call last):
        ...
        RuntimeError: Gap produced error output
        Error, Variable: 'exportMTXLIB' must have a value
        <BLANKLINE>
           executing exportMTXLIB;
        sage: _gap_init()   # indirect doctest
        sage: gap.eval('exportMTXLIB') == '"MTXLIB=%s; export MTXLIB; "'%os.environ['MTXLIB']
        True

    Moreover, the random seed of GAP is reset.
    ::

        sage: libgap.eval('List([1..10],i->Random(1,100000))')
        [ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]
        sage: _gap_init()
        sage: libgap.eval('List([1..10],i->Random(1,100000))')
        [ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]

    """
    from sage.all import set_random_seed
    set_random_seed(seed)
    # Read the library, if it deems needed
    if not gap.IsBoundGlobal("exportMTXLIB"):
        gap.Read(os.path.join(SAGE_ROOT,'local','share','sage','ext','gap','modular_cohomology','GapMaxels.g'))
        gap.Read(os.path.join(SAGE_ROOT,'local','share','sage','ext','gap','modular_cohomology','GapMB.g'))
        gap.Read(os.path.join(SAGE_ROOT,'local','share','sage','ext','gap','modular_cohomology','GapSgs.g'))
        #~ gap.eval('DeclareGlobalVariable("exportMTXLIB")') # exportMTXLIB is declared in GapMB.g
        gap.eval('InstallValue(exportMTXLIB,"MTXLIB=%s; export MTXLIB; ")'%(os.path.join(DOT_SAGE,"meataxe")))
    # Reset the random generator
    gap.eval('Reset(GlobalMersenneTwister, {})'.format(seed))
    gap.eval('Reset(GlobalRandomSource, {})'.format(seed))

_gap_init()

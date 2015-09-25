#*****************************************************************************
#
#    Auxiliar functions for pGroupCohomology
#
#    Copyright (C) 2015 Simon A. King  <simon.king@uni-jena.de> and
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
"""
Auxiliary functions for the optional pGroupCohomology package.

AUTHORS:

- Simon King <simon.king@uni-jena.de>

"""

import os
from sage.env import SAGE_ROOT

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
## Auxiliary class managing options

class OPTION:
    """
    Set/unset global options fro cohomology computations.

    INPUT:

    Either ``opt`` (string) or no input.

    OUTPUT:

    - If no input is given, the value of all options is displayed.
    - An option is set if ``opt`` is one of
       * 'prot' [not default], display protocol
       * 'timing' [not default], display timing
       * 'useMTX' [default], use MTX matrices for linear algebra
       * 'reload' [default], reload differentials from file
       * 'save' [default], save intermediate results
       * 'sparse' [default], automatic export of lifts, if Urbild GB is loaded
       * 'liftlist' [not default], try to lift a whole bunch of cochains (often not faster)
       * 'use_web_in_doctest' [not default], allow web access during doctests
    - If ``opt`` is ``'no'+X``, where ``X`` is one of the above strings, the
      corresponding option is unset.

    NOTE:

    The options are stored in the attribute OPTION.opts, a dictionary.
    If option 'prot' is set, some information about the progress of
    computation is displayed.
    If option 'timing' is set, timings for various critical steps
    of the computation are displayed (CPU and Wall times).
    See :mod:`pGroupCohomology`, :mod:`~pGroupCohomology.cohomology` and 
    :class:`pGroupCohomology.resolution.RESL` for use cases and further 
    details.
    
    EXAMPLES::

        sage: from pGroupCohomology.auxiliaries import OPTION
        sage: sorted(OPTION.opts.items())
        [('SingularCutoff', 70),
         ('liftlist', False),
         ('prot', False),
         ('reload', True),
         ('save', True),
         ('sparse', True),
         ('timing', False),
         ('useMTX', True),
         ('use_web_in_doctest', False)]
        sage: OPTION('nosave')
        sage: OPTION('timing')
        sage: sorted(OPTION.opts.items())
        [('SingularCutoff', 70),
         ('liftlist', False),
         ('prot', False),
         ('reload', True),
         ('save', False),
         ('sparse', True),
         ('timing', True),
         ('useMTX', True),
         ('use_web_in_doctest', False)]

    We return to the original options, in order to not break
    the other doc tests.
    ::

        sage: OPTION('save')
        sage: OPTION('notiming')

    """
    opts = {'prot':False, 'timing':False, 'useMTX':True, 'reload':True,'save':True,'sparse':True, 'liftlist':False, 'SingularCutoff':70, 'use_web_in_doctest':False}
    def __init__(self, opt=''):
        """
        TESTS::

            sage: from pGroupCohomology.auxiliaries import OPTION
            sage: sorted(OPTION.opts.items())
            [('SingularCutoff', 70),
             ('liftlist', False),
             ('prot', False),
             ('reload', True),
             ('save', True),
             ('sparse', True),
             ('timing', False),
             ('useMTX', True),
             ('use_web_in_doctest', False)]
            sage: OPTION('nosave')   # indirect doctest
            sage: OPTION('timing')
            sage: sorted(OPTION.opts.items())
            [('SingularCutoff', 70),
             ('liftlist', False),
             ('prot', False),
             ('reload', True),
             ('save', False),
             ('sparse', True),
             ('timing', True),
             ('useMTX', True),
             ('use_web_in_doctest', False)]

        We return to the original options, in order to not break
        the other doc tests.
        ::

            sage: OPTION('save')
            sage: OPTION('notiming')

        """
        if isinstance(opt, str):
            if opt=='':
                for X in OPTION.opts.items():
                    print str(X[0])+': '+str(X[1])
                return
            if len(opt)>1 and opt[:2]=='no':
                self.__class__.opts[opt[2:]] = False
            else:
                self.__class__.opts[opt] = True
        else:
            raise TypeError, "option must be of type <str>"
        if opt=='noprot':
            global _previous_label
            _previous_label = ''

    def __repr__(self):
        """
        TESTS::

            sage: from pGroupCohomology.auxiliaries import OPTION
            sage: sorted(OPTION.opts.items())
            [('SingularCutoff', 70),
             ('liftlist', False),
             ('prot', False),
             ('reload', True),
             ('save', True),
             ('sparse', True),
             ('timing', False),
             ('useMTX', True),
             ('use_web_in_doctest', False)]
            sage: OPTION('nosave') # indirect doctest
            sage: OPTION('timing') # indirect doctest
            sage: sorted(OPTION.opts.items())
            [('SingularCutoff', 70),
             ('liftlist', False),
             ('prot', False),
             ('reload', True),
             ('save', False),
             ('sparse', True),
             ('timing', True),
             ('useMTX', True),
             ('use_web_in_doctest', False)]

        We return to the original options, in order to not break
        the other doc tests.
        ::

            sage: OPTION('save')
            sage: OPTION('notiming')

        """
        return ''

################################################
##   Auxiliary function: Print protocol
################################################

_previous_label = ''

def print_protocol(txt, slf=None):
    """
    Print a text (if protocol mode is used).

    INPUT:

    - ``txt``, some string which must not contain a line break
    - ``slf``, some object

    OUTPUT:

    If the verbosity is at least 2, or if the Cohomology option ``'prot'`` is
    used, then ``slf.label()`` followed by ": " and ``txt`` is printed, unless
    the same label has been used in the previous usage of this function, in
    which case the text is just indented. If ``slf`` is ``None`` then
    there is no indentation.

    EXAMPLES::

        sage: from pGroupCohomology.auxiliaries import print_protocol, OPTION
        sage: def foo(n):
        ...     print_protocol('Some text')
        ...     if not n:
        ...         return True
        ...     return foo(n-1)
        ...
        sage: foo(8)
        True
        sage: OPTION('prot')
        <BLANKLINE>
        sage: foo(8)
          Some text
            Some text
              Some text
                Some text
                  Some text
                    Some text
                      Some text
                        Some text
                          Some text
        True
        sage: OPTION('noprot')
        <BLANKLINE>
        sage: set_verbose(2)
        sage: foo(8)
          Some text
            Some text
              Some text
                Some text
                  Some text
                    Some text
                      Some text
                        Some text
                          Some text
        True
        sage: set_verbose(0)
        sage: foo(8)
        True

    """
    from sage.all import get_verbose
    global _previous_label
    if OPTION.opts['prot'] or (get_verbose()>=2):
        if '\n' in txt:
            raise RuntimeError,txt
        if slf is None:
            print txt
            return
        try:
            label = slf.label()
        except AttributeError:
            label = repr(slf)
        if label == _previous_label:
            label = " "*min(8, len(label)+2)
        else:
            _previous_label = label
            label = label + ': '
        print label + txt


########################
## Initialisation of Gap

class GAP_INIT:
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
        sage: gap.eval('exportMTXLIB') == '"MTXLIB=%s; export MTXLIB; "'%os.environ['MTXLIB']
        Traceback (most recent call last):
        ...
        RuntimeError: Gap produced error output
        Error, Variable: 'exportMTXLIB' must have a value
        <BLANKLINE>
           executing exportMTXLIB;
        sage: _gap_init()   # indirect doctest
        sage: gap.eval('exportMTXLIB') == '"MTXLIB=%s; export MTXLIB; "'%os.environ['MTXLIB']
        True

    Moreover, the random seed of GAP is reset. Note that this also works
    with a different Instance of GAP.
    ::

        sage: gap.eval('List([1..10],i->Random(1,100000))')
        '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'
        sage: _gap_init()
        sage: gap.eval('List([1..10],i->Random(1,100000))')
        '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'
        sage: G2 = sage.interfaces.gap.Gap()
        sage: _gap_init(G2)
        sage: G2.eval('List([1..10],i->Random(1,100000))')
        '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'

    """
    def __init__(self):
        """
        TESTS::

            sage: from pGroupCohomology.auxiliaries import GAP_INIT
            sage: g = GAP_INIT()  # indirect doctest
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'

        """
        from sage.all import set_random_seed, current_randstate, gap
        if not hasattr(self,'_seed'):
            self._seed = 100
        set_random_seed(self._seed)
        current_randstate().set_seed_gap()
        self.mersenne = gap.State('GlobalMersenneTwister')
        self.classical = gap.State('GlobalRandomSource')

    def set_seed(self, seed=100):
        """
        Set the random seed.

        INPUT:

        An optional integer (default 100).

        EXAMPLE::

            sage: from pGroupCohomology.auxiliaries import _gap_init
            sage: _gap_init()
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'

        We now use a different seed::

            sage: _gap_init.set_seed(50)
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 83653, 8053, 99110, 37581, 73132, 24628, 1859, 33921, 12261, 81897 ]'

        Return to the default seed::

            sage: _gap_init.set_seed()
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'

        After setting a seed, it will be used when the random generator
        is reset::

            sage: _gap_init.set_seed(50)
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 83653, 8053, 99110, 37581, 73132, 24628, 1859, 33921, 12261, 81897 ]'
            sage: _gap_init()
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 83653, 8053, 99110, 37581, 73132, 24628, 1859, 33921, 12261, 81897 ]'

        """
        self._seed = seed
        self.__init__()

    def __call__(self,G=None):
        """
        INPUT:

        ``G`` -- optional instance of the GAP interface

        OUTPUT:

        Reset the random generators of ``G`` (or of ``sage.all.gap``
        if ``G`` is not provided). If necessary, also load the
        GAP programs that are needed for our cohomology computations.

        TESTS::

            sage: from pGroupCohomology.auxiliaries import _gap_init
            sage: gap.eval('exportMTXLIB') == '"MTXLIB=%s; export MTXLIB; "'%os.environ['MTXLIB']
            True
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'
            sage: _gap_init()
            sage: gap.eval('List([1..10],i->Random(1,100000))')
            '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'
            sage: G2 = sage.interfaces.gap.Gap()
            sage: G2.eval('exportMTXLIB') == '"MTXLIB=%s; export MTXLIB; "'%os.environ['MTXLIB']
            Traceback (most recent call last):
            ...
            RuntimeError: Gap produced error output
            Error, Variable: 'exportMTXLIB' must have a value
            <BLANKLINE>
               executing exportMTXLIB;
            sage: _gap_init(G2)   # indirect doctest
            sage: G2.eval('exportMTXLIB') == '"MTXLIB=%s; export MTXLIB; "'%os.environ['MTXLIB']
            True
            sage: G2.eval('List([1..10],i->Random(1,100000))')
            '[ 97172, 88236, 80252, 19356, 27190, 18332, 44166, 99250, 99181, 74959 ]'

        """
        from sage.all import gap as G0
        if G is None:
            gap = G0
        else:
            gap = G
        # Read the library, if it deems needed
        if not gap('IsBoundGlobal("exportMTXLIB")'):
            gap.eval('Read("%s/local/pGroupCohomology/GapMaxels");'%(SAGE_ROOT))
            gap.eval('Read("%s/local/pGroupCohomology/GapMB");'%(SAGE_ROOT))
            gap.eval('Read("%s/local/pGroupCohomology/GapSgs");'%(SAGE_ROOT))
            gap.eval('InstallValue(exportMTXLIB,"MTXLIB=%s; export MTXLIB; ")'%os.environ['MTXLIB'])
        # Reset the random generator
        try:
            self.mersenne._check_valid()
            self.classical._check_valid()
        except ValueError: # gap crashed
            self.__init__()
        if gap is not self.mersenne.parent():
            # we got a different gap instance,
            # thus we update our random seed
            self.mersenne = gap(self.mersenne)
            self.classical = gap(self.classical)
        gap.Reset('GlobalMersenneTwister',self.mersenne)
        gap.Reset('GlobalRandomSource',self.classical)

_gap_init = GAP_INIT()
_gap_init()

####################
## String repr. of ordinals

def Ordinals(n):
    """
    Return an ordinal number in string form

    INPUT:
    
    n -- a non-negative integer

    OUTPUT:
    
    A string representation for the n-th ordinal number

    EXAMPLES::

        sage: from pGroupCohomology.auxiliaries import Ordinals
        sage: Ordinals(1)
        '1st'
        sage: Ordinals(2)
        '2nd'
        sage: Ordinals(3)
        '3rd'
        sage: Ordinals(4)
        '4th'
        sage: Ordinals(10)
        '10th'
        sage: Ordinals(11)
        '11th'
        sage: Ordinals(12)
        '12th'
        sage: Ordinals(21)
        '21st'

    """
    i = n%10
    if i==1:
        if n%100==11:
            return '%dth'%(n)
        return '%dst'%(n)
    if i==2:
        if n%100==12:
            return '%dth'%(n)
        return '%dnd'%(n)
    if i==3:
        if n%100==13:
            return '%dth'%(n)
        return '%drd'%(n)
    return '%dth'%(n)


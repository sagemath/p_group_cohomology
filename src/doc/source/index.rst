Mod-*p* Group Cohomology Package
================================

This is the documentation for our `Sage <http://www.sagemath.org/>`_ package
on the computation of modular cohomology rings of finite groups.

Summary
-------

The source code consists of

 * Python and Cython extension modules as well as Singular and GAP functions
   written by `Simon King <https://users.fmi.uni-jena.de/~king/eindex.html>`_.
 * C-programs and Gap functions created by `David Green <https://users.fmi.uni-jena.de/~green/index-en.php>`_
   and modified by `Simon King <https://users.fmi.uni-jena.de/~king/eindex.html>`_.

The package comprises a data base of the cohomology rings of all groups of
order 64, and can access a repository of the cohomology rings of
all groups of order 128, all but 6 groups of order 243, of the Sylow
2-subgroup of the Higman-Sims group, and of the Sylow 2-subgroup of the
third Conway group. These data were produced with our package.

Since version 2.0, it can also compute the modular cohomology rings
of non prime power groups. In particular, it allows for the computation
of the modular cohomology for various primes of the first three Janko
groups, of Mathieu groups 11, 12, 22 and 23, of the McLaughlin group,
of SuzukiGroup(8), of the Higman-Sims group and of the third Conway group.
`Here are the computational results <https://users.fmi.uni-jena.de/cohomology/>`_.
It is planned (but not done yet) to include these cohomology rings in
our repository.

The standard way of creating cohomology rings is documented
in :mod:`pGroupCohomology`. More details on the available methods can be
found in the :mod:`~pGroupCohomology.factory`,
:mod:`~pGroupCohomology.cohomology` and
:mod:`~pGroupCohomology.modular_cohomology` modules. There are
also five other modules used in the background, which may be less
interesting to a casual user.

The computation of the modular cohomology rings of non prime power groups
is reduced to the case of prime power groups, possibly in several steps,
by virtue of the stable element method. The cohomology computation for prime
power groups is based on the construction of a minimal free resolution.

In both cases, we follow `Jon Carlson's <http://www.math.uga.edu/~jfc/>`_
basic approach to compute an approximation of the cohomology ring in
increasing degree, and to use criteria to prove that at some point the
approximation is actually isomorphic to the cohomology ring.

We use completeness criteria proposed by
`Dave Benson <http://www.maths.abdn.ac.uk/~bensondj/html/>`_,
`David Green <https://users.fmi.uni-jena.de/~green/index-en.php>`_,
`Simon King <https://users.fmi.uni-jena.de/~king/eindex.html>`_ and
`Peter Symonds <http://www.maths.manchester.ac.uk/~pas/>`_.
The construction of minimal free resolutions is based on an algorithm
of `David Green <https://users.fmi.uni-jena.de/~green/index-en.php>`_.

Installation
------------

Our cohomology package uses the `Small Groups <http://www-public.tu-bs.de:8080/~hubesche/small.html>`_
library of Hans Ulrich Besche, Bettina Eick and Eamonn O'Brien. Since 2018 it is
distributed as a standard package for SageMath.

Prior to version 3.0, the cohomology package provided a copy of an old
version of `MeatAxe <http://www.math.rwth-aachen.de/~MTX/>`_. Now, the package
links against a MeatAxe fork, `SharedMeatAxe <https://users.fmi.uni-jena.de/~king/SharedMeatAxe/>`_.
It is a build-time dependency and can be installed in Sage by doing
::

    sage -i meataxe
    sage -b

By `trac ticket 26001 <https://trac.sagemath.org/ticket/26001>`_, the cohomology
package can then be installed in your copy of Sage by
::

    sage -i p_group_cohomology

Testing
-------

The Cython and Python parts of the package have 100% doctest coverage, but
be warned that running the test suite requires a considerable amount of
time (easily one hour if a single thread is used). If the environment variable
``SAGE_CHECK`` is set to ``yes``, the test script is launched right after
installing the package. The same effect can be achieved by
::

    sage -i -c p_group_cohomology

Documentation
-------------

If the environment variable ``SAGE_SPKG_INSTALL_DOCS`` is set to ``yes``, then
the documentation of our spkg is automatically created and put into
``SAGE_ROOT/local/share/doc/p_group_cohomology/``.

Acknowledgements
----------------

The development of the initial version of this SPKG was funded by by the
German Science Foundation, DFG project GR 1585/4--1, and mainly accomplished
at Friedrich Schiller University Jena.

Since version 1.0.1, the further work on this SPKG was funded by Marie Curie
grant MTKD-CT-2006-042685 and was pursued at the National University of
Ireland, Galway. Since version 2.1.2, the project has returned to Jena and was
funded by DFG project KI 861/2--1.

We thank William Stein for giving us access to various computers
on which we could build test the SPKG and on which some huge computations
could be completed, and acknowledge the support by National Science
Foundation Grant No. DMS-0821725.

We are also grateful to William Stein and David Joyner for critical comments
and for testing the installation of our package on a large variety of
platforms. Suggestions of Mikael Vejdemo Johansson and John Palmieri
were very valuable for verifying the code on the computation of Massey
products.

We thank Mathieu Dutour Sikirić for his explanations how to keep track of
large lists of double cosets in GAP. We are also grateful to the GAP support
group for solving various technical problems that became imminent when
dealing with non prime power groups.

We thank Peter Symonds for interesting discussions, in particular for
suggesting to use the Poincaré series in a completeness criterion.

Versions
--------

See SPKG.txt for a more detailed account.

  * v3.2 (July 2019):

    - Detection of graded non-induced isomorphisms of cohomology rings.
    - Easier creation of a cohomology ring from a tower of subgroups.
    - Kernels and preimage representatives of induced maps.
    - Stop hard-coding MTXLIB environment variable.

  * v3.1 (December 2018):

    - Hilbert series computation by using a new implementation in SageMath.
    - Vastly improved computation of filter degree type (now relying on Hilbert series).
    - Use libgap instead of the GAP pexpect interface.
    - Sub-package upgrade: modres-1.1

  * v3.0.1 (August 2018):

    - Add a routine to compute filter regular parameters in small degrees by enumeration.
    - More self-consistency checks.
    - A routine to compute a cohomology ring from a tower of subgroups.

  * v3.0 (February 2018):

    - Turn the cohomology package into a "new style spkg". It is split into several smaller parts that are either using an autotoolized build system or are pip installable.
    - Replace the old custom test and doc-build scripts by standard tools.

  * v2.1.5 (Mai 2015):

    - Improved computation of the nil-radical, including a degree-wise computation.
    - Methods is_nilpotent and nilpotency_degree for cohomology ring elements.
    - Various improvements for the computation of depth and filter degree type.

  * v2.1.4 (April 2013):

    - Consequently compute parameters for the *complete* cohomology ring rather than only for the ring approximation.
    - Improved heuristics to speed-up computations.
    - Better portability.
    - Improved logging.

  * v2.1.3 (July 2012):

    - Improved heuristics to choose between Hilbert-Poincaré and Symonds criteria, and to deal with lower bounds for the depth.
    - Allow storing of "permanent results" that are indexed in terms of data in Gap.
    - Switch to a new location for the public web repository.

  * v2.1.2 (March 2012):

    - Use Sage's coercion model more properly.
    - Build the documentation locally.

  * v2.1.1 (September 2010):

    - Make it so that write permission in ``SAGE_DATA`` are only needed during installation of the package, but not for using it.
    - Restructuring the code.

  * v2.1 (September 2010):

    - Support for big endian machines.
    - 100% doctest coverage, parallel testing.
    - New: Essential and depth essential ideals, kernels and preimages of induced homomorphisms.
    - Improved completion tests.

  * v2.0 (April 2010):

    - Modular cohomology rings for arbitrary finite groups (not just prime power groups).
    - Improved portability.

  * v1.2.p0 (March 2010):

    - Improved test for the presence of the Small Groups library (thanks to Dima Pasechnik).

  * v1.2 (October 2009):

    - Minor bug fixes and code improvements.
    - Persistent Group Cohomology (bar codes), based on ideas of Graham Ellis and Simon King.

  * v1.1 (August 2009):

    - Yoneda cocomplex.
    - Restricted Massey powers and general Massey products.

  * v1.0.2 (July 2009):

    - Minor fixes to prevent a regression.

  * v1.0.1 (July 2009):

    - First public version in GPL 2 or later

Licence
-------

This document and our data bases of cohomology rings are licensed under a
`Creative Commons Attribution-Share Alike 3.0 License`__.

__ http://creativecommons.org/licenses/by-sa/3.0/

The code of our package is licensed under the GNU General Public License
(`GPL`__) version 2 or later, at your choice.

__ http://www.gnu.org/licenses/

AUTHORS:

- Simon King <simon.king@uni-jena.de>
- David Green <david.green@uni-jena.de>

Table of Contents
-----------------

.. toctree::
   :maxdepth: 2

   pGroupCohomology
   factory
   cohomology
   modular_cohomology
   barcode
   cochain
   resolution
   dickson
   auxiliaries

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`

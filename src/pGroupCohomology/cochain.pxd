#*****************************************************************************
#
#    Cohomology Ring Elements and Maps
#
#    Copyright (C) 2009 Simon A. King <simon.king@uni-jena.de>
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

# to be defined below
cdef class COCH
cdef class ChMap
cdef class YCOCH

from pGroupCohomology.mtx cimport FEL, PTR, matrix_t, size_t, matmulF, tmultinv, zitof, zadvance, zsteprow, ptrPlus, matfree, matdup, MTX
from pGroupCohomology.resolution cimport RESL
from sage.structure.element import RingElement, ModuleElement
from sage.structure.element cimport RingElement, ModuleElement
from sage.rings.morphism cimport RingHomomorphism

cdef extern from "meataxe.h":
    size_t zsize(long nrows)
    int zsetlen(long ncols)
    int zsetfield(long field)
    PTR zalloc(long nrows)
    void zfree(PTR p)
    PTR zaddmulrow(PTR dest, PTR src, FEL f)
    PTR zaddrow(PTR dest, PTR src)
    PTR zmaprow(PTR row, PTR matrix, long nor, PTR result)
    matrix_t *matadd(matrix_t *dest, matrix_t *src)
        
###########################################################
## p-Gruppen
###########################################################

cdef extern from "pgroup.h":
    ctypedef int boolean
    ctypedef long yesno
    cdef extern yesno yes
    cdef extern yesno no
    cdef extern yesno unknown
    ctypedef struct path_t:
        long index
        char *path
        path_t **child
        path_t *parent
        long lastArrow
        long depth       #/* depth of node in tree, i.e. length of path */
        long dim         # /* Dimension of path, for Jennings case */
    ctypedef struct group_t:
        char *stem
        long arrows
        long nontips
        long maxlength
        long mintips
        long p
        char ordering
        char **nontip
        path_t *root
        path_t *lroot
        matrix_t **action
        matrix_t **laction
        matrix_t **bch
        long *dim
        long *dS          # /* depth Steps: for resolution only */

###############################################################
## Funktionsprototypen fuer Gruppen
cdef extern from "pgroup_decls.h":
    #PTR ptrPlus(PTR base, long offset)
    group_t *fullyLoadedGroupRecord(char *stem)
    group_t *newGroupRecord ()
    group_t *namedGroupRecord(char *stem)
    void freeGroupRecord (group_t *group)
    void readHeader(group_t *group)
    void loadNonTips(group_t *group)
    void loadActionMatrices(group_t *group)
    void loadLeftActionMatrices(group_t *group)
    path_t *allocatePathTree(group_t *group)
    void buildPathTree(group_t *group)
    void buildLeftPathTree(group_t *group)

    matrix_t *rightActionMatrix(group_t *group, PTR vec)
    matrix_t *leftActionMatrix(group_t *group, PTR vec)
    void innerRightActionMatrix(group_t *group, PTR vec, PTR dest)
    void innerLeftActionMatrix(group_t *group, PTR vec, PTR dest)
    void innerRightCompose(group_t *group, PTR alpha, PTR beta, \
                                long s, long r, long q, PTR scratch, PTR gamma)

    int verifyGroupIsAbelian(group_t *A)


###############################################################
## Berechnung von Aufloesungen:
## 1. Typen
##

cdef extern from "aufloesung.h":
    ctypedef struct resol_t:
        group_t *group
        char *stem
        char *moduleStem
        long numproj
        long numproj_alloc
        long *projrank    #/* projrank[n] = free rank of nth projective */
        long *Imdim       #/* Imdim[n] = dim of Im d_n (which is a submod of P_{n-1}) */

cdef extern from "nDiag.h":
    ctypedef struct gV_t: # general vector
        PTR w
        FEL coeff
        long dim
        long len
        long block
        long col
        boolean radical

    ctypedef struct uV_t: # unreduced vector
        gV_t *gv
        long index
        uV_t *prev
        uV_t *next

    ctypedef struct modW_t

    ctypedef struct rV_t: # reduced vector
        gV_t *gv
        modW_t *node
        rV_t *next
        rV_t *prev
        long expDim

    ctypedef struct modW_t:
        modW_t *parent
        modW_t **child
        rV_t *divisor
        long qi   #  /* index of quotient path */
        long status

    ctypedef struct ngs_t: # newCommonGeneratingSet
        long r, s # /* r is rank of ambient free, s rank of preimage (0 for fgs) */
        rV_t *firstReduced
        rV_t *lastReduced
        uV_t *unreducedHeap
        modW_t **proot
        gV_t *gVwaiting
        long pnontips # /* present guess at the number of nontips */
        long expDim
        long targetRank
        long latestStatusChatter
        long dimLoaded
        long blockLoaded
        long nops # /* number of products */
        PTR thisBlock
        PTR w
        PTR theseProds
        long blockSize
        # char stem[MAXLINE]
        char stem[120]
        long prev_pnon, unfruitful

    ctypedef struct nFgs_t: # newFlaggedGeneratingSet
        boolean finished
        boolean nRgsUnfinished
        ngs_t *ngs
        long max_unfruitful

    ctypedef struct nRgs_t: # newResentfulGeneratingSet
        nFgs_t *ker # /* ker is the hgs for the known part of kernel */
        ngs_t *ngs
        long prev_ker_pnon, overshoot


###############################################################
## Berechnung von Aufloesungen:
## 2. Funktionen
##
cdef extern from "aufloesung_decls.h":
    cdef char *differentialFile(resol_t *resol, long n)
    # /* String returned must be used at once, never reused, never freed. */
    # /* Represents d_n : P_n -> P_{n-1} */
    cdef char *urbildGBFile(resol_t *resol, long n)
    # /* String returned must be used at once, never reused, never freed. */
    # /* Represents urbild Groebner basis for d_n : P_n -> P_{n-1} */
    cdef char *resolStem(long Gsize, char *Gname)
    # /* String returned must be used at once, never reused, never freed. */
    cdef char *resolDir(long Gsize)
    # /* String returned must be used at once, never reused, never freed. */

    cdef nRgs_t *nRgsStandardSetup(resol_t *resol, long n, PTR mat)
    # /* mat should be a block of length rankProj(resol, n-1) x rankProj(resol, n) */

    cdef resol_t *newResolutionRecord()
    cdef resol_t *newResolWithGroupLoaded (char *RStem, char *GStem, long N)
    cdef void freeResolutionRecord(resol_t *resol)

    ## diese zwei Funktionen geben nur Teile von resol_t zurück
    # cdef long rankProj(resol_t *resol, long n)
    # cdef long dimIm(resol_t *resol, long n)
    cdef void setRankProj(resol_t *resol, long n, long r)
    cdef void setRankProjCoverForModule(resol_t *resol, long rkP0, long dimM)

    ## dies mache ich lieber von Sage aus...
    #cdef void initializeDateCommand(char *stem)
    #void chatterDate()
    #cdef char *numberedFile(long n, char *stem, char *ext)
    # /* String returned must be used at once, never reused, never freed. */
    # /* extension WITHOUT dot */

    cdef matrix_t *makeFirstDifferential(resol_t *resol)
    cdef void makeThisDifferential(resol_t *resol, long n)
    # /* n must be at least two */
    cdef nRgs_t *loadDifferential(resol_t *resol, long n)
    cdef nRgs_t *loadUrbildGroebnerBasis(resol_t *resol, long n)

    cdef void readKnownResolution(resol_t *resol, long N)

    cdef void innerPreimages(nRgs_t *nRgs, PTR images, long noi, group_t *group, PTR preimages)
    # /* PTR preimages(nRgs_t *nRgs, PTR images, long noi, group_t *group); */

    cdef void readOrConstructThisProjective(resol_t *resol, long n)
    cdef void ensureThisProjectiveKnown(resol_t *resol, long n)
    cdef void ensureThisUrbildGBKnown(resol_t *resol, long n)


#####################################################################
## Urbilder / Urbild-GB
cdef extern from "urbild_decls.h":
    void freeNRgs(nRgs_t *nRgs)
    void saveUrbildGroebnerBasis(nRgs_t *nRgs, char *outfile, group_t *group)
    #long countGenerators(nFgs_t *nFgs)
    long numberOfHeadyVectors(ngs_t *ngs)
    void saveMinimalGenerators(nFgs_t *nFgs, char *outfile, group_t *group)
    matrix_t *getMinimalGenerators(nFgs_t *nFgs, group_t *group)

cdef extern from "nBuchberger_decls.h":
    void nRgsBuchberger(nRgs_t *nRgs, group_t *group)

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

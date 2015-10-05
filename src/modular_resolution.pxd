#*****************************************************************************
#       Copyright (C) 2015 Simon King <simon.king@uni-koeln.de>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.libs.meataxe cimport *

###########################################################
## p-groups
###########################################################
cdef extern from "modular_resolution/pgroup.h":
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
        Matrix_t **action
        Matrix_t **laction
        Matrix_t **bch
        long *dim
        long *dS          # /* depth Steps: for resolution only */

###############################################################
## function prototypes for p-groups
cdef extern from "modular_resolution/pgroup_decls.h":
    #PTR FfGetPtr(PTR base, long offset)
    group_t *fullyLoadedGroupRecord(char *stem) except NULL
    group_t *newGroupRecord () except NULL
    group_t *namedGroupRecord(char *stem) except NULL
    void freeGroupRecord (group_t *group)
    int readHeader(group_t *group) except 1
    int loadNonTips(group_t *group) except 1
    int loadActionMatrices(group_t *group) except 1
    int loadLeftActionMatrices(group_t *group) except 1
    path_t *allocatePathTree(group_t *group) except NULL
    int buildPathTree(group_t *group) except 1
    int buildLeftPathTree(group_t *group) except 1

    Matrix_t *rightActionMatrix(group_t *group, PTR vec)
    Matrix_t *leftActionMatrix(group_t *group, PTR vec)
    void innerRightActionMatrix(group_t *group, PTR vec, PTR dest)
    void innerLeftActionMatrix(group_t *group, PTR vec, PTR dest)
    void innerRightCompose(group_t *group, PTR alpha, PTR beta, \
                                long s, long r, long q, PTR scratch, PTR gamma)

    int verifyGroupIsAbelian(group_t *A) except -1


###############################################################
## Resolutions
cdef extern from "modular_resolution/modular_resolution.h":
    ctypedef struct resol_t:
        group_t *group
        char *stem
        char *moduleStem
        long numproj
        long numproj_alloc
        long *projrank    #/* projrank[n] = free rank of nth projective */
        long *Imdim       #/* Imdim[n] = dim of Im d_n (which is a submod of P_{n-1}) */

    cdef char *differentialFile(resol_t *resol, long n)
    # /* String returned must be used at once, never reused, never freed. */
    # /* Represents d_n : P_n -> P_{n-1} */
    cdef char *urbildGBFile(resol_t *resol, long n)
    # /* String returned must be used at once, never reused, never freed. */
    # /* Represents urbild Groebner basis for d_n : P_n -> P_{n-1} */

    cdef nRgs_t *nRgsStandardSetup(resol_t *resol, long n, PTR mat) except NULL
    # /* mat should be a block of length rankProj(resol, n-1) x rankProj(resol, n) */

    cdef resol_t *newResolWithGroupLoaded (char *RStem, char *GStem, long N) except NULL
    cdef void freeResolutionRecord(resol_t *resol)

    cdef long dimIm(resol_t *resol, long n) except -1
    cdef int setRankProj(resol_t *resol, long n, long r) except 1

    cdef Matrix_t *makeFirstDifferential(resol_t *resol) except NULL
    cdef nRgs_t *loadUrbildGroebnerBasis(resol_t *resol, long n)

    cdef int innerPreimages(nRgs_t *nRgs, PTR images, long noi, group_t *group, PTR preimages) except 1
    # /* PTR preimages(nRgs_t *nRgs, PTR images, long noi, group_t *group); */

cdef extern from "modular_resolution/nDiag.h":
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


#####################################################################
## preimages / "urbild Groebner basis"
cdef extern from "modular_resolution/urbild_decls.h":
    void freeNRgs(nRgs_t *nRgs)
    int saveUrbildGroebnerBasis(nRgs_t *nRgs, char *outfile, group_t *group) except 1
    #long countGenerators(nFgs_t *nFgs)
    long numberOfHeadyVectors(ngs_t *ngs)
    int saveMinimalGenerators(nFgs_t *nFgs, char *outfile, group_t *group) except 1
    Matrix_t *getMinimalGenerators(nFgs_t *nFgs, group_t *group)

cdef extern from "modular_resolution/nBuchberger_decls.h":
    int nRgsBuchberger(nRgs_t *nRgs, group_t *group) except 1


# -----> Shared library
lib_LIBRARIES               = libmodres.a
libmodres_a_SOURCES         = pincl.c pgroup.c aufloesung.c

# -----> Headers
pkginclude_HEADERS          = modular_resolution.h pgroup.h pgroup_decls.h\
                              nDiag.h urbild_decls.h nBuchberger_decls.h
dist_noinst_HEADERS         = aufloesung_decls.h aufnahme_decls.h pcommon.h\
                              pincl_decls.h pincl.h pmatrix_decls.h slice_decls.h

# -----> Executable (built from the shared library)
bin_PROGRAMS = makeActionMatrices makeNontips groupInfo perm2Gap makeInclusionMatrix
makeActionMatrices_SOURCES  = mam.c
makeActionMatrices_LDADD    = $(lib_LIBRARIES)
makeNontips_SOURCES         = mnt.c
dist_noinst_DATA            = test.reg
makeNontips_LDADD           = $(lib_LIBRARIES)
groupInfo_SOURCES           = gi.c
groupInfo_LDADD             = $(lib_LIBRARIES)
perm2Gap_SOURCES            = perm2Gap.c
perm2Gap_LDADD              = $(lib_LIBRARIES)
makeInclusionMatrix_SOURCES = mim.c
makeInclusionMatrix_LDADD   = $(lib_LIBRARIES)

# -----> A simple check
check_SCRIPTS               = mnttest.sh
TESTS                       = $(check_SCRIPTS)

mnttest.sh: test.reg
	test -r ./test.reg || cp $(srcdir)/test.reg .
	@echo './makeNontips -O RLL 2 test && groupInfo test | grep -Fxq "Size of Groebner basis: 3"' > mnttest.sh
	@chmod +x mnttest.sh

CLEANFILES                  = mnttest.sh test.reg test.nontips

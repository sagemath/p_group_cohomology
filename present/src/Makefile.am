#~     This file is part of p_group_cohomology.

#~     p_group_cohomoloy is free software: you can redistribute it and/or modify
#~     it under the terms of the GNU General Public License as published by
#~     the Free Software Foundation, either version 2 of the License, or
#~     (at your option) any later version.

#~     p_group_cohomoloy is distributed in the hope that it will be useful,
#~     but WITHOUT ANY WARRANTY; without even the implied warranty of
#~     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#~     GNU General Public License for more details.

#~     You should have received a copy of the GNU General Public License
#~     along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.

# -----> Shared library
lib_LTLIBRARIES              = libmodres.la
libmodres_la_SOURCES         = aufloesung.c aufnahme.c fileplus.c nBuchberger.c pgroup.c pincl.c slice.c urbild.c

# -----> Headers
pkginclude_HEADERS          = fileplus.h fp_decls.h modular_resolution.h pgroup.h pgroup_decls.h\
                              nDiag.h urbild_decls.h nBuchberger_decls.h\
                              pcommon.h slice_decls.h
dist_noinst_HEADERS         = aufloesung_decls.h aufnahme.h pincl_decls.h pincl.h

# -----> Executable (built from the shared library)
bin_PROGRAMS = makeActionMatrices makeNontips groupInfo perm2Gap makeInclusionMatrix
makeActionMatrices_SOURCES  = mam.c
makeActionMatrices_LDADD    = $(lib_LTLIBRARIES)
makeNontips_SOURCES         = mnt.c
dist_noinst_DATA            = test.reg
makeNontips_LDADD           = $(lib_LTLIBRARIES)
groupInfo_SOURCES           = gi.c
groupInfo_LDADD             = $(lib_LTLIBRARIES)
perm2Gap_SOURCES            = perm2Gap.c
perm2Gap_LDADD              = $(lib_LTLIBRARIES)
makeInclusionMatrix_SOURCES = mim.c
makeInclusionMatrix_LDADD   = $(lib_LTLIBRARIES)

# -----> A simple check
check_SCRIPTS               = mnttest.sh
TESTS                       = $(check_SCRIPTS)

mnttest.sh: test.reg
	test -r ./test.reg || cp $(srcdir)/test.reg .
	@echo './makeNontips -O RLL 2 test && groupInfo test | grep -Fxq "Size of Groebner basis: 3"' > mnttest.sh
	@chmod +x mnttest.sh

CLEANFILES                  = mnttest.sh test.nontips

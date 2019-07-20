#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

#~ Copyright 2018: Simon King <simon.king@uni-jena.de>
#
#~     This file is part of p_group_cohomology.
#
#~     p_group_cohomoloy is free software: you can redistribute it and/or modify
#~     it under the terms of the GNU General Public License as published by
#~     the Free Software Foundation, either version 2 of the License, or
#~     (at your option) any later version.
#
#~     p_group_cohomoloy is distributed in the hope that it will be useful,
#~     but WITHOUT ANY WARRANTY; without even the implied warranty of
#~     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#~     GNU General Public License for more details.
#
#~     You should have received a copy of the GNU General Public License
#~     along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.

AC_PREREQ([2.69])
AC_INIT([modular_resolution], [1.1], [simon.king@uni-jena.de])
AM_INIT_AUTOMAKE([check-news dist-bzip2 -Wall])
AM_PROG_AR
LT_INIT([disable-static])
AC_CONFIG_SRCDIR([src/modular_resolution.h])
AC_CONFIG_HEADERS([config.h])
AC_CONFIG_MACRO_DIR([m4])

# Checks for programs.
AC_PROG_CC
AM_PROG_CC_C_O
AC_PROG_INSTALL

# Checks for libraries.
AC_SEARCH_LIBS([MtxError], [mtx])

# Checks for header files.
AC_CHECK_HEADERS([stdlib.h string.h unistd.h meataxe.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_CHECK_HEADER_STDBOOL
AC_C_INLINE
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_MALLOC

AC_CONFIG_FILES([Makefile src/Makefile])
AC_OUTPUT

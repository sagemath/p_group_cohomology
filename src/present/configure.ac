#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])
AC_INIT([modular_resolution], [1.0], [simon.king@uni-koeln.de])
AM_INIT_AUTOMAKE([check-news dist-bzip2 -Wall])
AM_PROG_AR
LT_INIT
AC_CONFIG_SRCDIR([src/modular_resolution.h])
AC_CONFIG_HEADERS([config.h])

# Checks for programs.
AC_PROG_CC
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

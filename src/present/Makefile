#*****************************************************************************
#         Makefile for David Green's programs for constructing
#            minimal free resolutions for finite p-groups
#
#       Copyright (C) 2009 Simon A. King <simon.king@uni-jena.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
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

#########################################################################
## Usage:
## > cd LocalDirectory/bin
## > make ROOTDIR=/path/to/package/directory -f /path/to/Makefile
## This results in installing the executables in LocalDirectory/bin/
#########################################################################
# Use GNU make
# SHELL=/bin/sh
# VPATH=../src

############## Configuration options here ###############################

# The directory of Simon King's Sage-package src directory
# This will usually be given to make by ROOTDIR=path/to/package
ROOTDIR=$(PWD)

# Standard path to this makefile
ODIR=$(ROOTDIR)/present

# The target directory for executables
TDIR=$(PWD)

# The directory in which source files will be found
VPATH=$(ODIR)/src

# MeatAxe source directory
MTXSRC=$(ROOTDIR)/mtx2.2.4/src/

# MeatAxe library directory
MTXLIBDIR=$(ROOTDIR)/lib

MTXLIBNAME=mtx
# Name of MeatAxe library to use.  Usually just "mtx", meaning that the
# library has filename  "libmtx.a"

# In order to deal with build problems on Intel Mac, we defined
# the variable DARWIN64 in spkg-install
CFLAGS=-I$(MTXSRC) -Wall $(OO) -g -fPIC $(DARWIN64)
#original: CFLAGS=-I$(MTXSRC) -Wall
LFLAGS=-L$(MTXLIBDIR) $(DARWIN64)
LFLAGS2=-l$(MTXLIBNAME) $(DARWIN64)
# Insert options to taste

# CC=gcc
# Comment out if you don't have gcc
############## End of configuration options ###########################

common=pgroup.o perror.o
top_level=mam.o wgb.o mnt.o gi.o perm2Gap.o mim.o matmag.o
objects=$(common) $(top_level) pincl.o
executables=makeActionMatrices writeGroebnerBasis makeNontips groupInfo perm2Gap makeInclusionMatrix matmag

all: $(executables)

makeActionMatrices: mam.o $(common)
	$(CC) $(LFLAGS) -o makeActionMatrices mam.o $(common) $(LFLAGS2)

writeGroebnerBasis: wgb.o $(common)
	$(CC) $(LFLAGS) -o writeGroebnerBasis wgb.o $(common) $(LFLAGS2)

makeNontips: mnt.o $(common)
	$(CC) $(LFLAGS) -o makeNontips mnt.o $(common) $(LFLAGS2)
	echo "Testing makeNontips"
	$(ROOTDIR)/bin/maketab 2
	./makeNontips -ORLL 2 $(VPATH)/test

groupInfo: gi.o $(common)
	$(CC) $(LFLAGS) -o groupInfo gi.o $(common) $(LFLAGS2)

perm2Gap: perm2Gap.o $(common)
	$(CC) $(LFLAGS) -o perm2Gap perm2Gap.o $(common) $(LFLAGS2)

matmag: matmag.o $(common)
	$(CC) $(LFLAGS) -o matmag matmag.o $(common) $(LFLAGS2)

makeInclusionMatrix: mim.o $(common) pincl.o
	$(CC) $(LFLAGS) -o makeInclusionMatrix mim.o $(common) pincl.o $(LFLAGS2)

$(top_level): pgroup.h pgroup_decls.h
mim.o: pincl_decls.h
mim.o pincl.o: pincl.h
pgroup.o: pgroup.h

$(objects): pcommon.h perror_decls.h

delete:
	-$(RM) $(objects) $(executables)
clean:
	-$(RM) $(objects)

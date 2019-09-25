#!/bin/sh
# create a distribution of p_group_cohomology.
# Requested argument: The folder with the sources.
# To be executed from within a Sage shell

# Source folder
SRC=$1
# Create the distribution in a sub-directory of the current directory
VERSION=`cat $SRC/downstream/package-version.txt`
DIST_DIR=$(pwd)/p_group_cohomology-$VERSION
mkdir -p $DIST_DIR
cd $SRC
cp INSTALL $DIST_DIR/

## The python/cython modules
# The following creates a .tar.gz-file, which is actually not what we want.
# So, we unpack it in the end.
cd src
sage -python setup.py sdist --dist-dir $DIST_DIR
cd $DIST_DIR
tar -xzf pGroupCohomology-$VERSION.tar.gz
rm pGroupCohomology-$VERSION.tar.gz
cp pGroupCohomology-$VERSION/README pGroupCohomology-$VERSION/COPYING .

## The C library
$SRC/present/configure --prefix=$DIST_DIR
$MAKE distdir
$MAKE distclean
rm -r src

## The distribution
cd ..
tar cf - p_group_cohomology-$VERSION | xz -z -e - > p_group_cohomology-$VERSION.tar.xz

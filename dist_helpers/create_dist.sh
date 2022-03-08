#!/bin/sh
# create a distribution of p_group_cohomology.
# Requested argument: The folder with the sources.
# To be executed from within a Sage shell

# Create the distribution in a sub-directory of the current directory
VERSION=3.3.3
DIST_DIR=$(pwd)/p_group_cohomology-$VERSION
mkdir -p $DIST_DIR

## Copying the parts that do not require compilation
cp INSTALL $DIST_DIR/
cp -r test_data $DIST_DIR/
cp -r gap_helper $DIST_DIR/
cp -r singular_helper $DIST_DIR/

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
cd $DIST_DIR/../present
autoreconf -ivf
./configure --prefix=$DIST_DIR
$MAKE distdir
$MAKE distclean
# rm -r src

## The distribution
cd $DIST_DIR/..
tar cf - p_group_cohomology-$VERSION | xz -z -e - > p_group_cohomology-$VERSION.tar.xz

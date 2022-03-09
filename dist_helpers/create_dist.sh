#!/bin/sh
# create a distribution of p_group_cohomology.

# Create the distribution in a sub-directory of the current directory
git clean -fdx
VERSION=3.3.3
DIST_DIR=$(pwd)/p_group_cohomology-$VERSION

## The python/cython modules
# The following creates a .tar.gz-file, which is actually not what we want.
# So, we unpack it in the end.
cd src
sage --python setup.py sdist --dist-dir $DIST_DIR
cd $DIST_DIR
tar xf pGroupCohomology-$VERSION.tar.gz
rm pGroupCohomology-$VERSION.tar.gz
cp pGroupCohomology-$VERSION/README pGroupCohomology-$VERSION/COPYING .

cd ..
## Copying the parts that do not require compilation
cp INSTALL $DIST_DIR/
cp -r test_data $DIST_DIR/
cp -r gap_helper $DIST_DIR/
cp -r singular_helper $DIST_DIR/

## The distribution
tar cf - p_group_cohomology-$VERSION | xz -z -e - > p_group_cohomology-$VERSION.tar.xz

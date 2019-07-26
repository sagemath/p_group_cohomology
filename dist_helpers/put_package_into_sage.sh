#!/bin/sh
# Make it so that p_group_cohomology can be installed with sage -i p_group_cohomology.
# The source ball must be in the current directory.
# Required argument: The source folder, as it also contains the
# latest versions of spkg-install etc.
# The script must be executed in a sage shell.

SRC=$1
VERSION=`cat $SRC/downstream/package-version.txt`

cp p_group_cohomology-$VERSION.tar.xz $SAGE_ROOT/upstream/
cp $SRC/downstream/* $SAGE_ROOT/build/pkgs/p_group_cohomology/
sage --package fix-checksum

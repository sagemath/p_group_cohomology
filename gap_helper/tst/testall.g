#
# p_group_cohomology_helper: GAP helper for p_group_cohomology SageMath package
#
# This file runs package tests. It is also referenced in the package
# metadata in PackageInfo.g.
#
LoadPackage( "p_group_cohomology_helper" );

TestDirectory(DirectoriesPackageLibrary( "p_group_cohomology_helper", "tst" ),
  rec(exitGAP := true));

FORCE_QUIT_GAP(1); # if we ever get here, there was an error

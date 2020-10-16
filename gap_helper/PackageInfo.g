#
# p_group_cohomology_helper: GAP helper for p_group_cohomology SageMath package
#
# This file contains package meta data. For additional information on
# the meaning and correct usage of these fields, please consult the
# manual of the "Example" package as well as the comments in its
# PackageInfo.g file.
#
SetPackageInfo( rec(

PackageName := "p_group_cohomology_helper",
Subtitle := "GAP helper for p_group_cohomology SageMath package",
Version := "0.1",
Date := "16/10/2020", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
    FirstNames := "Simon",
    LastName := "King",
    WWWHome := "https://users.fmi.uni-jena.de/~king/index.html",
    Email := "simon dot king at uni hyphen jena dot de",
    IsAuthor := true,
    IsMaintainer := true,
    PostalAddress := "07737 Jena",
    Place := "Jena",
    Institution := "Friedrich-Schiller-Universität Jena",
  ),
],

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/simon-king-jena/p_group_cohomology_helper"
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := "https://github.com/simon-king-jena/p_group_cohomology_helper/",
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),

ArchiveFormats := ".tar.gz",

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "submitted"     for packages submitted for the refereeing
##    "deposited"     for packages for which the GAP developers agreed
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages
##    "other"         for all other packages
##
Status := "dev",

AbstractHTML   :=  "",

PackageDoc := rec(
  BookName  := "p_group_cohomology_helper",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "GAP helper for p_group_cohomology SageMath package",
),

Dependencies := rec(
  GAP := ">= 4.10",
  NeededOtherPackages := [ ],
  SuggestedOtherPackages := [ ],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

#Keywords := [ "TODO" ],

));



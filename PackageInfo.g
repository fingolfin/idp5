#############################################################################
##
##  PackageInfo.g                                           Idp5 package
##
##  Idp5: Identification of the groups of order dividing p^5
##
SetPackageInfo( rec(

PackageName := "Idp5",
Subtitle := "Identification of the groups of order dividing p^5",
Version := "1.0.0",
Date := "08/11/2026", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
    FirstNames := "Heiko",
    LastName := "Dietrich",
    WWWHome := "http://users.monash.edu.au/~heikod/",
    Email := "heiko.dietrich@monash.edu",
    IsAuthor := true,
    IsMaintainer := true,
    Place := "Melbourne, Australia",
    Institution := "Monash University",
  ),
  rec(
    FirstNames := "Bettina",
    LastName := "Eick",
    WWWHome := "http://www.iaa.tu-bs.de/beick",
    Email := "beick@tu-bs.de",
    IsAuthor := true,
    IsMaintainer := false,
    Place := "Braunschweig, Germany",
    Institution := "TU Braunschweig",
  ),
  rec(
    FirstNames := "Henrik",
    LastName := "Schanze",
    WWWHome := "https://www.iaa.tu-bs.de/henschan",
    Email := "henrik.schanze@tu-braunschweig.de",
    IsAuthor := true,
    IsMaintainer := false,
    Place := "Braunschweig, Germany",
    Institution := "TU Braunschweig",
  ),
],

# TODO: create the GitHub repository (and its GitHub Pages site) before
# submitting the package; GAP's package distribution reads PackageInfoURL.
SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/heikodietrich/idp5",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := "https://heikodietrich.github.io/idp5/",
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/idp5-", ~.Version ),

ArchiveFormats := ".tar.gz",

AbstractHTML :=
  "The <span class=\"pkgname\">Idp5</span> package identifies the groups of \
order dividing p<sup>5</sup>, for any prime p, with the groups in the \
SmallGroups library, and constructs isomorphisms onto the library groups.",

PackageDoc := rec(
  BookName  := "Idp5",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Identification of the groups of order dividing p^5",
),

Dependencies := rec(
  GAP := ">= 4.14",
  NeededOtherPackages := [ [ "smallgrp", ">= 1.5" ] ],
  SuggestedOtherPackages := [ [ "autpgrp", ">= 1.10" ] ],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

Keywords := [ "group identification", "IdGroup", "IdSmallGroup",
              "p-groups", "groups of order p^5", "small groups library",
              "isomorphism" ],

AutoDoc := rec(
  TitlePage := rec(
    Copyright := """
&#169; 2026 by Heiko Dietrich, Bettina Eick, and Henrik Schanze.
<P/>
The &Idp5; package is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 2 of the License, or (at your
option) any later version.
""",
    Abstract := """
The &Idp5; package identifies the groups of order dividing <M>p^5</M>, for
any prime <M>p</M>, with the groups in the SmallGroups library, and
constructs isomorphisms onto the library groups.
""",
  ),
),

));

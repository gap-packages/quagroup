#############################################################################
##  
##  PkgInfo file for the package QuaGroup               Willem de Graaf
##  

SetPackageInfo( rec(
PackageName := "QuaGroup",
Subtitle := "Computations with quantum groups",        
Version := "1.8.4",
Date := "11/01/2024", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
  LastName := "de Graaf",
  FirstNames := "Willem Adriaan",
  IsAuthor := true,
  IsMaintainer := true,
  Email := "degraaf@science.unitn.it",
  WWWHome := "http://www.science.unitn.it/~degraaf",
  Place := "Trento",
  Institution := "Dipartimento di Matematica"
  ),
  rec(
    LastName      := "GAP Team",
    FirstNames    := "The",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "support@gap-system.org",
  ),
],
Status := "accepted",
CommunicatedBy := "Gerhard Hiss (Aachen)",
AcceptDate := "10/2003",

PackageWWWHome  := "https://gap-packages.github.io/quagroup/",
README_URL      := Concatenation( ~.PackageWWWHome, "README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "PackageInfo.g" ),
SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/gap-packages/quagroup",
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/quagroup-", ~.Version ),
ArchiveFormats := ".tar.gz",

AbstractHTML := "The package <span class=\"pkgname\">QuaGroup</span> contains \
                 functionality for working with quantized enveloping algebras\
                 of finite-dimensional semisimple Lie algebras.",

PackageDoc := rec(
  BookName := "QuaGroup",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile := "doc/manual.pdf",
  SixFile := "doc/manual.six",
  LongTitle := "Computations with quantum groups",
  Autoload := true
  ),
Dependencies := rec(
  GAP := ">=4.8",
  NeededOtherPackages:= [ ],                 
  SuggestedOtherPackages := [ ],
  ExternalConditions := []
),
AvailabilityTest := ReturnTrue,

# the banner
BannerString := Concatenation(
"     |                                                                 \n",
"     |          QuaGroup ", ~.Version, "\n",
"     |                                                                 \n",
"-----------     A package for dealing with quantized enveloping algebras\n",
"     |                                                                 \n",
"     |          Willem de Graaf                                        \n",
"     |          degraaf@science.unitn.it                               \n\n"
),
Keywords := ["quantum groups"],

TestFile := "tst/testall.g",

AutoDoc := rec(
    TitlePage := rec(
        Version := Concatenation( "Version ", ~.Version ),
        Copyright := "&copyright; 2002 Willem A. de Graaf",
    ),
),

));



#############################################################################
##  
##  PkgInfo file for the package QuaGroup               Willem de Graaf
##  

SetPackageInfo( rec(
PackageName := "QuaGroup",
Subtitle := "Computations with quantum groups",        
Version := "1.8",
Date := "16/08/2013", # this is in dd/mm/yyyy format

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
  )
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

PackageDoc := [rec(
  BookName := "QuaGroup",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile := "doc/manual.pdf",
  SixFile := "doc/manual.six",
  LongTitle := "Computations with quantum groups",
  Autoload := true
  )],
Dependencies := rec(
  GAP := ">=4.3",
  NeededOtherPackages:= [ ],                 
  SuggestedOtherPackages := [ ["GAPDoc", ">= 0.99"] ],
  ExternalConditions := []
),
AvailabilityTest := ReturnTrue,
Autoload := false,

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

AutoDoc := rec(
    TitlePage := rec(
        Version := Concatenation( "Version ", ~.Version ),
        Copyright := "&copyright; 2002 Willem A. de Graaf",
    ),
),

));



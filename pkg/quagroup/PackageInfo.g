#############################################################################
##  
##  PkgInfo file for the package QuaGroup               Willem de Graaf
##  

SetPackageInfo( rec(
PackageName := "QuaGroup",
Subtitle := "a package for doing computations with quantum groups",        
Version := "1.8",
Date := "16/08/2013",
ArchiveURL := Concatenation("http://www.science.unitn.it/~degraaf/quagroup-",
                            ~.Version),
ArchiveFormats := ".tar.gz",
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
README_URL := 
  "http://www.science.unitn.it/~degraaf/README.quagroup",
PackageInfoURL := 
  "http://www.science.unitn.it/~degraaf/PackageInfo.g",
AbstractHTML := "The package <span class=\"pkgname\">QuaGroup</span> contains \
                 functionality for working with quantized enveloping algebras\
                 of finite-dimensional semisimple Lie algebras.",
PackageWWWHome := "http://www.science.unitn.it/~degraaf/quagroup.html",
PackageDoc := [rec(
  BookName := "QuaGroup",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile := "doc/manual.pdf",
  SixFile := "doc/manual.six",
  LongTitle := "a package for doing computations with quantum groups",
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
"     |          QuaGroup                                               \n",
"     |                                                                 \n",
"-----------     A package for dealing with quantized enveloping algebras\n",
"     |                                                                 \n",
"     |          Willem de Graaf                                        \n",
"     |          degraaf@science.unitn.it                               \n\n"
),
Keywords := ["quantum groups"]
));



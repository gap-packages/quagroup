#############################################################################
##  
##  PkgInfo file for the package QuaGroup               Willem de Graaf
##  

SetPackageInfo( rec(
PackageName := "QuaGroup",
Subtitle := "a package for doing computations with quantum groups",        
Version := "1.1",
Date := "01/04/2003",
ArchiveURL := "http://www-circa.mcs.st-and.ac.uk/~wdg/quagroup-1.1",
ArchiveFormats := ".tar.gz",
Persons := [
  rec(
  LastName := "de Graaf",
  FirstNames := "Willem Adriaan",
  IsAuthor := true,
  IsMaintainer := true,
  Email := "quagroup@hetnet.nl",
  WWWHome := "http://www-circa.mcs.st-and.ac.uk/~wdg",
  Place := "Utrecht",
  Institution := ""
  )
],
Status := "accepted",
CommunicatedBy := "Gerhard Hiss",
AcceptDate := "10/2003",
README_URL := 
  "http://www-circa.mcs.st-and.ac.uk/~wdg/README.quagroup",
PackageInfoURL := 
  "http://www-circa.mcs.st-and.ac.uk/~wdg/PackageInfo.g",
AbstractHTML := "The package <span class=\"pkgname\">QuaGroup</span> contains \
                 functinality for working with quantized enveloping algebras\
                 of finite-dimensional semisimple Lie algebras.",
PackageWWWHome := "http://www-circa.mcs.st-and.ac.uk/~wdg/quagroup.html",
PackageDoc := [rec(
  BookName := "QuaGroup",
  Archive := 
      "http://www-circa.mcs.st-and.ac.uk/~wdg/quadoc.tar.gz",                 
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
"     |          QuaGroup      Version 1.1                              \n",
"     |                                                                 \n",
"-----------     A package for dealing with quantized enveloping algebras\n",
"     |                                                                 \n",
"     |          Willem de Graaf                                        \n",
"     |          quagroup@hetnet.nl                                     \n\n"
),
Keywords := ["quantum groups"]
));



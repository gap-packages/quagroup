############################################################################
##
#W  fileacc.gd                  QuaGroup                     Willem de Graaf
##
##
##  Writing and reading algebras, modules to, from files
##


############################################################################
##
#O   WriteQEAToFile( <U>, <file> )
##
##   Write <U> to <file>.
##
DeclareOperation( "WriteQEAToFile", [ IsQuantumUEA, IsString ] );

############################################################################
##
#O   ReadQEAFromFile( <file> )
##
##   Read a QEA from <file>.
##
DeclareOperation( "ReadQEAFromFile", [ IsString ] );


############################################################################
##
#O   WriteModuleToFile( <V>, <file> )
##
##   Write the module <V> to <file>.
##
DeclareOperation( "WriteModuleToFile", [ IsAlgebraModule, IsString ] );


############################################################################
##
#O   ReadModuleFromFile( <file> )
##
##   Read a module from <file>.
##
DeclareOperation( "ReadModuleFromFile", [ IsString ] );


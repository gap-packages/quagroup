############################################################################
##
#W  rmat.gd                  QuaGroup                         Willem de Graaf
##
##
##


############################################################################
##
#O  IsomorphismOfTensorModules( <V>, <W> )
##
##  Returns an isomorphism <V>x<W> --> <W>x<V>.
##
DeclareOperation( "IsomorphismOfTensorModules", 
                          [ IsAlgebraModule, IsAlgebraModule ] );


#############################################################################
##
#A  RMatrix( <V> )
##
##  Returns the R-matrix corresponding to the U-module <V>.
## 
DeclareAttribute( "RMatrix", IsAlgebraModule );

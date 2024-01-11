##########################################################################
##
#W  basic.gd                  QuaGroup                      Willem de Graaf
##
##
##  Declares some global variables and operations to be used throughout.
##

#############################################################################
##
#V  QGPrivateFunctions
##
##
BindGlobal( "QGPrivateFunctions", rec(indetNo:= 1000) );


#############################################################################
##
#C   IsQuantumField( <F> )
##
##   The category to which the field Q(q) belongs.
##
DeclareCategory( "IsQuantumField", IsField );


#############################################################################
##
#V    _q
##
##    This is the generator of `QuantumField'. The element `q' will be
##    fixed once the package {\sf QuaGroup} is loaded. It is used 
##    in many places in the code.
##
BindGlobal( "_q", Indeterminate( Rationals, QGPrivateFunctions.indetNo ) );
SetName( _q, "q" );


###########################################################################
##
#F   GaussNumber( <n>, <a> )
##
##   is defined as $a^(n-1)+a^(n-3)+...+a^(-n+1)$.
##
DeclareOperation( "GaussNumber", [ IsInt, IsMultiplicativeElement ] );


############################################################################
##
#F   GaussianFactorial( <n>, <a> )
##
##   is defined as $[n][n-1]...[1]$, where $[k]$ is the Gauss number with 
##   respect to $k$, and <a>.
##
DeclareOperation( "GaussianFactorial", [ IsInt, 
                                 IsMultiplicativeElement   ] );


##########################################################################
##
#F   GaussianBinomial( <n>, <k>, <a> )
##
##   is defined as $[n]!/[k]![n-k]!$, where $[r]!$ is the Gaussian factorial 
##   with respect to $r$ and <a>.
##
DeclareOperation( "GaussianBinomial", [ IsInt, IsInt, 
                               IsMultiplicativeElement ] );

############################################################################
##
#A   WeightsAndVectors( <V> )
##
##   A list of two lists; the first of these is a list of the weights
##   of <V>, the second a list of corresponding weight vectors. These
##   are again grouped in lists: if the multiplicity of a weight is 
##   $\mu$, then there are $\mu$ weight vectors, forming a basis of 
##   the corresponding weight space.
##
DeclareAttribute( "WeightsAndVectors", IsAlgebraModule );

############################################################################
##
#A   HighestWeightsAndVectors( <V> )
##
##   Is analogous to `WeightsAndVetors'; only now only the highest
##   weights are listed along with the corresponding highest-weight vectors.
##
DeclareAttribute( "HighestWeightsAndVectors", IsAlgebraModule );



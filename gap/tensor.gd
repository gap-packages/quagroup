############################################################################
##
#W  tensor.gd                  QuaGroup                      Willem de Graaf
##
##
##  Tensor products of quantized enveloping algebras and their modules.
##


#############################################################################
##
#C  IsQEATensorPowElement( <qt> ) 
##
##  category of elements of the tensor square of a quantized enveloping 
##  algebra.
##
DeclareCategory( "IsQEATensorPowElement", IsTensorElement and 
                                         IsMultiplicativeElementWithOne);
DeclareCategoryCollections( "IsQEATensorPowElement" );
DeclareCategoryFamily( "IsQEATensorPowElement" );


##############################################################################
##
#O  TensorPower( <U>, <d> )
##
##  Here <U> is a quantized universal enveloping algebra, and <d> a
##  non-negative integer. This function returns the asociatitive algebra
##  with underlying vector space the <d>-fold tensor product of <U> with 
##  itself. The product is defined componentwise.
## 
DeclareOperation( "TensorPower", [ IsVectorSpace, IsInt ] );

#1 
##  By using the comultiplication $\Delta$ of a quantized universal
##  enveloping algebra $U$, the tensor product of two $U$-modules
##  can be made into a $U$-module. {\sf QuaGroup} uses the comultiplication
##  given by the following formulas
##
##  $$ \Delta( F_{\alpha} ) = F_{\alpha}\otimes K_{\alpha}^{-1} +
##       1\otimes F_{\alpha},$$ 
##  $$ \Delta( K_{\alpha} ) = K_{\alpha}\otimes K_{\alpha},$$
##  $$ \Delta( E_{\alpha} ) = E_{\alpha}\otimes 1 + K_{\alpha}\otimes
##  E_{\alpha}.$$
##
##  Furthermore, for $u\in U$ we set $\Delta^2(u) = (\Delta\otimes 1)
##  (\Delta(u))$,
##  $\Delta^3(u) = (\Delta\otimes 1\otimes 1)(\Delta^2(u))$, etc. 
##  These formulas are used to make the tensor product of three, four, ...
##  $U$-modules into a $U$-module. It is of course also possible to do this
##  by using the tensor product for two $U$-modules. 
##

#############################################################################
##
#O  UseTwistedHopfStructure( <U>, <f> )
##
##  Use twisted Hopf structure, by the (anti-)automorphism <f>.
##
DeclareOperation( "UseTwistedHopfStructure", [ IsQuantumUEA, 
         IsAlgebraHomomorphism, IsAlgebraHomomorphism ] );

#############################################################################
##
#A  HopfStructureTwist( <U> )
##
DeclareAttribute( "HopfStructureTwist", IsQuantumUEA );


#############################################################################
##
#O  ComultiplicationMap( <U>, <d> )
##
DeclareAttribute( "ComultiplicationMap", IsQuantumUEA );

#############################################################################
##
#C  IsComultMap( <map> )
#C  IsGenericCoMultMap( <map> )
#C  IsInducedCoMultMap( <map> )
##
DeclareCategory( "IsCoMultMap", IsAlgebraHomomorphism ); 
DeclareCategory( "IsGenericCoMultMap", IsCoMultMap );
DeclareCategory( "IsInducedCoMultMap", IsCoMultMap );


#############################################################################
##
#A  AntipodeMap( <U> )
##
DeclareAttribute( "AntipodeMap", IsQuantumUEA );


#############################################################################
##
#A  CounitMap( <U> )
##
DeclareAttribute( "CounitMap", IsQuantumUEA );


#############################################################################
##
#C  IsDualElement( <I> ) 
##
##  category of elements of a dual vector space.
##
DeclareCategory( "IsDualElement", IsVector and IsMapping and 
                                                IsSPGeneralMapping ); 
DeclareCategoryCollections( "IsDualElement" );
DeclareCategoryFamily( "IsDualElement" );


#############################################################################
##
#F  IsDualElementsSpace( <V> )
##
##  Finite dimensional spaces of dual elements are handled by nice bases.
##
DeclareHandlingByNiceBasis( "IsDualElementsSpace",
    "for free left modules of dual elements" );


##############################################################################
##
#O  DualSpace( <V> )
##
##  The dual space of the vector space <V>.
##
DeclareOperation( "DualSpace", [ IsLeftModule ] );

##############################################################################
##
#A  DualAlgebraModule( <V> )
##
##  The dual module of the algebra module <V>.
##
DeclareAttribute( "DualAlgebraModule", IsAlgebraModule );

##############################################################################
##
#A  TrivialAlgebraModule( <U> )
##
##  The trivial module over <U>
##
DeclareAttribute( "TrivialAlgebraModule", IsAlgebra );


############################################################################
##
#W  qea.gd                  QuaGroup                          Willem de Graaf
##
##
##  Declarations for elements of quantized enveloping algebras, and highest
##  weight modules
##



##############################################################################
##
#C  IsQEAElement( <obj> )
#C  IsQEAElementCollection( <obj> )
#C  IsQEAElementFamily( <fam> )
##
##  This is the category of elements of a quantized enveloping algebra.
##  
DeclareCategory( "IsQEAElement", IsVector and IsRingElement and
                     IsMultiplicativeElementWithOne );
DeclareCategoryCollections( "IsQEAElement" );
DeclareCategoryFamily( "IsQEAElement" );


##############################################################################
##
#F   CollectQEAElement
##
##
DeclareGlobalFunction( "CollectQEAElement" );

#############################################################################
##
#C   IsQuantumUEA( <A> )
##
##   The category of quantized enveloping algebras.
##
DeclareCategory( "IsQuantumUEA", IsAlgebra );

#############################################################################
##
#A   QuantizedUEA( <R> )
##
##   For a root system <R> this function returns the corresponding quantized 
##   enveloping algebra <U>. The attribute `GeneratorsOfAlgebra' of <U>
##   is a list of generators of a PBW-type basis of <U>. These are computed
##   relative to the reduced expression for the longest element of the 
##   Weyl group contained in `LongestWeylWord( <R> )'. If you would like to
##   have a PBW-type basis relative to a different reduced expression than
##   you must set the value of this attribute by hand (preferably directly
##   after creating the root system).
##
DeclareAttribute( "QuantizedUEA", IsRootSystem );


##############################################################################
##
#O  LeadingQEAMonomial( <novar>, <f> )
##
##  For an element of the negative part of a qea, this gives its leading
##  monomial with respect to the reverse lexicographical ordering.
##  <novar> is the number of generators of that negative part (i.e., 
##  the number of positive roots).
##
DeclareOperation( "LeadingQEAMonomial", [ IsInt, IsQEAElement ] );

###############################################################################
##
#F   LeftReduceQEAElement( <novar>, <G>, <lms>, <lmtab>, <p> )
##
##   Left reduction in the negative part of a qea.
##
DeclareGlobalFunction( "LeftReduceQEAElement" );

#############################################################################
##
#A   QuantumParameter( <U> )
##
##   The is the quantum parameter of the quantized universal enveloping 
##   algebra <U>.
##
DeclareAttribute( "QuantumParameter", IsQuantumUEA );


###########################################################################\
##
#C   IsGenericQUEA( <U> )
##
##   A quantized uea has this category if it is defined over 
##   the QuantumField, i.e., uring the generic function for constructing
##   quantized enveloping algebras.
##
DeclareCategory( "IsGenericQUEA", IsQuantumUEA );

#############################################################################
##
#A   IrreducibleQuotient( <V> )
##
##   Here <V> is a highest-weight module over a quantized enveloping
##   algebra, possibly defined with a root of 1 as quantum parameter.
##   This function returns the unique irreducible quotient of <V>,
##   that contains a highest weight vector.   
##
DeclareAttribute( "IrreducibleQuotient", IsAlgebraModule );

#############################################################################
##
#A   CanonicalMapping( <A> )
##    
DeclareAttribute( "CanonicalMapping", IsObject );

############################################################################
##
#A   GenericModule( <V> )
##
DeclareAttribute( "GenericModule", IsAlgebraModule);

#############################################################################
##
#O   HWModuleByGenerator( <W>, <w>, <hw> )
##
DeclareOperation( "HWModuleByGenerator", 
                             [ IsAlgebraModule, IsObject, IsList ] );

#############################################################################
##
#O   InducedQEAModule( <U>, <V> )
##
DeclareOperation( "InducedQEAModule", [ IsQuantumUEA, IsAlgebraModule ] );

############################################################################
##
#A   FundamentalModules( <U> )
##
DeclareAttribute( "FundamentalModules", IsQuantumUEA );

#############################################################################
##
#O   HWModuleByTensorProduct( <U>, <list> )
##
DeclareOperation( "HWModuleByTensorProduct", [ IsQuantumUEA, IsList ] );

#############################################################################
##
#W  isom.gd                  QuaGroup                           Willem de Graaf
##
##
##  Isomorphisms of quantized enveloping algebras.
##

##############################################################################
##
#C  IsQUEAHomomorphism( <f> )
#C  IsGenericQUEAHomomorphism( <f> )
#C  IsInducedQUEAHomomorphism( <f> )
##
##
DeclareCategory( "IsQUEAHomomorphism", IsAlgebraHomomorphism );
DeclareCategory( "IsGenericQUEAHomomorphism", IsQUEAHomomorphism );
DeclareCategory( "IsInducedQUEAHomomorphism", IsQUEAHomomorphism );

##############################################################################
##
#O  QEAAutomorphism( <U>, <list> )
##
##  operation for creating homomorphisms.
##
DeclareOperation( "QEAHomomorphism", [ IsQuantumUEA, IsObject, IsObject ] );

##############################################################################
##
#C  IsQUEAAutomorphism( <f> )
#C  IsGenericQUEAAutomorphism( <f> )
#C  IsInducedQUEAAutomorphism( <f> )
##
##  Categories of automorphisms of quantized uea's. `Generic' for 
##  automorphisms with quantum parameter q; `Induced' for automorphisms
##  of quantized uea's with a different parameter. The images of `induced'
##  automorphisms, are calculated by using the `original' map.
##
DeclareCategory( "IsQUEAAutomorphism", IsAlgebraHomomorphism and 
                      IsQUEAHomomorphism );
DeclareCategory( "IsGenericQUEAAutomorphism", IsQUEAAutomorphism and
                      IsGenericQUEAHomomorphism );
DeclareCategory( "IsInducedQUEAAutomorphism", IsQUEAAutomorphism and 
                      IsInducedQUEAHomomorphism );

##############################################################################
##
#O  QEAAutomorphism( <U>, <list> )
##
##  operation for creating automorphisms.
##
DeclareOperation( "QEAAutomorphism", [ IsQuantumUEA, IsObject ] );

#############################################################################
##
#C  IsQUEAAntiAutomorphism( <f> )
#C  IsGenericQUEAAntiAutomorphism( <f> )
#C  IsInducedQUEAAntiAutomorphism( <f> )
##
##  Categories of anti-automorphisms of quantized uea's. `Generic' for 
##  anti-automorphisms with quantum parameter q; `Induced' for 
##  anti-automorphisms of quantized uea's with a different parameter. 
##  The images of `induced'
##  anti-automorphisms, are calaulated by using the `original' map.
##
DeclareCategory( "IsQUEAAntiAutomorphism", IsAlgebraHomomorphism );
DeclareCategory( "IsGenericQUEAAntiAutomorphism", IsQUEAAntiAutomorphism );
DeclareCategory( "IsInducedQUEAAntiAutomorphism", IsQUEAAntiAutomorphism );

##############################################################################
##
#O  QEAAntiAutomorphism( <U>, <list> )
##
##  operation for creating anti-automorphisms.
##
DeclareOperation( "QEAAntiAutomorphism", [ IsQuantumUEA, IsObject ] );

##############################################################################
##
#A  AutomorphismOmega( <U> )
#A  AntiAutomorphismTau( <U> )
#O  AutomorphismTalpha( <U> )
#A  DiagramAutomorphism( <U> )
##
##  operations for creating some standard automorphisms.
##
DeclareAttribute( "AutomorphismOmega", IsQuantumUEA );
DeclareAttribute( "AntiAutomorphismTau", IsQuantumUEA );
DeclareOperation( "AutomorphismTalpha", [ IsQuantumUEA, IsInt ] );
DeclareOperation( "DiagramAutomorphism", [ IsQuantumUEA, IsPerm ] );
DeclareAttribute( "BarAutomorphism", IsQuantumUEA );

##############################################################################
##
#P  IsqReversing( <f> )
##
##  An (anti-) automorphism <f> is q-reversing if it sends q to q^-1;
##  this is strictly speaking only an isomorphism of the quea viewed
##  as Q-algebra.
##
DeclareProperty( "IsqReversing", IsQUEAAutomorphism );
DeclareProperty( "IsqReversing", IsQUEAAntiAutomorphism );

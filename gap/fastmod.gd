############################################################################
##
#W  fastmod.gd                  QuaGroup                     Willem de Graaf
##
##
##  Some fast methods for creating modules in special cases.
##


############################################################################
##
#O   A2Module( <U>, <hw> )
##
##   When the root system is of type A2.
##
DeclareOperation( "A2Module", [ IsQuantumUEA, IsList ] );


############################################################################
##
#O   MinusculeModule( <U>, <hw> )
##
##   When the highest weight is minuscule.
##
DeclareOperation( "MinusculeModule", [ IsQuantumUEA, IsList ] );




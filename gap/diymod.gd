############################################################################
##
#W  diymod.gd                  QuaGroup                      Willem de Graaf
##
##
##


##############################################################################
##
#O  DIYModule( <U>, <V>, <acts> )
##
## Here U is a quantized enveloping algebra, and 
## V is a U-module, and atcs is a list of lists, of length 4*l,
## where l is the rank of te root system. acts describes the actions
## of the generators [F_1,...,F_l,K_1,...,K_l,K_1^-1,...,K_l^-1, 
## E_1,...,E_l ]. The action of each generator is described by a list
## of length dim V, giving the images as elts of V; the zero elements
## may be omitted: in that case there is a `hole' in the list.
## This function returns the <U>-module defined by this list.
##
DeclareOperation( "DIYModule", [ IsQuantumUEA, IsLeftModule, IsList ] );

##########################################################################
##
#W  roots.gd                  QuaGroup                     Willem de Graaf
##
##
##  Some general functions for Weyl groups. 
##

############################################################################
##
#A   LongestWeylWord( <R> )
##
##   Here <R> is a root system. `LongestWeylWord( <R> )' returns
##   the longest word in the Weyl group. 
##
##   If this function is called for a root system <R>, a reduced expression 
##   the longest element in the Weyl group is calculated. However, if you
##   would like to work with a different reduced expression, then it is 
##   possible to set it by `SetLongestWeylWord( <R>, <wd> )', where <wd> is 
##   a reduced expression of the longest element in the Weyl group. Note
##   that you will have to do this *before* calling `LongestWeylWord', or
##   any function that may call `LongestWeylWord' (once the attribute is set,
##   it will not be possible to change it). Note also that you must be sure
##   that the word you give is in fact a reduced expression for the longest
##   element in the Weyl group, as this is not checked.
##
## 
DeclareAttribute( "LongestWeylWord", IsRootSystem );

############################################################################
##
#A   SimpleRootsAsWeights( <R> )
##
##   List of the simple roots represented as weights (i.e., as linear 
##   combinations of the fundamental weights).
##
DeclareAttribute( "SimpleRootsAsWeights", IsRootSystem );

###########################################################################
##
#O   ApplyWeylElement( <W>, <v>, <w> )
##
##   Here <W> is a Weyl group, <v> an element of the weight lattice,
##   written as linear combination of the fundamental weights, and <w>
##   is a (not necessarily reduced) word in <W>. This function returns
##   the image of <v> under the action of <w>.
##
DeclareOperation( "ApplyWeylElement", [ IsWeylGroup, IsList, IsList ] );

#############################################################################
##
#O  LengthOfWeylWord( <W>, <w> )
##
##  Here <W> is a Weyl group, and <w> a (not necessarily reduced)
##  word in <W>. This function returns the length of <w>.
##
DeclareOperation( "LengthOfWeylWord", [ IsWeylGroup, IsList ] );

##########################################################################
##
#O  ExchangeElement( <W>, <w>, <k> )
##
##  Here <W> is a Weyl group, and <w> is a *reduced* word in <W>,
##  and <k> is an index. Let <v> denote the word obtained from <w>
##  by adding <k> at the end. This function assumes that the length
##  of <v> is one less than the length of <w>, and returns a reduced
##  expression for <v> (using the exchange condition).
##
DeclareOperation( "ExchangeElement", [ IsWeylGroup, IsList, IS_INT ] );

##########################################################################
##
#O  GetBraidRelations( <W>, <w1>, <w2> )
##
##  Here <W> is a Weyl group, and <w1>, <w2> are words in <W>
##  representing the same element. This function returns a
##  list of braid relations that can be applied to <w1> to 
##  obtain <w2>.
##
DeclareOperation( "GetBraidRelations", [ IsWeylGroup, IsList, IsList ] );


############################################################################
##
#A   PositiveRootsInConvexOrder( <R> )
##
##   List of the positive roots in convex order. Let $w_0=s_1\cdots s_t$
##   be a reduced expression of the longest element in the Weyl group.
##   Then the $k$-th element in `PositiveRootsInConvexOrder( <R> )'
##   is the root $s_1\cdots s_k(\alpha_{i_{t-k+1}})$, where 
##   $\alpha_{i_{t-k+1}}$ is the simple root corresponding to the 
##   reflection $s_{t-k+1}$. The expression contained in 
##   `LongestWeylWord( <R> )' is used; if you would like to use
##   a different expression, then you can set the value of this
##   attribute by hand, preferably immediately after having created
##   the root system.
##
##   This order has the property that $\alpha+\beta$ lies between 
##   $\alpha$ and $\beta$.
##
DeclareAttribute( "PositiveRootsInConvexOrder", IsRootSystem );


############################################################################
##
#A   LongWords( <R> )
##
##   For a root system this returns a list of triples. Let <t> be the $k$-th
##   triple occurring in this list. The first element
##   of <t> is an expression for the longest element of the Weyl group,
##   starting with $k$. The second element is a list of elementary moves,
##   moving this expression to the value of `LongestWeylWord( <R> )'.
##   The third element is a list of elementary moves performing the 
##   reverse transformation.
##
##
DeclareAttribute( "LongWords", IsRootSystem );

#############################################################################
##
#O  ReducedWordIterator( <W>, <wd> )
## 
##  iterates over all reduced expressions for the reduced word <wd>.
##
DeclareOperation( "ReducedWordIterator", [ IsWeylGroup, IsList ] );

##############################################################################
##
#A  TypeOfRootSystem( <R> )
##
##  This attribute is a list of the form, e.g., [ "F", 4, "G", 2 ];
##  meaning that the root system is of type F4+G2.
##
DeclareAttribute( "TypeOfRootSystem", IsRootSystem );


############################################################################
##
#A   BilinearFormMatNF( <R> )
##
##   Matrix of the bilinear form of <R>, such that the smallest squared
##   norm is 2.
##
DeclareAttribute( "BilinearFormMatNF", IsRootSystem );

############################################################################
##
#A   PositiveRootsNF( <R> )
##
##   Set of positive roots written as linear combinations of the simple roots.
##
DeclareAttribute( "PositiveRootsNF", IsRootSystem );

############################################################################
##
#A   SimpleSystemNF( <R> )
##
##   Simple system of <R>, where the elements are written as unit vectors.
##
DeclareAttribute( "SimpleSystemNF", IsRootSystem );

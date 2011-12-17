############################################################################
##
#W  paths.gd                  QuaGroup                       Willem de Graaf
##
##
##  Declarations for LS-paths, and the path model.
##



##############################################################################
##
#C   IsLSPath( <p> )
##
##   The category of LS-paths.
##
DeclareCategory( "IsLSPath", IsObject );

##############################################################################
##
#O   DominantLSPath( <R>, <wt> )
##
##   Here <R> is a root system, and <wt> a dominant weight in the weight
##   lattice of <R>. This function returns the LS-path that is the line
##   from the origin to <wt>.
##
DeclareOperation( "DominantLSPath", [ IsRootSystem, IsList ] );

##############################################################################
##
#O   Falpha( <o>, <i> )
##
##   Here <o> is an object, which can be (A) an LS-path, (B) a monomial in the 
##   negative part of a quantized enveloping algebra, or (C) an element of a 
##   module over a quantized enveloping algebra. Furthermore,
##   <i> an integer. This function returns the object obtained from <o> by
##   (A) applying the root operator $f_{\alpha_i}$, where $\alpha_i$ is the 
##   <i>-th simple root, or (B,C) applying the Kashiwara operator 
##   $\tilde{F}_i$, corresponding to the <i>-th simple root.
##
DeclareOperation( "Falpha", [ IsObject, IsInt ] );

##############################################################################
##
#O   Ealpha( <p>, <i> )
##
##   Here <o> is an object, which can be (A) an LS-path, (B) a monomial in the 
##   negative part of a quantized enveloping algebra, or (C) an element of a 
##   module over a quantized enveloping algebra. Furthermore,
##   <i> an integer. This function returns the object obtained from <o> by
##   (A) applying the root operator $e_{\alpha_i}$, where $\alpha_i$ is the 
##   <i>-th simple root, or (B,C) applying the Kashiwara operator 
##   $\tilde{E}_i$, corresponding to the <i>-th simple root.
##
DeclareOperation( "Ealpha", [ IsObject, IsInt ] );

##############################################################################
##
#A   WeylWord( <p> )
##
##   Here <p> is an LS-path in the orbit (under the root operators)
##   of a dominant LS-path $p_0$ ending in the dominant weight $\lambda$. 
##   This means that the first direction of <p> is of the form 
##   $s_1\cdots s_m(\lambda)$. This function returns the reduced 
##   word $s_1\cdots s_m$.
##    
DeclareAttribute( "WeylWord", IsLSPath );

##############################################################################
##
#A   EndWeight( <p> )
##
##   Here <p> is an LS-path; this function returns the weight that is 
##   the endpoint of <p>.
##
DeclareAttribute( "EndWeight", IsLSPath );

##############################################################################
##
#A   LSSequence( <p> )
##
##   returns the two sequences (of weights and rational numbers) that
##   define the LS-path <p>.
##
DeclareAttribute( "LSSequence", IsLSPath );


##############################################################################
##
#F   CrystalGraph( <R>, <wt> )
#F   CrystalGraph( <V> )
##
##   This function returns a record describing the crystal graph corresponding
##   to the input
##   Denote the output by <r>; then <r>`.points' is the list of 
##   points of the graph. Furthermore, <r>`.edges' is a list
##   of edges of the graph; this is a list of lists of the form 
##   `[ [ i, j ], u ]'. This mean that point `i' (i.e., the point 
##   on position `i' in <r>.`points') is connected to 
##   point `j', and that the edge has label `u'.
##
##   The input can have two formats. First it can be a root system
##   <R> together with a dominant weight <wt>. In this case <r>.`points'.
##   is a set of LS-paths.
##
DeclareGlobalFunction( "CrystalGraph" );

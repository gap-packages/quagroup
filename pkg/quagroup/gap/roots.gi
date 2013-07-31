###########################################################################
##
#W  roots.gi                  QuaGroup                     Willem de Graaf
##
##
##  Some general functions for root systems and Weyl groups. 
##



##########################################################################
##
#M   RootSystem( [t1, n1, t2, n2, ....] )
#M   RootSystem( t, n )
##
InstallOtherMethod( RootSystem,
    "for a sequence of types and ranks",
    true, [ IsList ], 0,

    function( lst )
    
       local   C,  i,  posr,  ready,  ind,  le,  a,  j,  ej,  r,  b,  q,  
               R, bilin, types, ranks, n, type, k, lenr, CM, Bl, offset, 
               simp, posR, rt;  

#+  Here t1, t2,... are types, i.e., capital letters between `"A"', and `"G"'.
#+  n1, n2,... are ranks, i.e., positive integers. This function constructs
#+  the root system corresponding to this data. Fpr example if the input is 
#+  `[ "A", 3, "F", 4 ]', then the root system of type $A_3+F_4$ is
#+  constructed. 
    
       lenr:= Sum( lst{[2,4..Length(lst)]} );
       posR:= [ ];
       simp:= [ ];
       CM:= NullMat( lenr, lenr );
       Bl:= NullMat( lenr, lenr );
       offset:= 0;

       for k in [1,3..Length(lst)-1] do
        
          type:= lst[k]; n:= lst[k+1];

          if not type in [ "A", "B", "C", "D", "E", "F", "G" ] then
             return "type not one of A, B, C, D, E, F";
          fi;

          if not IsInt( n ) and n > 0 then
             return "rank not a positive integer";
          fi; 
       
          C:= 2*IdentityMat( n );
          if type = "A" then
             for i in [1..n-1] do
                 C[i][i+1]:= -1;
                 C[i+1][i]:= -1;
             od;
             bilin:= List( C, ShallowCopy );
          elif type = "B" then
             for i in [1..n-1] do
                 C[i][i+1]:= -1;
                 C[i+1][i]:= -1;
             od;
             C[n-1][n]:= -2;
             bilin:= 2*C;
             bilin[n-1][n]:= -2;
             bilin[n][n]:= 2;
          elif type = "C" then
             for i in [1..n-1] do
                 C[i][i+1]:= -1;
                 C[i+1][i]:= -1;
             od;
             C[n][n-1]:= -2;
             bilin:= List( C, ShallowCopy );
             bilin[n][n]:= 4;
             bilin[n-1][n]:= -2;
        
          elif type = "D" then
             for i in [1..n-2] do
                 C[i][i+1]:= -1;
                 C[i+1][i]:= -1;
             od;        
             C[n-2][n]:=-1;
             C[n][n-2]:= -1;
             bilin:= List( C, ShallowCopy );
          elif type = "E" then
        
             C:= [
                   [ 2, 0, -1, 0, 0, 0, 0, 0 ], [ 0, 2, 0, -1, 0, 0, 0, 0 ],
                   [ -1, 0, 2, -1, 0, 0, 0, 0 ], [ 0, -1, -1, 2, -1, 0, 0, 0 ],
                   [ 0, 0, 0, -1, 2, -1, 0, 0 ], [ 0, 0, 0, 0, -1, 2, -1, 0 ],
                   [ 0, 0, 0, 0, 0, -1, 2, -1 ], [ 0, 0, 0, 0, 0, 0, -1, 2 ] ];
        
             if n = 6 then
                C:= C{ [ 1 .. 6 ] }{ [ 1 .. 6 ] };
             elif n = 7 then
                C:= C{ [ 1 .. 7 ] }{ [ 1 .. 7 ] };
             elif n < 6 or 8 < n then
                 return "rank for E  must be one of 6, 7, 8";
             fi;
             bilin:= List( C, ShallowCopy );
          elif type = "F" then
             if n<>4 then 
                return "rank for F must be 4";
             fi;

             C:= [ [2,-1,0,0], [-1,2,-2,0], [0,-1,2,-1], [0,0,-1,2] ];
             bilin:= [ [4,-2,0,0], [-2,4,-2,0], [0,-2,2,-1], [0,0,-1,2] ];
          elif type = "G" then
             if n<>2 then 
                return "rank for G must be 2";
             fi;
             C:= [[2,-1],[-3,2]];
             bilin:= [[2,-3],[-3,6]];
          fi;

          for i in [1..n] do
             for j in [1..n] do
                CM[i+offset][j+offset]:= C[i][j];
                Bl[i+offset][j+offset]:= bilin[i][j];
             od;
          od;
    
          posr:= [ ];
          for j in [1..n] do
             rt:= [1..lenr]*0;
             rt[offset+j]:= 1;
             Add( posr, rt );
          od;
                     
          ready:= false;
          ind:= 1;
          le:= n;
          while ind <= le  do
        
             # We loop over those elements of `posR' that have been found in
             # the previous round, i.e., those at positions ranging from
             # `ind' to `le'.
        
             le:= Length( posr );
             for i in [ind..le] do
                 a:= posr[i];
            
                 # We determine whether a+ej is a root (where ej is the j-th
                 # simple root).
                 for j in [1..n] do
                     ej:= posr[j];
                
                     # We determine the maximum number `r' such that a-r*ej is
                     # a root.
                     r:= -1;
                     b:= ShallowCopy( a );
                     while b in posr do
                         b:= b-ej;
                         r:=r+1;
                     od; 
                     q:= r-LinearCombination( TransposedMat( C )[j], 
                                               a{[offset+1..offset+n]} );
                     if q>0 and (not a+ej in posr ) then 
                        Add( posr, a+ej );
                     fi;
                 od;
             od;
             ind:= le+1;
             le:= Length( posr );
          od; 

          Append( posR, posr );
          Append( simp, posr{[1..n]} );

          offset:= offset+n;                    

       od;
    
       R:= Objectify( NewType( NewFamily( "RootSystemFam", IsObject ),
                   IsAttributeStoringRep and 
                   IsRootSystem ), rec() );
       SetPositiveRoots( R, posR );
       SetNegativeRoots( R, -posR );
       SetSimpleSystem( R, simp );
       SetCartanMatrix( R, CM );
       SetBilinearFormMat( R, Bl );
       SetPositiveRootsNF( R, posR );
       SetSimpleSystemNF( R, simp );
       SetBilinearFormMatNF( R, Bl );
       SetTypeOfRootSystem( R, lst );
       return R;
    
end );

InstallOtherMethod( RootSystem,
    "for a type and a rank",
    true, [ IsString, IsInt ], 0,
function( tp, rk ) 

#+ The second format is short for RootSystem( [ t, n ] ).

      return RootSystem( [tp,rk] ); 
end );
  
#############################################################################
##
#M  PrintObj( <R> )
##
##
InstallMethod( PrintObj, 
        "for a root system with type set",
        true, [ IsRootSystem and HasTypeOfRootSystem ], 0,
        function( R )
    
    local   tt,  k;
    
    tt:= TypeOfRootSystem( R );
    Print("<root system of type ");
    for k in [1,3..Length(tt)-1] do
        Print(tt[k]); Print(tt[k+1]);
        if k < Length( tt ) - 1 then Print(" "); fi;
    od;
    Print(">");
end );



##########################################################################
##
#M   SimpleRootsAsWeights( <R> )
##
##
InstallOtherMethod( SimpleRootsAsWeights,
    "for a root system",
    true, [ IsRootSystem ], 0,
function( R )

    return PositiveRootsAsWeights( R ){ 
           List( SimpleSystem(R), x -> Position( PositiveRoots(R), x ) ) };
end );

#######################################################################
##
#M   LongestWeylWord( <R> )          for a root system
##
InstallMethod( LongestWeylWord,
        "for a root system", true, 
        [ IsRootSystem ], 0,
        function( R )
    
    return ConjugateDominantWeightWithWord( WeylGroup(R), 
                List( [1..Length(CartanMatrix(R))], x -> -1 ) )[2];
end );
    

###########################################################################
##
#M   ApplyWeylElement( <W>, <v>, <w> )
##
InstallMethod( ApplyWeylElement,
       "for Weyl group, vector, word in the Weyl group", true,
       [ IsWeylGroup, IsList, IsList ], 0,
function( W, vec, w )
    
    # apply `w' to the vector `vec'
    # (written as linco of the fundamental wts)
    
    local   res,  k;
    
    res:= ShallowCopy( vec );
    for k in [Length(w), Length(w)-1..1] do
        ApplySimpleReflection( SparseCartanMatrix( W ), w[k], res );
    od;
    return res;
    
end );


#############################################################################
##
#M   LengthOfWeylWord( <W>, <w> )
##
##
InstallMethod( LengthOfWeylWord,
     "for a Weyl group and a word in that group", true,
     [ IsWeylGroup, IsList ], 0,
function( W, w )

    local   posR;
    
    posR:= PositiveRootsAsWeights( RootSystem(W) );
    return Length( Filtered( posR, x -> not ( ApplyWeylElement( W, x, 
                   w )  in posR ) ) );
    
end );


##########################################################################
##
#M  ExchangeElement( <W>, <w>, <k> )
##
##
InstallMethod( ExchangeElement,
      "for a Weyl group, word, and index", true,
      [ IsWeylGroup, IsList, IS_INT ], 0,

function( W, w, ind )
    
    # we *assume* that w*ind has length l(w)-1.
    # we return a reduced expression for w*ind.
    
    local   R, n,  posR,  alph,  u, sim;

    n:= Length( w );
    R:= RootSystem( W );

    posR:= PositiveRootsAsWeights( R );
    sim:= SimpleRootsAsWeights( R );
    alph:= sim[ ind ];
    while n >= 1 do
        alph:= ApplyWeylElement( WeylGroup(R), alph, [ w[n] ] );
        if not alph in posR then
            break;
        fi;
        n:= n-1;
    od;
    u:= ShallowCopy( w );
    Unbind( u[n] );
    return Filtered( u, x -> IsBound(x) );
end );

    
InstallMethod( GetBraidRelations,
        "for a Weyl group, and two words", 
        true, [ IsWeylGroup, IsList, IsList ], 0,
        
        function( W, w1, w2 )
    
    # here w1, w2 are two words (reduced expressions) in the Weyl group of R, 
    # representing
    # the same element. The output is a list of elementary moves,
    # moving w1 into w2.
    
    local   n,  i,  j,  ipij,  ipji, u,  st2,  st1, up, R;

    if w1=w2 then return []; fi;

    n:= Length( w1 );
    i:= w1[ n ];
    j:= w2[ n ];
    
    if i = j then
        return GetBraidRelations( W, w1{[1..n-1]}, w2{[1..n-1]} );
    fi;
    
    R:= RootSystem( W );
    ipij:= CartanMatrix(R)[i][j];
    ipji:= CartanMatrix(R)[j][i];
    
    if ipij = 0 then
        
        u:= ExchangeElement( W, w1, j );
        Add( u, j );
        
        # u is now a third rep of the same elt, but ending with i,j
        
        st2:= GetBraidRelations( W, u{[1..n-1]}, w2{[1..n-1]} );
        u[n]:=i; u[n-1]:= j;
        st1:= GetBraidRelations( W, w1{[1..n-1]}, u{[1..n-1]} );
        Add( st1, [ n-1, i, n, j ] );
        Append( st1, st2 );
        return st1;
    elif ipij = -1 and ipji = -1 then
        
        u:= ExchangeElement( W, w1, j );
        Add( u, j );
        u:= ExchangeElement( W, u, i );  
        Add( u, i );
        
        # now u is a third rep of the same elt, but ending with i,j,i
        
        st1:= GetBraidRelations( W, w1{[1..n-1]}, u{[1..n-1]} );
        Add( st1, [ n-2, j, n-1, i, n, j ] );
        
        u[n-2]:= j; u[n-1]:= i; u[n]:= j;
        
        Append( st1, GetBraidRelations( W, u{[1..n-1]}, 
                                                    w2{[1..n-1]} ) );
        return st1;

    elif ipij = -2 or ipji = -2 then

        u:= ExchangeElement( W, w1, j );
        Add( u, j );
        u:= ExchangeElement( W, u, i );  
        Add( u, i );
        u:= ExchangeElement( W, u, j );
        Add( u, j );
        
        # now u is a third rep of the same elt, but ending with i,j,i,j

        up:= ShallowCopy( u );
        up[n-3]:= j; up[n-2]:= i; up[n-1]:= j; up[n]:= i;

        st1:= GetBraidRelations( W, w1{[1..n-1]}, up{[1..n-1]} );
        Add( st1, [ n-3, i, n-2, j, n-1, i, n, j ] );
        
        Append( st1, GetBraidRelations( W, u{[1..n-1]}, 
                                                     w2{[1..n-1]} ) );
        return st1;
        
    elif ipij = -3 or ipji = -3 then

        u:= ExchangeElement( W, w1, j );
        Add( u, j );
        u:= ExchangeElement( W, u, i );  
        Add( u, i );
        u:= ExchangeElement( W, u, j );
        Add( u, j );
        u:= ExchangeElement( W, u, i );  
        Add( u, i );
        u:= ExchangeElement( W, u, j );
        Add( u, j );
        
        # now u is a third rep of the same elt, but ending with i,j,i,j,i,j

        up:= ShallowCopy( u );
        up[n-5]:=j; up[n-4]:= i;
        up[n-3]:= j; up[n-2]:= i; up[n-1]:= j; up[n]:= i;

        st1:= GetBraidRelations( W, w1{[1..n-1]}, up{[1..n-1]} );
        Add( st1, [ n-5, i, n-4, j, n-3, i, n-2, j, n-1, i, n, j ] );
        
        Append( st1, GetBraidRelations( W, u{[1..n-1]}, 
                                                     w2{[1..n-1]} ) );
        return st1;

    fi;
end );


##########################################################################
##
#M   PositiveRootsInConvexOrder( <R> )
##
##
InstallMethod( PositiveRootsInConvexOrder,
    "for a root system",
    true, [ IsRootSystem ], 0,
function( R )

    local   w0,  wts,  list,  len,  k,  sims;    
    
    w0:= LongestWeylWord( R );
    wts:= PositiveRootsAsWeights( R );
    sims:= SimpleRootsAsWeights( R );
    list:= [ ];
    len:= Length( w0 );
    for k in [1..Length( w0 )] do
        Add( list, PositiveRootsNF(R)[ Position( wts,
                ApplyWeylElement( WeylGroup(R), sims[w0[k]],
                        w0{[1..k-1]} ) ) ] );
    od;
    return list;
    
end );

############################################################################
##
#M  LongWords( <R> )
##
##  Straightforward function.
##
InstallMethod( LongWords,
        "for a root system",
        true, [ IsRootSystem ], 0,
        function( R )
    
    local   w0,  w0rev,  wds,  i,  v;
    
    w0:= LongestWeylWord( R );
    w0rev:= Reversed( w0 );
    wds:= [ ];
    for i in [1..Length( CartanMatrix(R) )] do
        v:= ExchangeElement( WeylGroup(R), w0rev, i );
        Add( v, i );
        v:= Reversed( v );
        Add( wds, [ v, GetBraidRelations( WeylGroup(R), w0, v ),
                GetBraidRelations( WeylGroup(R), v, w0 ) ] );
    od;
    return wds;
end);


DeclareRepresentation( "IsReducedWordIteratorRep", IsComponentObjectRep,
              [ "weylGroup", "stack", "isDone" ] );


##############################################################################
##
#M   ReducedWordIterator( <W>, <wd> )
##
##
InstallMethod( ReducedWordIterator,
        "for a Weyl group and a reduced word",
        true,
        [ IsWeylGroup, IsList ], 0,

        function( W, word )
    
    local   lam,  stack,  rep,  pos;
    
    lam:= List( CartanMatrix( RootSystem( W ) ), x -> 1 );
    lam:= ApplyWeylElement( W, lam, word );
    
    stack:= [ ];
    rep:= [ ];
    pos:= PositionProperty( lam, x -> x < 0 );
    while pos <> fail do
        Add( stack, [ lam, ShallowCopy(rep), pos ] );
        lam:= ApplyWeylElement( W, lam, [pos] );
        Add( rep, pos );
        pos:= PositionProperty( lam, x -> x < 0 );
    od;
    Add( stack, [ rep ] );

    return Objectify( NewType( IteratorsFamily,
                   IsIterator
                   and IsMutable
                   and IsReducedWordIteratorRep ),
                   rec( stack:= stack, weylGroup:= W, isDone:= false ) );

end );

InstallMethod( NextIterator,
        "for a reduced word iterator",
        true, [ IsIterator and IsMutable and IsReducedWordIteratorRep ], 0,
        function( it )
    
    local   W,  stck,  len,  output,  found,  node,  j,  rep,  lam,  
            pos;
    
    
    W:= it!.weylGroup;
    stck:= it!.stack;
    len:= Length( stck );
    output:= stck[ len ][1];
    
    found:= false;
    while not found do
        Unbind( stck[len] );
        len:= len - 1;
        if len = 0 then break; fi;
        node:= stck[len];
        j:= node[3]+1;
        while j <= Length( node[1] ) and node[1][j] >= 0 do
            j:= j+1;
        od;
        if j <= Length( node[1] ) then
            found:= true;
        fi;
    od;
    
    if len = 0 then 
        it!.stack:= [];
        it!.isDone:= true;
    else
    
        rep:= ShallowCopy( node[2] );
        stck[len][3]:= j;
        lam:= ApplyWeylElement( W, node[1], [j] );
        Add( rep, j );
        pos:= PositionProperty( lam, x -> x < 0 );
        while pos <> fail do
            Add( stck, [ lam, ShallowCopy( rep ), pos ] );
            lam:= ApplyWeylElement( W, lam, [pos] );
            Add( rep, pos );
            pos:= PositionProperty( lam, x -> x < 0 );
        od;
        Add( stck, [ rep ] );
        
        it!.stack:= stck;
    fi;
    
    return output;
    
end );

    
############################################################################
##
#M  IsDoneIterator( <it> ) . . . . . . . . . . . . for reduced word iterator
##
##
InstallMethod( IsDoneIterator,
        "for reduced word iterator",
        true, [ IsIterator and IsMutable and IsReducedWordIteratorRep ], 0,
        function( it )

    return it!.isDone;

end );


############################################################################
##
#M  BilinearFormMatNF( <R> )
##
##
InstallMethod( BilinearFormMatNF,
        "for a root system",
        true, [ IsRootSystem ], 0,
        function( R )

    local m;

    m:= Minimum( List([1..Length(CartanMatrix(R))], i -> 
            BilinearFormMat(R)[i][i] ) );
    return BilinearFormMat(R)*2/m;
end );

############################################################################
##
#M  PositiveRootsNF( <R> )
##
##
InstallMethod( PositiveRootsNF,
        "for a root system",
        true, [ IsRootSystem ], 0,
        function( R )

    local b, st;

    st:= SimpleSystem(R);
    b:= Basis( VectorSpace( DefaultFieldOfMatrix(st), st ), st );
    return List( PositiveRoots(R), x -> Coefficients( b, x ) );
end );


############################################################################
##
#M  SimpleSystemNF( <R> )
##
##
InstallMethod( SimpleSystemNF,
        "for a root system",
        true, [ IsRootSystem ], 0,
        function( R )

    return IdentityMat( Length(CartanMatrix(R)) );
end );

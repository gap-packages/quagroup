############################################################################
##
#W  fastmod.gi                  QuaGroup                     Willem de Graaf
##
##
##  Some fast methods for creating modules in special cases.
##

InstallMethod( A2Module,
        "for a qea of type A2, highest weight", true,
        [ IsQuantumUEA and IsGenericQUEA, IsList ], 0,
        function( U, hw )
    
    local   n1,  n2,  bas,  mons,  c,  b,  a,  erep,  dim,  V,  vv,  
            acts,  act,  i,  pos,  M,  v,  k,  v1,  v2,  W,  wts,  
            vecs,  wt;
    
    n1:= hw[1]; n2:= hw[2];
    
    # Get a basis of the module:
    bas:= [ ];
    mons:=  [ ];
    for c in [0..n1] do
        for b in [c..n2+c] do
            for a in [0..n1+b-2*c] do
                erep:= [ ];
                if a <> 0 then Append( erep, [1,a] ); fi;
                if c <> 0 then Append( erep, [2,c] ); fi;
                if b-c <> 0 then Append( erep, [3,b-c] ); fi;
                
                Add( mons, ObjByExtRep( ElementsFamily(FamilyObj(U)),
                        [ erep, _q^0 ] ) );
                Add( bas, [a,b,c] );
            od;
        od;
    od;
    
    # The actual module will be a sparse row space:
    dim:= Length( bas );
    V:= FullSparseRowSpace( QuantumField, dim );
    vv:= BasisVectors( Basis(V) );
    acts:= [ ];
    
    # We compute the actions:
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        if a < n1+b-2*c then
            pos:= Position( bas, [a+1,b,c] );
            Add( act, GaussNumber( a+1, _q )*vv[pos] );
        elif a+1+c <= b then
            M:= Minimum( c, n2+c-b );
            v:= Zero(V);
            for k in [1..M] do
                pos:= Position( bas, [a+1+k,b,c-k] );
                v:= v + _q^(k*(b-c+k))*GaussianBinomial( a+1+k, k,_q )*vv[pos];
            od;
            v:= -v*GaussNumber( a+1, _q );
            Add( act, v );
        else
            M:= Minimum( c, n2+c-b );
            v:= Zero(V);
            for k in [1..M] do
                pos:= Position( bas, [a+1+k,b,c-k] );
                v:= v + _q^(k*(a+1+k))*GaussianBinomial( b-c+k, b-c,_q )*
                    vv[pos];
            od;
            v:= -v*GaussNumber( a+1, _q );
            Add( act, v );
        fi;
    od;
    Add( acts, act );
    
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        if b=n2+c then
            v:= Zero(V);
        else
            v:= _q^(a-c)*GaussNumber( b-c+1, _q )*
                vv[ Position( bas, [a,b+1,c] ) ];
        fi;
        
        if a >= 1 then
            if c < n1 then
                pos:= Position( bas, [a-1,b+1,c+1] );
                v:= v+GaussNumber( c+1, _q )*vv[pos];
            elif a+c<=b+1 then
                M:= Minimum( c, n2+c-b-1 );
                v1:= Zero( V );
                for k in [0..M] do
                    pos:= Position( bas, [a+k,b+1,c-k] );
                    v1:=v1+_q^((k+1)*(b+1-c+k))*
                        GaussianBinomial(a+k,k+1,_q)*vv[pos];
                od;
                v:= v-v1*GaussNumber( c+1, _q );
            else
                M:= Minimum( c, n2+c-b-1 );
                v1:= Zero( V );
                for k in [0..M] do
                    pos:= Position( bas, [a+k,b+1,c-k] );
                    v1:=v1+_q^((k+1)*(a+k))*
                        GaussianBinomial(b-c+1+k,b-c,_q)*vv[pos];
                od;
                v:= v-v1*GaussNumber( c+1, _q );
            fi;
        fi;
        Add( act, v );
    od;
    Add( acts, act );
    
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        Add( act, _q^(n1-2*(a+c)+b)*vv[i] );
    od;
    Add( acts, act );
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        Add( act, _q^(n2+a+c-2*b)*vv[i] );
    od;
    Add( acts, act );
    
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        Add( act, _q^-(n1-2*(a+c)+b)*vv[i] );
    od;
    Add( acts, act );
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        Add( act, _q^-(n2+a+c-2*b)*vv[i] );
    od;
    Add( acts, act );
    
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        if a = 0 then
            v1:= Zero(V);
        else
            pos:= Position( bas, [a-1,b,c] );
            v1:= GaussNumber( 1-a-2*c+b+n1, _q )*vv[pos];
        fi;
        if c = 0 or b = n2+c then
            v2:= Zero(V);
        else
            pos:= Position( bas, [a,b,c-1] );
            v2:= _q^(n1+2+b-2*c)*GaussNumber( b-c+1, _q )*vv[pos];
        fi;
        Add( act, v1-v2 );
    od;
    Add( acts, act );
    act:= [ ];
    for i in [1..dim] do
        a:= bas[i][1]; b:= bas[i][2]; c:= bas[i][3];
        if b = c or a = n1+b-2*c then
            v1:= Zero(V);
        else
            pos:= Position( bas, [a,b-1,c] );
            v1:= GaussNumber( n2+1-b+c, _q )*vv[pos];
        fi;
        if c = 0 then
            v2:= Zero(V);
        else
            pos:= Position( bas, [a+1,b-1,c-1] );
            v2:= _q^(2*b-2*c-n2)*GaussNumber( a+1, _q )*vv[pos];
        fi;
        if a < n1+b-2*c or b = c then
            Add( act, v1+v2 );
        else
            M:= Minimum( c, n2+c-b+1 );
            v1:= Zero( V );
            for k in [1..M] do
                pos:= Position( bas, [a+k,b-1,c-k] );
                v1:= v1 + _q^(k*(a+k))*GaussianBinomial( b-c+k-1, b-c-1, _q)*
                     vv[pos];
            od;
            Add( act, v2-GaussNumber( n2+1-b+c, _q )*v1 );
        fi;
    od;
    Add( acts, act );
    
    W:= DIYModule( U, V, acts );
    # Set the attribute WeightsAndVectors...
    wts:= [ ]; vecs:= [ ];
    for i in [1..Length(bas)] do    
        wt:= hw-[bas[i][1]+bas[i][3],bas[i][2]]*CartanMatrix( RootSystem(U) );
        pos:= Position( wts, wt );
        if pos = fail then
            Add( wts, wt ); Add( vecs, [ Basis(W)[i] ] );
        else
            Add( vecs[pos], Basis(W)[i] );
        fi;
    od;
    SetWeightsAndVectors( W, [ wts, vecs ] );
    SetHighestWeightsAndVectors( W, [ [ wts[1] ], [ vecs[1] ] ] );
    return W;
    
end );

InstallMethod( A2Module,
        "for a qea of type A2, highest weight", true,
        [ IsQuantumUEA, IsList ], 0,
        function( U, hw )
    
    local   action,  U0,  V,  qpar,  W,  ww,  wvecs, fam;
    
    # Here U is non-generic; we construct the highest-weight
    # module over the generic quea, and compute the action by
    # mapping to this one, and mapping back. We note that it is 
    # not possible (in general) to do a Groebner basis thing, because
    # if qpar is a root of 1, then there are zero divisors.     
    
    action:= function( qpar, famU0, x, v )
        
        local Vwv, Wwv, ev, ex, im, vi, j, m, vvi, evv, i, k;
        
        Vwv:= FamilyObj( v )!.originalBVecs;
        Wwv:= FamilyObj( v )!.basisVectors;
        
        ev:= ExtRepOfObj( v );
        ex:= ExtRepOfObj( x );
        im:= 0*v;
        for i in [1,3..Length(ev)-1] do
            # calculate the image x^vi, map it back, add it to im.
            vi:= Vwv[ ev[i] ];
            for j in [1,3..Length(ex)-1] do
                m:= ObjByExtRep( famU0, [ ex[j], _q^0 ] );
                vvi:= m^vi;
                # map vvi back to the module W:
                evv:= ExtRepOfObj( ExtRepOfObj( vvi ) );
                for k in [1,3..Length(evv)-1] do
                    im:= im+Wwv[ evv[k] ]*Value( evv[k+1], qpar )*
                         ex[j+1]*ev[i+1];
                od;
            od;
        od;
        return im;
    end;
    
    U0:= QuantizedUEA( RootSystem( U ) );
    V:= A2Module( U0, hw );
    
    # create the new module
    qpar:= QuantumParameter( U );
    
    W:= LeftAlgebraModule( U, function(x,v) return 
      action( qpar, ElementsFamily( FamilyObj(U0) ), x, v ); end,
        FullSparseRowSpace( LeftActingDomain(U), Dimension(V) ) );
      
    fam:= FamilyObj( ExtRepOfObj(Zero(W)) );
    fam!.originalBVecs:= BasisVectors( Basis(V) );
    fam!.basisVectors:= List( BasisVectors( Basis( W ) ), x ->x![1] );
      
    # Set the attributes `WeightsAndVectors', and 
    # `HighestWeightsAndVectors'.
    ww:= WeightsAndVectors( V );
    wvecs:= List( ww[2], x -> List( x, y -> Basis(W)[ y![1]![1][1] ] ) );
      
    SetWeightsAndVectors( W, [ ww[1], wvecs ] );
    SetHighestWeightsAndVectors( W, [ [ww[1]], [wvecs[1]] ] );
      
    return W;
    
end );


InstallMethod( MinusculeModule,
        "for a qea, highest weight", true,
        [ IsGenericQUEA, IsList ], 0,
        function( U, hw )
    
    local   R,  char,  o,  wts,  V,  vv,  acts,  sim,  posR,  B,  
            rank,  i,  act,  j,  pos;
    
    R:= RootSystem( U );
    char:= DominantCharacter( R, hw );
    if Length( char[1] ) > 1 then  
        Error("<hw> is not minuscule.");
    fi;
    
    o:= WeylOrbitIterator( WeylGroup(R), hw );
    wts:= [ ];
    while not IsDoneIterator( o ) do
        Add( wts, NextIterator( o ) );
    od;
    
    V:= FullSparseRowSpace( LeftActingDomain(U), Length( wts ) );
    vv:= BasisVectors( Basis( V ) );
    acts:= [ ];
    sim:= SimpleRootsAsWeights( R );
    posR:= PositiveRootsInConvexOrder( R );
    B:= BilinearFormMatNF(R);
    
    rank:= Length( sim );
    # action of the F's:
    for i in [1..rank] do
        act:= [ ];
        for j in [1..Length(vv)] do
            if wts[j][i] > 0 then
                pos:= Position( wts, wts[j] - sim[i] );
                act[j]:= vv[pos];
            fi;
        od;
        Add( acts, act );
    od;
    
    # action of the K's:
    for i in [1..rank] do
        Add( acts, List( [1..Length(wts)], x -> 
                _q^(wts[x][i]*B[i][i]/2)*vv[x] ) );
    od;
    
    # action of the K's:
    for i in [1..rank] do
        Add( acts, List( [1..Length(wts)], x -> 
                _q^(-wts[x][i]*B[i][i]/2)*vv[x] ) );
    od;    
    
    # action of the F's:
    for i in [1..rank] do
        act:= [ ];
        for j in [1..Length(vv)] do
            if wts[j][i] < 0 then
                pos:= Position( wts, wts[j] + sim[i] );
                act[j]:= vv[pos];
            fi;
        od;
        Add( acts, act );
    od;
    
    return DIYModule( U, V, acts );
    
end );

       
        

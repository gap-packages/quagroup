############################################################################
##
#W  paths.gi                  QuaGroup                       Willem de Graaf
##
##
##  Implementation of methods for LS-paths.
##

#############################################################################
##
#M  PrintObj( <p> )
##
InstallMethod( PrintObj,
        "for LS paths", true,
        [ IsLSPath ], 0,
        function( path )
    
    Print("<LS path of shape ",FamilyObj( path )!.shape," ending in ");
    Print( EndWeight( path ), " >" );
end );

#############################################################################
##
#M  \=( <p1>, <p2> )
##
InstallMethod( \=,
        "for LS paths", IsIdenticalObj,
        [ IsLSPath, IsLSPath ], 0,
        function( p1, p2 )
    
    return LSSequence( p1 ) = LSSequence( p2 );
end );


#############################################################################
##
#M  DominantLSPath( <R>, <wt> )
##
InstallMethod( DominantLSPath,
        "for a dominant weight",true,
        [ IsRootSystem, IsList ], 0,
        function( R, wt )
    
    local   fam,  path;    
    
    if not ForAll( wt, x -> IsPosInt(x) or x = 0 ) then
        Error("<wt> must be dominant");
    fi;
    
    if not Length( wt ) = Length( CartanMatrix( R ) ) then
        Error( "<wt> is not contained in the weight lattice of <R>" );
    fi;
    
    fam:= NewFamily( "LSPathFamily", IsLSPath );
    fam!.shape:= wt;
    fam!.rootSystem:= R;
    path:= Objectify( NewType( fam, IsLSPath and 
                                    IsComponentObjectRep and 
                                    IsAttributeStoringRep ),
                   rec() );
    SetLSSequence( path, [ [ wt ], [ 0, 1 ] ] );
    SetWeylWord( path, [] );
    SetEndWeight( path, wt );
    return path;
end );

#############################################################################
##
#M   Falpha( <p>, <i> )
##
InstallMethod( Falpha, 
        "for an LS path and an integer", true,
        [ IsLSPath, IsInt ], 0,
        function( p, alpha )
    
    # Here path is an L-S path, represented as 
    # [ [w1, w2,..., ws], [a0=0, a1, a2, ..., as=1] ]
    # We apply the root operator f_{\alpha}.
    # alpha is represented by the index in which it occurs
    # in the list of simple roots.
    
    local   path,  R,  s,  h,  i,  m_a,  j,  k,  eta,  x,  w,  res,  
            word;
    
    path:= LSSequence( p );
    R:= FamilyObj( p )!.rootSystem;
    
    s:= Length( path[1] );
    h:= [0];
    for i in [1..s] do
        Add( h, h[i] + (path[2][i+1]-path[2][i])*path[1][i][alpha] );
    od;
    
    m_a:= Minimum( h );
    j:= Length(h);
    while h[j] <> m_a do j:= j-1; od;
    
    k:= j+1;
    while k <= Length( h ) and h[k] < m_a + 1 do
        k:= k+1;
    od;
    
    if k > Length(h) then return fail; fi;
    
    if h[k] = h[j] + 1 then
        eta:= List( path, ShallowCopy );
        for i in [j..k-1] do
            eta[1][i]:= ShallowCopy( eta[1][i] );
            ApplySimpleReflection( SparseCartanMatrix(WeylGroup(R)),
                    alpha, eta[1][i] );
        od;
    else
        x:= path[2][k-1] + (1/path[1][k-1][alpha])*(h[j]+1-h[k-1]);
        eta:= [ [], [] ];
        for i in [1..j-1] do 
            Add( eta[1], path[1][i] );
            Add( eta[2], path[2][i] );
        od;
        for i in [j..k-1] do
            w:= ShallowCopy( path[1][i] );
            ApplySimpleReflection( SparseCartanMatrix(WeylGroup(R)),
                    alpha, w );
            Add( eta[1], w );
            Add( eta[2], path[2][i] );
        od;
        Add( eta[1], path[1][k-1] );
        Add( eta[2], x );
        for i in [k..s] do
            Add( eta[1], path[1][i] );
            Add( eta[2], path[2][i] );
        od;
        Add( eta[2], path[2][s+1] );
    fi;
    
    for i in [1..Length(eta[1])-1] do
        if eta[1][i] = eta[1][i+1] then
            Unbind( eta[1][i] );
            Unbind( eta[2][i+1] );
        fi;
    od;
    eta[1]:= Filtered( eta[1], x -> IsBound(x) );
    eta[2]:= Filtered( eta[2], x -> IsBound(x) );
    
    word:= ShallowCopy( WeylWord( p ) );
    if j = 1 then 
        word:= [ alpha ];
        Append( word,  WeylWord( p ) );
    else
        word:= ShallowCopy( WeylWord( p ) );
    fi;
    
    res:= rec();    
    ObjectifyWithAttributes( res, TypeObj( p ),
            WeylWord, word,
            EndWeight, EndWeight( p ) - SimpleRootsAsWeights(R)[alpha],
            LSSequence, eta );
    
    return res;
    
end );

#############################################################################
##
#M   Ealpha( <p>, <i> )
##
InstallMethod( Ealpha, 
        "for an LS path and an integer", true,
        [ IsLSPath, IsInt ], 0,
        function( p, alpha )
    
    # Here path is an L-S path, represented as 
    # [ [w1, w2,..., ws], [a0=0, a1, a2, ..., as=1] ]
    # We apply the root operator f_{\alpha}.
    # alpha is represented by the index in which it occurs
    # in the list of simple roots.
    
    local   path,  R,  s,  h,  i,  m_a,  j,  k,  eta,  x,  w,  res,  
            word;
    
    path:= LSSequence( p );
    R:= FamilyObj( p )!.rootSystem;

    s:= Length( path[1] );
    h:= [0];
    for i in [1..s] do
        Add( h, h[i] + (path[2][i+1]-path[2][i])*path[1][i][alpha] );
    od;

    m_a:= Minimum( h );
    j:= 1;
    while h[j] <> m_a do j:= j+1; od;
    
    k:= j-1;
    while k > 0 and h[k] < m_a + 1 do
        k:= k-1;
    od;
    
    if k = 0 then return fail; fi;
    
    if h[k] = h[j] + 1 then
        eta:= List( path, ShallowCopy );
        for i in [k..j-1] do
            eta[1][i]:= ShallowCopy( eta[1][i] );
            ApplySimpleReflection( SparseCartanMatrix(WeylGroup(R)),
                    alpha, eta[1][i] );
        od;
    else
        x:= path[2][k] + (1/path[1][k][alpha])*(h[j]+1-h[k]);
        eta:= [ [ ], [ 0 ] ];
        for i in [1..k-1] do 
            Add( eta[1], path[1][i] );
            Add( eta[2], path[2][i+1] );
        od;
        Add( eta[1], path[1][k] );
        Add( eta[2], x );
        for i in [k..j-1] do
            w:= ShallowCopy( path[1][i] );
            ApplySimpleReflection( SparseCartanMatrix(WeylGroup(R)),
                    alpha, w );
            Add( eta[1], w );
            Add( eta[2], path[2][i+1] );
        od;
        for i in [j..s] do
            Add( eta[1], path[1][i] );
            Add( eta[2], path[2][i+1] );
        od;
    fi;
    
    for i in [1..Length(eta[1])-1] do
        if eta[1][i] = eta[1][i+1] then
            Unbind( eta[1][i] );
            Unbind( eta[2][i+1] );
        fi;
    od;
    eta[1]:= Filtered( eta[1], x -> IsBound(x) );
    eta[2]:= Filtered( eta[2], x -> IsBound(x) );

    word:= ShallowCopy( WeylWord( p ) );
    if k = 1 and h[k] = m_a + 1 then
        word:= Reversed( WeylWord( p ) );
        word:= ExchangeElement( WeylGroup(R), word, alpha );
        word:= Reversed( word );
    else
        word:= ShallowCopy( WeylWord( p ) );
    fi;
    
    res:= rec();    
    ObjectifyWithAttributes( res, TypeObj( p ),
            WeylWord, word,
            EndWeight, EndWeight( p ) + SimpleRootsAsWeights(R)[alpha],
            LSSequence, eta );
    
    return res;
    
end );


#############################################################################
##
#M   CrystalGraph( <R>, <wt> )
##
InstallGlobalFunction( CrystalGraph, 
        function( arg )
    
    local   R,  wt,  p,  points,  edges,  lastlev,  lastpos,  curlev,  
            curpos,  ready,  nopoints,  rk,  k,  i,  path,  pos;
    
    if Length( arg ) = 1 then
        #dispatch
        return QGPrivateFunctions.crystal_graph( arg[1] );
    fi;
    
    R:= arg[1];
    wt:= arg[2];
    p:= DominantLSPath( R, wt );
    points:= [ p ];
    edges:= [ ];
    lastlev:= [ p ];
    lastpos:= [ 1 ];
    curlev:= [ ];
    curpos:= [ ];
    ready := false;
    nopoints:= 1;
    rk:= Length( CartanMatrix( R ) );
    
    while not ready do
        
        for k in [1..Length(lastlev)] do
            for i in [1..rk] do
                path:= Falpha( lastlev[k], i );
                if path <> fail then
                    pos:= Position( curlev, path );
                    if pos = fail then
                        Add( points, path );
                        nopoints:= nopoints+1;
                        Add( curlev, path );
                        Add( curpos, nopoints );
                        Add( edges, [ [lastpos[k],nopoints], i ] );
                    else
                        Add( edges, [ [lastpos[k],curpos[pos]], i ] );
                    fi;
                fi;
            od;
        od;
        
        ready:= curlev = [ ];
        lastpos:= curpos;
        lastlev:= curlev;
        curlev:= [ ];
        curpos:= [ ];

    od;
    return rec( points:= points, edges:= edges );
end );

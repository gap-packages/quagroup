############################################################################
##
#W  fileacc.gi                  QuaGroup                     Willem de Graaf
##
##
##  Writing and reading algebras, modules to, from files
##

QGPrivateFunctions.GetQEARecord:= function( U )
    
    local   r,  U0,  R,  tt,  T,  x,  i,  j,  rel,  k;
    
    r:= rec();
    if IsGenericQUEA( U ) then
        U0:= U;
        r.isGeneric:= true;
    else
        U0:= QuantizedUEA( RootSystem( U ) );
        r.isGeneric:= false;
        r.qpar:= QuantumParameter( U );
        r.field:= LeftActingDomain( U );
    fi;
    
    # First we make a record containing the data that defines the
    # root system.
    R:= RootSystem(U0 );
                               
    if HasLongestWeylWord( R ) then
        r.longw:= LongestWeylWord( R );
    fi;
    
    if HasTypeOfRootSystem( R ) then
        r.type:= TypeOfRootSystem( R );
    fi;
    
    r.posR:= PositiveRoots(R);
    r.simp:= SimpleSystem(R);
    r.cm:= CartanMatrix(R);
    r.bl:= BilinearFormMat(R);
    r.posRNF:= PositiveRootsNF(R);
    r.simpNF:= SimpleSystemNF(R);
    r.blNF:=BilinearFormMatNF(R);
    
    # Now we do the algebra (mainly the multiplication table):
    tt:= ElementsFamily( FamilyObj( U0 ) )!.multTab;
    T:= [ ];
    x:= Indeterminate( Rationals, "_q" );
    for i in [1..Length(tt)] do
        if IsBound(tt[i]) then
            T[i]:= [ ];
            for j in [1..Length(tt[i])] do
                if IsBound( tt[i][j] ) then
                    rel:= ShallowCopy( tt[i][j] );
                    for k in [2,4..Length(rel)] do
                        rel[k]:= Value( rel[k], x );
                    od;
                    T[i][j]:= rel;
                fi;
            od;
        fi;
    od;
    r.table:= T;
    return r;
end;


InstallMethod( WriteQEAToFile,
        "for qea and string", true, [IsQuantumUEA,IsString],0,        
        function( U, file )
    
    PrintTo( file, "return ", QGPrivateFunctions.GetQEARecord( U ),";");
end );

QGPrivateFunctions.ConstructGenericQEA:= function( r )
    
    local   R,  n,  rank,  B,  fam,  tt,  T,  i,  j,  rel,  k,  gens,  
            qp,  A;
    
    R:= Objectify( NewType( NewFamily( "RootSystemFam", IsObject ),
                IsAttributeStoringRep and 
                IsRootSystem ), rec() );
    SetPositiveRoots( R, r.posR );
    SetNegativeRoots( R, -r.posR );
    SetSimpleSystem( R, r.simp );
    SetCartanMatrix( R, r.cm );
    SetBilinearFormMat( R, r.bl );
    SetPositiveRootsNF( R, r.posRNF );
    SetSimpleSystemNF( R, r.simpNF );
    SetBilinearFormMatNF( R, r.blNF );
    
    if IsBound( r.type ) then
        SetTypeOfRootSystem( R, r.type );
    fi;
    if IsBound( r.longw ) then
        SetLongestWeylWord( R , r.longw );
    fi;
    
    # Reconstruct the algebra:
    
    n:= Length(PositiveRoots(R));
    rank:= Length( CartanMatrix(R) );
    B:= BilinearFormMatNF( R );
    
    fam:= NewFamily( "QEAEltFam", IsQEAElement );
    fam!.packedQEAElementDefaultType:=
      NewType( fam, IsPackedElementDefaultRep );
    fam!.noPosRoots:= Length( PositiveRoots(R) );
    fam!.rank:= Length( CartanMatrix(R) );
    fam!.rootSystem:= R;
    fam!.convexRoots:= PositiveRootsInConvexOrder( R );
    
    tt:= r.table;
    T:= [ ];
    for i in [1..Length(tt)] do
        if IsBound(tt[i]) then
            T[i]:= [ ];
            for j in [1..Length(tt[i])] do
                if IsBound( tt[i][j] ) then
                    rel:= ShallowCopy( tt[i][j] );
                    for k in [2,4..Length(rel)] do
                        rel[k]:= _q^0*rel[k];
                    od;
                    T[i][j]:= rel;
                fi;
            od;
        fi;
    od;
    fam!.multTab:= T;
    fam!.quantumPar:= _q;
    
    # Finally construct the generators.

    gens:= [ ];
    for i in [1..n] do
        gens[i]:= ObjByExtRep( fam, [ [ i, 1 ], _q^0 ] );
    od;
    for i in [1..Length( CartanMatrix(R) )] do
        Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], _q^0 ] ) );
        qp:= _q^(B[i][i]/2);
        Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], _q^0, 
                   [ [ n+i, 0 ], 1 ], qp^-1-qp ] ) );
    od;
    for i in [1..n] do
        Add( gens, ObjByExtRep( fam, 
                [ [ n+Length(CartanMatrix(R)) +i, 1 ], _q^0 ] ) );
    od;
    
    A:= Objectify( NewType( CollectionsFamily( FamilyObj( gens[1] ) ),
                                IsMagmaRingModuloRelations
                            and IsQuantumUEA
                            and IsGenericQUEA
                            and IsAttributeStoringRep ),
                   rec() );
    SetIsAssociative( A, true );
    SetLeftActingDomain( A, QuantumField );
    SetGeneratorsOfLeftOperatorRing( A, gens );
    SetGeneratorsOfLeftOperatorRingWithOne( A, gens );
    SetOne( A, gens[1]^0 );
    SetRootSystem( A, R );
    SetQuantumParameter( A, _q );

    # add a pointer to `A' to the family of the generators:
    fam!.qAlgebra:= A;
    
    return A;
end;

InstallMethod( ReadQEAFromFile,
        "for a file name", true, [IsString], 0,  
        function( file )
    
    local   r,  U0,  R,  F,  v,  n,  rank,  B,  fam,  tt,  tt_new,  k,  
            i,  j,  rel,  gens,  qp,  A;
    
    r:= ReadAsFunction( file )();
    U0:= QGPrivateFunctions.ConstructGenericQEA( r );
    if r.isGeneric then
        return U0;
    else
        
        R:= RootSystem( U0 );
        F:= r.field;
        v:= r.qpar;
        n:= Length(PositiveRoots(R));
        rank:= Length( CartanMatrix(R) );
        B:= BilinearFormMatNF( R );
        
        fam:= NewFamily( "QEAEltFam", IsQEAElement );
        fam!.packedQEAElementDefaultType:=
          NewType( fam, IsPackedElementDefaultRep );
        fam!.noPosRoots:= n;
        fam!.rank:= rank;
        fam!.rootSystem:= R;
        
        fam!.genericQUEA:= U0;
        
        tt:= ElementsFamily( FamilyObj( U0 ) )!.multTab;
        # copy tt and substitute v for q:
        tt_new:= List([1..n], x -> [] );  
        for k in [1..n] do
            tt_new[k+rank+n]:= [];
        od;
        for i in [1..Length(tt)] do
            if IsBound( tt[i] ) then
                for j in [1..Length(tt[i]) ] do
                    if IsBound( tt[i][j] ) then
                        rel:= List( tt[i][j], ShallowCopy );
                        for k in [2,4..Length(rel)] do
                            rel[k]:= Value( rel[k], v );
                        od;
                        tt_new[i][j]:= rel;
                    fi;
                od;
            fi;
        od;
        
        fam!.multTab:= tt_new;
        
        # some more data:
        fam!.convexRoots:= ElementsFamily( FamilyObj( U0 ) )!.convexRoots;
        fam!.quantumPar:= v;
        
        # Finally construct the generators.
        
        gens:= [ ];
        for i in [1..n] do
            gens[i]:= ObjByExtRep( fam, [ [ i, 1 ], v^0 ] );
        od;
        for i in [1..Length( CartanMatrix(R) )] do
            Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], v^0 ] ) );
            qp:= v^(B[i][i]/2);
            if IsZero( qp^-1-qp ) then
                Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], qp^0 ] ) );
            else
                Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], qp^0, 
                        [ [ n+i, 0 ], 1 ], qp^-1-qp ] ) );
            fi;
        od;
        for i in [1..n] do
            Add( gens, ObjByExtRep( fam, 
                    [ [ n+Length(CartanMatrix(R)) +i, 1 ], v^0 ] ) );
        od;
        
        A:= Objectify( NewType( CollectionsFamily( FamilyObj( gens[1] ) ),
                    IsMagmaRingModuloRelations
                    and IsQuantumUEA
                    and IsAttributeStoringRep ),
                    rec() );
        SetIsAssociative( A, true );
        SetLeftActingDomain( A, F );
        SetGeneratorsOfLeftOperatorRing( A, gens );
        SetGeneratorsOfLeftOperatorRingWithOne( A, gens );
        SetOne( A, gens[1]^0 );
        SetRootSystem( A, R );
        SetQuantumParameter( A, v );
        
        # add a pointer to `A' to the family of the generators:
        fam!.qAlgebra:= A;
        
        return A;
    fi;
        
end );

InstallMethod( WriteModuleToFile,
        "for a module and a string", true, [IsAlgebraModule,IsString],0,
        function( V, file )
  
    local   U,  r,  g,  BV,  bv,  acts,  x,  i,  act,  j,  cf,  vv,  
            k,  acts1,  R,  n,  rank;
    
    # This only works for generic qea's, because in the non-generic
    # case it may be difficult to handle the K-elements. In the generic
    # case the action of a K-element follows from the actions of K, K^-1;
    # but in the non-generic case this may be difficult to achieve.
    # Maybe it would be possible to do it with some kind of fct...
    
    U:= LeftActingAlgebra( V );
    
    if not IsGenericQUEA( U ) then
        Error("Currently WriteModueToFile is only implemented for generic quantized enveloping algebras");
    fi;        
    
    r:= QGPrivateFunctions.GetQEARecord( U );
    g:= GeneratorsOfAlgebra( U );
    BV:= Basis( V );
    bv:= BasisVectors( BV );
    acts:= [ ];
    x:= Indeterminate( Rationals, "_q" );
    
    for i in [1..Length(g)] do
        act:= [ ];
        for j in [1..Length(bv)] do
            cf:= Coefficients( BV, g[i]^bv[j] );
            vv:= [ ];
            for k in [1..Length(cf)] do
                if cf[k] <> 0*cf[k] then
                    Add( vv, k ); Add( vv, Value( cf[k], x ) );
                fi;
            od;
            Add( act, vv );
        od;
        Add( acts, act );
    od;
    
    acts1:= [ ];
    R:= RootSystem(U);
    n:= Length( PositiveRoots(R) );
    rank:= Length( CartanMatrix(R) );
    for i in [1..n] do acts1[i]:= acts[i]; od;
    for i in [1..rank] do Add( acts1, acts[n+2*i-1] ); od;
    for i in [1..rank] do Add( acts1, acts[n+2*i] ); od;
    for i in [1..n] do Add( acts1, acts[n+2*rank+i] ); od;
    
    r.acts:= acts1;
    r.dim:= Dimension( V );
    
    PrintTo( file, "return ", r,";");        
    
end );


InstallMethod( ReadModuleFromFile,
        "for a file-name", true, [IsString], 0,
        function( file )
    
    local   r,  V,  bv,  acts,  aa,  i,  j,  v,  k,  U,  R,  posR,  s,  
            rank,  B,  f;    
    
    r:= ReadAsFunction( file )();
    if not r.isGeneric then
        Error("Currently ReadModueFromFile is only implemented for generic quantized enveloping algebras");
    fi;
    
    V:= FullSparseRowSpace( QuantumField, r.dim );
    bv:= BasisVectors( Basis( V ) );
    acts:= r.acts;
    aa:= [ ];
    for i in [1..Length(acts)] do
        aa[i]:= [ ];
        for j in [1..Length(acts[i])] do
            v:= Zero(V);
            for k in [1,3..Length(acts[i][j])-1] do
                v:= v + ( acts[i][j][k+1]*_q^0 )*bv[ acts[i][j][k] ];
            od;
            Add( aa[i], v );
        od;
    od;
    
    U:= QGPrivateFunctions.ConstructGenericQEA( r );
    R:= RootSystem( U );
    posR:= PositiveRootsInConvexOrder( R );
    s:= Length( posR );
    rank:= Length( CartanMatrix(R) );
    B:= BilinearFormMat( R );
    
    f:= function( x, u ) return 
      QGPrivateFunctions.DIYAction( V, s, rank, B, posR, aa, x, u ); end;
    return LeftAlgebraModule( U, f, V );
    
end );

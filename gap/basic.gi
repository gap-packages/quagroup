############################################################################
##
#W  basic.gi                 QuaGroup                       Willem de Graaf
##
##
##  Installs some global variables and operations to be used throughout.
##


#############################################################################
##
#V   QuantumField
##
##   This is the field ${\bf Q}(q)$ over which all quantized enveloping
##   algebras are defined.
##
##
BindGlobal( "QuantumField",  Objectify( NewType(
                   CollectionsFamily( FamilyObj( _q ) ),
                   IsAttributeStoringRep and 
                   IsField and 
                   IsQuantumField and 
                   IsRationalFunctionCollection ), rec() ) );

SetName( QuantumField, "QuantumField" );
SetIsLeftActedOnByDivisionRing( QuantumField, true );
SetSize( QuantumField, infinity );
SetLeftActingDomain( QuantumField, Rationals );
SetGeneratorsOfField( QuantumField, [ _q ] );
SetOne( QuantumField, _q^0 );
SetZero( QuantumField, 0*_q );

InstallMethod( \in,
    "for an object and a quantum field",
    IsElmsColls,
    [ IsObject, IsQuantumField ], 0,
    function( p, qf )
    # all univariate rational functions with indeterminate q 
    # are in the quantum field.
    
    return IsUnivariateRationalFunction( p ) and
      IndeterminateNumberOfUnivariateRationalFunction( p ) =
      IndeterminateNumberOfUnivariateRationalFunction( _q );
end );


############################################################################
##
#M   GaussNumber( <a>, <qp> )
#M   GaussianFactorial( <a>, <qp> )
#M   GaussianBinomial( <a>, <n>, <qp> )
##
##
InstallMethod( GaussNumber,
       "for an integer and a q-element",
       true, [ IsInt, IsMultiplicativeElement ], 0,

function( a, qp )
  
    if a < 0 then
       return - Sum( List( [0..-a-1], i -> qp^(-a-2*i-1) ) )*qp^0;
    fi;
    return Sum( List( [0..a-1], i -> qp^(a-2*i-1) ) )*qp^0;
end );

InstallMethod( GaussianFactorial,
     "for an integer and a q-element",
     true, [ IsInt, IsMultiplicativeElement ], 0, 
function( a, qp )
    
    return Product( List( [1..a], i -> GaussNumber( i, qp ) ) )*qp^0;
end );

InstallMethod( GaussianBinomial,
       "for two integers and a q-element",
       true, [ IsInt, IsInt, IsMultiplicativeElement ], 0,
function( a, n, qp )
    
    local e;
    e:= Product( List( [0..n-1], i -> GaussNumber( a-i, _q ) ) )*_q^0/
        ( Product( List( [2..n], i -> GaussNumber( i, _q ) ) )*_q^0 );
    return Value( e, qp );
end );

#############################################################################
##
#M   WeightsAndVectors( <V> )
##
InstallMethod( WeightsAndVectors,
        "for a module over a quantized uea", true,
        [IsAlgebraModule], 0,
        function( V )
    
    local   U,  vv,  wts,  vecs,  R,  noPosR,  rank,  Bil,  k,  v,  
            bas,  wt,  pos, get_exp; 
    
    get_exp:= function( pol )
        
        # assume that pol is q^k; get k.
        
        local   en,  ed,  k;
        
        en:= ExtRepNumeratorRatFun( pol )[1];
        ed:= ExtRepDenominatorRatFun( pol )[1];
        if en = [ ] then
            k:= 0;
        else
            k:= en[2];
        fi;
        if ed <> [] then
            k:= k-ed[2];
        fi;
        return k;
    end;
    
    
    U:= LeftActingAlgebra( V );
    if not IsQuantumUEA( U ) or not IsGenericQUEA(U) then 
        Error("<V> must be defined over a generic quantized uea");
    fi;
    
    # We only do the case where all basis elements of <V> are 
    # weight vectors. This will be the most common case; the other case
    # will in general be very har (computationally).
    
    vv:= BasisVectors( Basis( V ) );
    wts:= [ ];
    vecs:= [ ];
    R:= RootSystem( U );
    noPosR:= Length( PositiveRoots( R ) );
    rank:= Length( CartanMatrix( R ) );
    Bil:= BilinearFormMatNF( R );
    k:= GeneratorsOfAlgebra( U ){[noPosR+1,noPosR+3..noPosR+2*rank-1]};
    
    for v in vv do
        bas:= Basis( VectorSpace( LeftActingDomain(V), [v] ), [v] );
        wt:= List( [1..rank], i -> 2*get_exp( Coefficients(bas,k[i]^v)[1] )/
                   Bil[i][i] );
        if fail in wt then
            Error("Not all basis vectors of <V> are weight vectors");
        fi;
        pos:= Position( wts, wt );
        if pos = fail then
            Add( wts, wt );
            Add( vecs, [ v ] );
        else
            Add( vecs[pos], v );
        fi;
    od;
    return [ wts, vecs ];
end );



#############################################################################
##
#M   HighestWeightsAndVectors( <V> )
##
InstallMethod( HighestWeightsAndVectors,
        "for a f.d. module over a quantized uea", true,
        [IsAlgebraModule], 0,
        function( V )
    
    local   www,  U,  R,  pos,  ee,  wts,  vecs,  i,  eqs,  j,  b,  v,  
            sol,  lst, eqs1;    
    
    www:= WeightsAndVectors( V );
    
    # for the dominant weights calculate the simultaneous null space
    # of the Ei.
    
    U:= LeftActingAlgebra( V );
    R:= RootSystem( U );
    pos:= List( SimpleSystemNF(R), x -> Position( 
                  PositiveRootsInConvexOrder(R), x ) );
    ee:= List( pos, x -> GeneratorsOfAlgebra( U )[ Length(PositiveRoots(R))+
                 2*Length( CartanMatrix(R) ) + x ] );

    wts:= [ ]; vecs:= [ ];
    
    for i in [1..Length(www[1])] do
        
        if ForAll( www[1][i], x -> x >=0 ) then
            # dominant weight...
            
            eqs:= [ ];
            for j in [1..Length(ee)] do
                
                pos:= Position( www[1], www[1][i]+
                              SimpleRootsAsWeights( R )[j] );
                if pos <> fail then
                    # Otherwise e_j acts as zero anyway.
                    eqs1:= [ ];
                    b:= Basis( VectorSpace( LeftActingDomain(V), 
                                www[2][pos] ), www[2][pos] );
                    for v in www[2][i] do
                        Add( eqs1, Coefficients( b, ee[j]^v ) );
                    od;
                    Append( eqs, TransposedMat( eqs1 ) );
                fi;
            od;
            
            eqs:= TransposedMat( eqs );
            if eqs = [ ] then
                Add( wts, www[1][i] );
                Add( vecs, www[2][i] );
            else
                sol:= NullspaceMat( eqs );
                if sol <> [] then
                    Add( wts, www[1][i] );
                    lst:= [];
                    for v in sol do
                        Add( lst, v*www[2][i] );
                    od;
                    Add( vecs, lst );
                fi;
            fi;
        fi;
    od;
    return [ wts, vecs ];
end );



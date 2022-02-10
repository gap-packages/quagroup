############################################################################
##
#W  tensor.gi                  QuaGroup                     Willem de Graaf
##
##
##  Tensor products of quantized enveloping algebras and their modules.
##


##############################################################################
##
#M  ConvertToNormalFormMonomialElement( <te> ) . . for a tensor qeaPow element
##
InstallMethod( ConvertToNormalFormMonomialElement,
        "for a tensor qeaPow element",
        true, [ IsQEATensorPowElement ], 0,
        function( u )

    local   eu,  fam,  famqea,  tensors,  cfts,  i,  le,  k,  tt,  ei,  
            c,  j,  tt1,  res,  len;

    # We expand every component of every tensor in `u' wrt the 
    # PBW-type basis.

    if u![2] then return u; fi;

    eu:= ExtRepOfObj( u );
    fam:= FamilyObj( u );
    famqea:= fam!.qeaElementsFam;

    # `tensors' will be a list of tensors, i.e., a list of lists
    # of algebra module elements. `cfts' will be the list of their
    # coefficients.

    tensors:= [ ];
    cfts:= [ ];
    for i in [1,3..Length(eu)-1] do
        if eu[i] <> [ ] then #i.e., if it is not the zero tensor
            Add( tensors, eu[i] );
            Add( cfts, eu[i+1] );
        fi;

    od;
    if tensors = [ ] then
        # the thing is zero...
        res:= ObjByExtRep( fam, [ [], fam!.zeroCoefficient ] );
        res![2]:= true;
        return res;
    fi;


    for i in [1..fam!.degree] do

        # in all tensors expand the i-th component

        le:= Length( tensors );
        for k in [1..le] do
            tt:= ShallowCopy( tensors[k] );
            
            ei:= tensors[k][i]![1];
            c:= cfts[k];

            # we replace the tensor on position `k', and add the rest
            # to the end of the list.

            for j in [1,3..Length(ei)-1] do
                tt1:= ShallowCopy( tt );
                tt1[i]:= ObjByExtRep( famqea, [ ei[j], ei[j+1]^0 ] ); 
             
                if j = 1 then
                    tensors[k]:= tt1;
                    cfts[k]:= c*ei[j+1];
                else                    
                    Add( tensors, tt1 );
                    Add( cfts, c*ei[j+1] );
                fi;
            od;
        
            if Length( ei ) = 0  then
                # i.e., the tensor is zero, erase it
                Unbind( tensors[k] );
                Unbind( cfts[k] );
            fi;

        od;
        tensors:= Filtered( tensors, x -> IsBound( x ) );
        cfts:= Filtered( cfts, x -> IsBound( x ) );
    od;

    # Merge tensors and coefficients, take equal tensors together.
    SortParallel( tensors, cfts );
    res:= [ ];
    len:= 0;
    for i in [1..Length(tensors)] do
        if len > 0 and tensors[i] = res[len-1] then
            res[len]:= res[len]+cfts[i];
            if res[len] = 0*res[len] then
                Unbind( res[len-1] );
                Unbind( res[len] );
                len:= len-2;
            fi;
        else
            Add( res, tensors[i] );
            Add( res, cfts[i] );
            len:= len+2;
        fi;
    od;
    if res = [] then res:= [ [], fam!.zeroCoefficient ]; fi;

    res:= ObjByExtRep( fam, res );
    res![2]:= true;
    return res;

end );

############################################################################
##
#M  \*( <qt1>, <qt2> )
#M  OneOp( <qt> )
##
InstallMethod( \*,
        "for qea tensor power elements",
        IsIdenticalObj, [ IsQEATensorPowElement, IsQEATensorPowElement ], 0,
        function( qt1, qt2 )
    
    local   res,  e1,  e2,  i,  j,  mon,  k;
    
    res:= [ ];
    e1:= qt1![1]; e2:= qt2![1];
    for i in [1,3..Length(e1)-1] do
        for j in [1,3..Length(e2)-1] do
            mon:= [ ];
            for k in [1..FamilyObj(qt1)!.degree] do
                Add( mon, e1[i][k]*e2[j][k] );
            od;
            Add( res, mon );
            Add( res, e1[i+1]*e2[j+1] );
        od;
    od;

    res:= ObjByExtRep( FamilyObj( qt1 ), res );
    res![2]:= false;
    return ConvertToNormalFormMonomialElement( res );
    
end);

InstallMethod( OneOp,
        "for a qea tensor Power element",
        true, [ IsQEATensorPowElement ], 0,
        function( qt )        
    
    local   one,  res;    
    
    one:= One( 
      GeneratorsOfAlgebra( FamilyObj( qt )!.qeaElementsFam!.qAlgebra )[1]
               );
    
    res:= ObjByExtRep( FamilyObj( qt ), 
                  [ List( [1..FamilyObj(qt)!.degree], x -> one ), 
                   One( FamilyObj( qt )!.zeroCoefficient ) ] );
    res![2]:= true;
    return res;

end );

############################################################################
##
#M  TensorPower( <U>, <d> )
##
##  returns the d-fold tensor product of U with itself.
##
InstallMethod( TensorPower,
        "for a quantized enveloping algebra and integer",
        true, [ IsQuantumUEA, IsInt ], 0,
        function( QA, deg )

    local   qfam,  F,  fam,  type,  gg,  one,  gens,  i,  j,  g,  T;
    
    # In order to avoid constructing the same tensor powers twice
    # we store them in the elements family of the family of the 
    # quantized enveloping algebra.
    
    qfam:= ElementsFamily( FamilyObj( QA ) );
    if IsBound( qfam!.tensorPowers ) then
        if IsBound( qfam!.tensorPowers[deg] ) then
            return qfam!.tensorPowers[deg];
        fi;
    else
        qfam!.tensorPowers:=[];
    fi;
    
    # We first make the family of the tensor elements, 

    F:= LeftActingDomain( QA );
    
    fam:= NewFamily( "TensorElementsFam", IsQEATensorPowElement );
    type:= NewType( fam, IsMonomialElementRep );
    fam!.monomialElementDefaultType:= type;
    fam!.zeroCoefficient:= Zero( F );
    fam!.qeaElementsFam:= ElementsFamily( FamilyObj( QA ) );
    fam!.degree:= deg;
    
    gg:= GeneratorsOfAlgebra( QA );
    one:= One( gg[1] );
    gens:= [ ];
    for i in [1..deg] do
        for j in [1..Length(gg)] do
            g:= List( [1..deg], x -> one );
            g[i]:= gg[j];  
            Add( gens, g );
        od;
    od;
    
    Sort( gens );

    gens:= List( gens, x -> ObjByExtRep( fam, [ x , One(F) ] ) );
    for i in [1..Length(gens)] do
        gens[i]![2]:= true;
    od;

    T:= AlgebraByGenerators( F, gens );
    SetOne( T, gens[1]^0 );
    qfam!.tensorPowers[deg]:= T;
    return T;

end );

###########################################################################
##
##  DeltaTable( <U>, <d> )
## 
##  returns a list of length 2*s+r, where s is the number of positive
##  roots, and r the rank. This function constructs the d-fold co-products
##  of the generators of <U> (that is, for the F's, and the E's). The first
##  s elements are the co-products of the F-elements, then there are r
##  unbound entries, and then s co-products of the E-elements.
##
QGPrivateFunctions.DeltaTable:= function( QA, deg, gentab )
    
    local   T,  tensorfam,  R,  B,  g,  fam,  sim,  posR,  convR,  
            deltatab,  one,  rank,  s,  i,  pp,  k,  k1,  k2,  pair,  
            rel,  pos,  cf,  qa,  tens,  onet,  t1,  j;

    T:= TensorPower( QA, deg );
    
    # We store the table in the family of tensor elements:
    tensorfam:= ElementsFamily( FamilyObj( T ) );
    if IsBound( tensorfam!.deltaTable ) then
        return tensorfam!.deltaTable;
    fi;
    
    R:= RootSystem( QA );
    B:= BilinearFormMatNF( R );
    g:= GeneratorsOfAlgebra( QA );
    fam:= ElementsFamily( FamilyObj( QA ) );
    sim:= SimpleSystemNF( R );
    
    posR:= PositiveRootsNF( R );
    convR:= fam!.convexRoots;
    deltatab:= [ ];
    one:= One( tensorfam!.zeroCoefficient );

    rank:= Length( CartanMatrix(R) );
    s:= Length( posR );
    
    # first we do the F elements
    
    for i in [1..s] do
        
        pp:= Position( sim, posR[i] );
        if pp <> fail then
            # simple root; copy from gentab
            
            deltatab[ Position( convR, posR[i] ) ]:= gentab[ pp ];

        else
            # find a `definition' for F_{\alpha}

            # find a simple root r such that posR[i]-r is also a root
            for k in [1..Length( sim ) ] do
                k1:= Position( convR, posR[i] - sim[k] );
                if k1 <> fail then
                    k2:= Position( convR, sim[k] );
                    if k1 > k2 then
                        pair:= [ k1, k2 ];
                    else
                        pair:= [ k2, k1 ];
                    fi;     
                    rel:= List( fam!.multTab[pair[1]][pair[2]], ShallowCopy );
                    
                    # see whether F_i is in there...
                    pos:= Position( rel, [ Position( convR, posR[i] ), 1 ] );
                    if pos <> fail then
                        break;
                    fi;
                    
                fi;
            od;

            # F_i is in `rel'; we get it out
            cf:= rel[ pos+1];
            Unbind( rel[pos] ); Unbind( rel[pos+1] );
            rel:= Filtered( rel, x -> IsBound(x) );
        
            for k in [2,4..Length(rel)] do
                rel[k]:= -(1/cf)*rel[k];
            od;
                
            Add( rel, [ pair[1], 1, pair[2], 1 ] );
            Add( rel, 1/cf );
                
            qa:=  _q^( -convR[k1]*( B*convR[k2] ) );
            Add( rel, [ pair[2], 1, pair[1], 1 ] );
            Add( rel, -qa/cf );
            
            # Now apply delta to the elements of rel, and add...

            tens:= Zero( T );
            onet:= One( tens );
            
            for k in [1,3..Length(rel)-1] do
                t1:= onet;
                for j in [1,3..Length(rel[k])-1] do
                    qa:= GaussianFactorial( rel[k][j+1], 
                         _q^(convR[rel[k][j]]*( B*convR[rel[k][j]] )/2) );
                    t1:=(1/qa)*t1*( deltatab[rel[k][j]]^rel[k][j+1] );
                od;
                tens:= tens+rel[k+1]*t1;
            od;
            
            deltatab[ Position( convR, posR[i] ) ]:= tens;

        fi;
        
    od;
    
    # Add K-elements from gentab: 
    Append( deltatab, gentab{[rank+1..3*rank]} );
    
    # then  we do the E elements
    
    for i in [1..s] do
        
        pp:= Position( sim, posR[i] );
        if pp <> fail then
            # simple root; copy from gentab
            
            deltatab[s+2*rank+Position( convR, posR[i] )]:= 
                                gentab[ 3*rank+pp ];

        else
            # find a `definition' for E_{\alpha}

            # find a simple root r such that posR[i]-r is also a root
            for k in [1..Length( sim ) ] do
                k1:= Position( convR, posR[i] - sim[k] );
                if k1 <> fail then
                    k2:= Position( convR, sim[k] );
                    
                    if k1 > k2 then
                        pair:= [ s+rank+k1, s+rank+k2 ];
                    else
                        pair:= [ s+rank+k2, s+rank+k1 ];
                    fi;
                    
                    rel:= List( fam!.multTab[pair[1]][pair[2]], ShallowCopy );
                    # See whether E_i is in rel:
                    pos:= Position( rel, [ Position( convR, posR[i] )+s+rank, 
                                  1 ] );
                    if pos <> fail then
                        break;
                    fi;
                fi;
            od;
            
            
            # E_i is in `rel'; we get it out
            cf:= rel[ pos+1];
            Unbind( rel[pos] ); Unbind( rel[pos+1] );
            rel:= Filtered( rel, x -> IsBound(x) );
        
            for k in [2,4..Length(rel)] do
                rel[k]:= -(1/cf)*rel[k];
            od;
                
            Add( rel, [ pair[1], 1, pair[2], 1 ] );
            Add( rel, 1/cf );
                
            qa:=  _q^( -convR[k1]*( B*convR[k2] ) );
            Add( rel, [ pair[2], 1, pair[1], 1 ] );
            Add( rel, -qa/cf );
            
            # Apply delta to rel...

            tens:= Zero( T );
            onet:= One( tens );
            
            for k in [1,3..Length(rel)-1] do
                t1:= onet;
                for j in [1,3..Length(rel[k])-1] do
                    qa:= GaussianFactorial( rel[k][j+1], 
        _q^(convR[rel[k][j]-s-rank]*( B*convR[rel[k][j]-s-rank] )/2) );
                    t1:=(1/qa)*t1*( deltatab[rel[k][j]+rank]^rel[k][j+1] );
                od;
                tens:= tens+rel[k+1]*t1;
            od;

            deltatab[ s+2*rank+Position( convR, posR[i] ) ]:= tens;

        fi;
        
    od;
    
    tensorfam!.deltaTable:= deltatab;
    
    return deltatab;
            
end;

QGPrivateFunctions.make_generic_comulmap:= function( arg )


    local   U,  d,  twisting,  f,  finv,  T,  tfam,  one,  R,  rank,  
            s,  posR,  g,  gens,  i,  p,  fgens,  nice,  x,  tens,  j,  
            ten,  dt,  map,  images,  noPosR,  tendeg,  imgs;

    U:= arg[1];
    d:= arg[2];
    if Length( arg ) = 2 then
        twisting:= false;
    else
        twisting:= true;
        f:= arg[3];
        finv:= arg[4];
    fi;
    
    T:= TensorPower( U, d );
    
    tfam:= ElementsFamily( FamilyObj( T ) );
    one:= One( tfam!.zeroCoefficient );

    R:= RootSystem( U );
    rank:= Length( CartanMatrix(R) );
    s:= Length( PositiveRoots(R) );
    posR:= PositiveRootsInConvexOrder( R );
    
    g:= GeneratorsOfAlgebra( U );
    gens:= [ ];
    for i in [1..rank] do
        p:= Position( posR, SimpleSystemNF( R )[i] );
        gens[i]:= g[ p ];
        gens[ rank+i ]:= g[ s + 2*i -1 ];
        gens[ 2*rank + i ]:= g[ s+2*i ];
        gens[ 3*rank + i ]:= g[ s+2*rank + p ];
    od;
        
    if twisting then
        # we check whether f maps generators to generators;
        # in that case we can make the table directly,
        # otherwise we need to make a standard table first,
        # and then map it with f.
        
        fgens:=  [ ];
        nice:= true;
        for i in gens do
            
            x:= Image( f, i );
            p:= Position( gens, x );
            if p = fail then
  
                nice:= false;
                break;
            else
                
                if p <= rank then
                    # an F
                    tens:= [ ];
                    for j in [1..d] do
                        ten:= List( [1..j], x -> One(g[1]) );
                        Append( ten, List( [j+1..d],  x -> g[s+2*p] ) );
                        ten[j]:= x;
                        Add( tens, ten ); Add( tens, one );
                    od;
                elif p <= 2*rank then
                    # a K
                    p:= p-rank;
                    tens:= [ List([1..d], ii -> g[s+2*p-1] ),
                            QuantumParameter(U)^0 ];
                elif p <= 3*rank then
                    # a K^-1
                    p:= p-2*rank;
                    tens:= [ List([1..d], ii -> g[s+2*p] ),
                            QuantumParameter(U)^0 ];
                else
                    # an E
                    p:= p-3*rank;
                    tens:= [ ];
                    for j in [1..d] do
                        ten:= List( [1..j], x -> g[s+2*p-1] );
                        Append( ten, List( [j+1..d],  x -> One(g[1]) ) );
                        ten[j]:= x;
                        Add( tens, ten ); Add( tens, one );
                    od;
                fi;  
                    
                Add( fgens, tens );
            fi;
        od;
        
        if nice then
            # apply f<x>f<x>...<x>f
            for i in [1..Length(fgens)] do
                for j in [1,3..Length(fgens[i])-1] do
                    fgens[i][j]:= List( fgens[i][j], uu -> Image( f, uu ) );
                od;
                fgens[i]:= ObjByExtRep( tfam, fgens[i] );
                fgens[i]![2]:= false;
                fgens[i]:= ConvertToNormalFormMonomialElement(fgens[i]);
            od;
        fi;    
    fi;
    
    if not twisting or not nice then
        # we make the `standard' table.
        fgens:= [ ];
        for p in [1..rank] do
            tens:= [ ];
            for j in [1..d] do
                ten:= List( [1..j], x -> One(g[1]) );
                Append( ten, List( [j+1..d],  x -> g[s+2*p] ) );
                ten[j]:= g[ Position( posR, SimpleSystemNF(R)[p] ) ];
                Add( tens, ten ); Add( tens, one );
            od;
            Add( fgens, tens );
        od;
        for p in [1..rank] do
            tens:= [ List([1..d], ii -> g[s+2*p-1] ),
                    QuantumParameter(U)^0 ];
            Add( fgens, tens );
        od;
        for p in [1..rank] do
            tens:= [ List([1..d], ii -> g[s+2*p] ),
                     QuantumParameter(U)^0 ];
            Add( fgens, tens );
        od;
        for p in [1..rank] do
            tens:= [ ];
            for j in [1..d] do
                ten:= List( [1..j], x -> g[s+2*p-1] );
                Append( ten, List( [j+1..d],  x -> One(g[1]) ) );
                ten[j]:= g[ s+2*rank + Position( posR, SimpleSystemNF(R)[p] ) ];
                Add( tens, ten ); Add( tens, one );
            od;            
            Add( fgens, tens );
        od;

        for i in [1..Length(fgens)] do
            fgens[i]:= ObjByExtRep( tfam, fgens[i] );
            fgens[i]![2]:= false;
            fgens[i]:= ConvertToNormalFormMonomialElement(fgens[i]);
        od;
    fi;
    
    dt:= QGPrivateFunctions.DeltaTable( U, d, fgens );

    map:= Objectify( TypeOfDefaultGeneralMapping( U, T,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericCoMultMap
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := dt,
                      rank:= rank,
                      noPosR:= s,
                      tendeg:= d
                      ) );
    
    if twisting and not nice then

        imgs:= [ ];
        for i in [1..s] do
            Add( imgs, Image( map, Image( finv, g[i] ) ) );
        od;
        for i in [1..rank] do
            Add( imgs, Image( map, Image( finv, g[s+2*i-1] ) ) );
        od;
        for i in [1..rank] do
            Add( imgs, Image( map, Image( finv, g[s+2*i] ) ) );
        od;
        for i in [1..s] do
            Add( imgs, Image( map, Image( finv, g[s+2*rank+i] ) ) );
        od;

        for i in [1..Length(imgs)] do
            # apply f<x>f...<x>f (d-factors).

            x:= ShallowCopy( imgs[i]![1] );
            ten:= [ ];
            for j in [1,3..Length(x)-1] do
                Add( ten, List( x[j], e -> Image( f, e ) ) );
                Add( ten, x[j+1] );
            od;
            ten:= ObjByExtRep( tfam, ten );
            ten![2]:= false;

            imgs[i]:=ConvertToNormalFormMonomialElement(ten);
        od;
        
        map:= Objectify( TypeOfDefaultGeneralMapping( U, T,
                      IsSPGeneralMapping
                      and IsAlgebraGeneralMapping
                      and IsGenericCoMultMap
                      and IsAlgebraHomomorphism),
                      rec(
                          images  := imgs,
                          rank:= rank,
                          noPosR:= s,
                          tendeg:= d
                          ) );
    fi;
    return map;
end;


InstallOtherMethod( ComultiplicationMap,
        "for a quea, and degree", true, [IsGenericQUEA,IsInt], 0,
        function( U, d )
    
    local   fam,  map;
    
    fam:= FamilyObj( U );
    
    if not IsBound( fam!.coMaps ) then fam!.coMaps:= [ ]; fi;
    if IsBound( fam!.coMaps[d] ) then return fam!.coMaps[d]; fi;

    if HasHopfStructureTwist( U ) then
        map:= QGPrivateFunctions.make_generic_comulmap( U, d, 
                            HopfStructureTwist( U )[1], 
                            HopfStructureTwist( U )[2] );
    else
        map:= QGPrivateFunctions.make_generic_comulmap( U, d );
    fi;
    
    fam!.coMaps[d]:= map;
    return map;

end );


InstallOtherMethod( ComultiplicationMap,
        "for a quea, and degree", true, [IsQuantumUEA,IsInt], 0,
        function( U, d )
    
    local   T,  fam,  U0, f, map;

    if IsGenericQUEA( U ) then TryNextMethod(); fi;
    
    fam:= FamilyObj( U );
    if not IsBound( fam!.coMaps ) then fam!.coMaps:= [ ]; fi;
    if IsBound( fam!.coMaps[d] ) then return fam!.coMaps[d]; fi;

    U0:= QuantizedUEA( RootSystem(U) );
    if HasHopfStructureTwist( U ) then
        f:= QGPrivateFunctions.make_generic_comulmap( U0, d,
                            HopfStructureTwist( U )[1]!.origMap, 
                            HopfStructureTwist( U )[2]!.origMap );
    else
        f:= QGPrivateFunctions.make_generic_comulmap( U0, d );
    fi;

    T:= TensorPower( U, d );
    map:= Objectify( TypeOfDefaultGeneralMapping( U, T,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsInducedCoMultMap
                  and IsAlgebraHomomorphism),
                  rec(
                      origMap:= f,
                      canMap:= CanonicalMapping( U ),
                      tendeg:= d
                      ) );    
    
    fam!.coMaps[d]:= map;
    return map;

end );



InstallMethod( PrintObj,
        "for a comultmap", true, [ IsCoMultMap ], 0,
        function( map )
    
    Print("<Comultiplication of ",Source(map),", degree ",map!.tendeg,">");
end );

# The code below is literally taken from isom.gi. It turned out to 
# be rather tricky to change the code for automorphisms, so as to allow
# more general homomorphisms, such as \Delta : U ---> U<x>...<x>U.
# This was basically caused by the fact that elements of U have a 
# special format, which is used heavily throughout the programs.
# Therefore we redo it for this special case (comult).

InstallMethod( ImageElm,
        "for comult map, and elm",
        true, [ IsGenericCoMultMap, IsQEAElement ], 0,
        function( map, x )

    local rew_K, ex, U, B, R, posR, sim, noposR, rank, i, j, im, u, qp, T;

    rew_K:= function( a, b, delta, s, qpar )

         local res, i;

         res:= a^delta;
         for i in [1..s] do
            res:= res*( qpar^(-i+1)*a-qpar^(i-1)*b )/( qpar^i-qpar^-i );
         od;
         return res;
    end;
    
    ex:= ExtRepOfObj( x );
    U:= Source( map );
    T:= Range( map );
    R:= RootSystem( U );
    B:= BilinearFormMatNF( R );
    posR:= PositiveRootsInConvexOrder( R );
    sim:= SimpleSystemNF( R );
    noposR:= map!.noPosR;
    rank:= map!.rank;
    
    im:= Zero( T );
    for i in [1,3..Length(ex)-1] do
        u:= ex[i+1]*One( T );
        for j in [1,3..Length(ex[i])-1] do
            if IsList( ex[i][j] ) then 
                #it is a K...; more difficult.
                qp:= _q^( sim[ ex[i][j][1]-noposR ]*( B*sim[ ex[i][j][1]-noposR ] )/2);
                u:= u*rew_K( map!.images[ ex[i][j][1] ], 
                             map!.images[ ex[i][j][1]+map!.rank ], ex[i][j][2], 
                             ex[i][j+1], qp );
            elif ex[i][j] <= map!.noPosR then
                #it is an F...
                qp:= _q^( posR[ ex[i][j] ]*( B*posR[ ex[i][j] ] )/2 );
                u:= u*( map!.images[ ex[i][j] ]^ex[i][j+1] )/
                   GaussianFactorial( ex[i][j+1], qp );
            else
                #it is an E...
                qp:= _q^( posR[ ex[i][j]-noposR-rank ]*( 
                                    B*posR[ ex[i][j]-noposR-rank ] )/2 );
  
                u:= u*( map!.images[ ex[i][j]+rank ]^ex[i][j+1] )/
                   GaussianFactorial( ex[i][j+1], qp );
            fi;
        od;
        im:= im+u;
    od;

    return im;

end );

InstallMethod( ImageElm,
        "for induced comult map, and elm",
        true, [ IsInducedCoMultMap, IsQEAElement ], 0,
        function( map, x )

        local U, T, qp, U0, f0, im, ex, canmap, i, j, y, tn;

        U:= Source( map );
        T:= Range( map );
        qp:= QuantumParameter( U );
        U0:= QuantizedUEA( RootSystem( U ) );
        f0:= map!.origMap;
        im:= Zero( T );
        ex:= ExtRepOfObj( x );

        canmap:= map!.canMap;

        for i in [1,3..Length(ex)-1] do
            y:= ObjByExtRep( ElementsFamily(FamilyObj(U0)), [ ShallowCopy(ex[i]), 
                    QuantumParameter(U0)^0 ] );
            tn:= ShallowCopy( ExtRepOfObj( Image( f0, y ) ) );
            for j in [2,4..Length(tn)] do
                tn[j]:= Value( tn[j], qp )*ex[i+1];
                if IsZero( tn[j] ) then
                   Unbind( tn[j] ); Unbind(tn[j-1]);
                else
                   tn[j-1]:= List( tn[j-1], x -> Image( canmap, x ) );
                fi;
            od;
            tn:= Filtered( tn, x -> IsBound(x) );
            im:= im + ObjByExtRep( ElementsFamily(FamilyObj(T)), tn );
        od;
        return im;
end );




##############################################################################
##
#M  TensorProductOfAlgebraModules( <list> )
##
##  constructs the tensor product of left modules over quantized uea.
##
InstallMethod( TensorProductOfAlgebraModules,
        "for a list of quantum algebra modules",
        true, [ IsDenseList ], 100,
        function( list )
#+    
#+  constructs the tensor product of left modules over quantized uea.
#+  <list> must be a list of left modules over the same quantized 
#+  enveloping algebra. `TensorProductOfAlgebraModules( <V>, <W> )'    
#+  is short for   `TensorProductOfAlgebraModules( [ <V>, <W> ] )'.  
    
    
    local   left_quantum_action_generic,  A,  VT,  dtab,  delta,  s,  rank,  
            g,  i,  Tprod,  wlist,  wts,  vecs,  ei,  wt,  j,  pos, 
            left_quantum_action_induced;
    
    # The following is a function that takes an element from the qea, and an
    # element from the tensor product. It returns the result of letting
    # x act on tn.
    
left_quantum_action_generic:= function( x, tn )

    # When everyting is defined over Q(q). `x' is the algebra elt, tn is an element
    # of the tensor product of modules.
    
    local   R,  noPosR,  rank,  B,  deg,  delta,  res,  ex,  etn,  i,  
            vec,  len,  j,  rule,  k,  vec1,  u,  v,  ind,  cf,  ka,  
            tv,  pos,  d;
    
    if tn = 0*tn then 
        return tn;
    fi;
    
    R:= FamilyObj(x)!.rootSystem;
    noPosR:= Length( PositiveRoots(R) );
    rank:= Length( CartanMatrix(R) );
    B:= BilinearFormMatNF( R );
    
    deg:= FamilyObj( tn )!.degree;
    delta:= FamilyObj( tn )!.deltaTab;
    d:= FamilyObj( tn )!.deltaMap;

    res:= [ ];  # result
    ex:= ExtRepOfObj( x );
    etn:= ExtRepOfObj( tn );
    
    for i in [1,3..Length(ex)-1] do

        # apply ex[i] to etn
        
        vec:= List( etn, ShallowCopy );
        len:= Length( ex[i] );
        for j in [len-1,len-3..1] do

            if not IsList( ex[i][j] )  then

                # It is an E or an F...
                rule:= delta[ ex[i][j] ];
                for k in [1..ex[i][j+1]] do
        
                    # we apply rule to all tensors in vec, and collect
                    # everything in vec1
                    vec1:= [ ]; 
                    for u in [1,3..Length(vec)-1] do
                        for v in [1,3..Length(rule)-1] do
                            Add(vec1, 
                    List( [1..Length(vec[u])], x -> rule[v][x]^vec[u][x]) );
                            Add( vec1, vec[u+1]*rule[v+1] );
                        od;
                    od;
                    vec:= vec1;
                od;
                # take into account that F_1^(k) = F_i^k/[k]!
                if ex[i][j] <= noPosR then
                    ind:= LongestWeylWord(R)[ ex[i][j] ];
                else
                    ind:= LongestWeylWord(R)[ ex[i][j]-noPosR-rank ];
                fi;
                cf:= GaussianFactorial( ex[i][j+1], _q^(B[ind][ind]/2) );
                for k in [2,4..Length(vec)] do
                    vec[k]:= vec[k]/cf;
                od;
                
            else
                # it is a `K'; we take the image under d... (I know nothing better).
                ka:= ObjByExtRep( FamilyObj(x), [ 
                             [ ex[i][j], ex[i][j+1] ], ex[i+1]^0] );
                rule:= ExtRepOfObj( Image( d, ka ) );

                # we apply rule to all tensors in vec, and collect
                # everything in vec1
                vec1:= [ ]; 
                for u in [1,3..Length(vec)-1] do
                    for v in [1,3..Length(rule)-1] do
                        Add(vec1, 
                List( [1..Length(vec[u])], x -> rule[v][x]^vec[u][x]) );
                        Add( vec1, vec[u+1]*rule[v+1] );
                    od;
                od;
                vec:= vec1;

            fi;
            
            # intermediate normalization...
            tv:= ObjByExtRep( FamilyObj(tn), vec );
            tv![2]:= false;
            tv:= ConvertToNormalFormMonomialElement(tv);
            vec:= ShallowCopy( tv![1] );
        od;
        vec:= ShallowCopy( vec );
        for k in [2,4..Length(vec)] do
            vec[k]:= ex[i+1]*vec[k];
        od;

        # add vec to `res'
        for k in [1,3..Length(vec)-1] do
            pos:= Position( res, vec[k] );
            if pos = fail then
                Add( res, vec[k] ); Add( res, vec[k+1] );
            else
                res[pos+1]:= res[pos+1]+vec[k+1];
                if res[pos+1] = 0*res[pos+1] then
                    Unbind( res[pos] ); Unbind( res[pos+1] );
                    res:= Filtered( res, x -> IsBound(x) );
                fi;
            fi;
        od;
        
    od;

    tv:= ObjByExtRep( FamilyObj(tn), res );
    tv![2]:= false;
    tv:= ConvertToNormalFormMonomialElement(tv);

    return tv;
end;


left_quantum_action_induced:= function( x, tn )

    # When the quantum parameter is not `q'. `x' is the algebra elt, tn is an element
    # of the tensor product of modules.
    
    local   res,  ex,  etn,  i,  
            vec,  len,  j,  rule,  k,  vec1,  u,  v,  ind,  cf,  
            tv,  pos,  d;
    
    if tn = 0*tn then 
        return tn;
    fi;
    
    d:= FamilyObj( tn )!.deltaMap;

    res:= [ ];  # result
    ex:= ExtRepOfObj( x );
    etn:= ExtRepOfObj( tn );
    
    for i in [1,3..Length(ex)-1] do

        # apply ex[i] to etn
        
        vec:= List( etn, ShallowCopy );
        len:= Length( ex[i] );
        for j in [len-1,len-3..1] do

            rule:= ExtRepOfObj( Image( d, ObjByExtRep( FamilyObj(x), 
                                              [ [ ex[i][j], ex[i][j+1] ], ex[i+1]^0] ) ) );

            # we apply rule to all tensors in vec, and collect
            # everything in vec1
            vec1:= [ ]; 
            for u in [1,3..Length(vec)-1] do
                for v in [1,3..Length(rule)-1] do
                    Add(vec1, 
                       List( [1..Length(vec[u])], x -> rule[v][x]^vec[u][x]) );
                    Add( vec1, vec[u+1]*rule[v+1] );
                od;
            od;
            vec:= vec1;
            
            # intermediate normalization...
            tv:= ObjByExtRep( FamilyObj(tn), vec );
            tv![2]:= false;
            tv:= ConvertToNormalFormMonomialElement(tv);
            vec:= ShallowCopy( tv![1] );
        od;
        vec:= ShallowCopy( vec );
        for k in [2,4..Length(vec)] do
            vec[k]:= ex[i+1]*vec[k];
        od;

        # add vec to `res'
        for k in [1,3..Length(vec)-1] do
            pos:= Position( res, vec[k] );
            if pos = fail then
                Add( res, vec[k] ); Add( res, vec[k+1] );
            else
                res[pos+1]:= res[pos+1]+vec[k+1];
                if res[pos+1] = 0*res[pos+1] then
                    Unbind( res[pos] ); Unbind( res[pos+1] );
                    res:= Filtered( res, x -> IsBound(x) );
                fi;
            fi;
        od;
        
    od;

    tv:= ObjByExtRep( FamilyObj(tn), res );
    tv![2]:= false;
    tv:= ConvertToNormalFormMonomialElement(tv);

    return tv;
end;


    # Now we make the tensor module.

    if not HasLeftActingAlgebra( list[1] ) then
       TryNextMethod();
    fi;

    A:= LeftActingAlgebra( list[1] );
    if not ForAll( [2..Length(list)], x -> LeftActingAlgebra(list[x])=A) then
        Error( "All modules must have the same acting algebra");
    fi; 
    if not IsQuantumUEA(A) then
        TryNextMethod();
    fi;
    
    VT:= TensorProduct( list );
    ElementsFamily( FamilyObj(VT) )!.degree:= Length(list);
    dtab:= ComultiplicationMap( A, Length(list) );
    ElementsFamily( FamilyObj( VT ) )!.deltaMap:= dtab;

    if IsGenericCoMultMap( dtab ) then 
       delta:= [ ];
       s:= dtab!.noPosR;
       rank:= dtab!.rank;
       g:= GeneratorsOfAlgebra( A );
       for i in [1..s] do
           delta[i]:= ExtRepOfObj( Image( dtab, g[i] ) );
           delta[s+rank+i]:= ExtRepOfObj( Image( dtab, g[s+2*rank+i] ) );
       od;
    
       ElementsFamily( FamilyObj( VT ) )!.deltaTab:= delta;    
       Tprod:= LeftAlgebraModule( A, left_quantum_action_generic, VT );
    else
       Tprod:= LeftAlgebraModule( A, left_quantum_action_induced, VT );
    fi;

    # Set the attribute `WeightsAndVectors', if each element
    # in the list has this attribute set.
    if ForAll( list, HasWeightsAndVectors ) then

        rank:= Length( CartanMatrix( RootSystem( 
                         LeftActingAlgebra(list[1]) ) ) );
        
        wlist:= List( list, x -> WeightsAndVectors(x) );
        wts:= [ ];
        vecs:= [ ];
        for i in Basis(Tprod) do
            ei:= ExtRepOfObj( ExtRepOfObj( i ) )[1];
            wt:= [1..rank]*0;
            for j in [1..Length(ei)] do
                pos:= PositionProperty( wlist[j][2], x -> ei[j] in x );
                wt:= wt + wlist[j][1][pos];
            od;
            
            pos:= Position( wts, wt );
            if pos = fail then
                Add( wts, wt );
                Add( vecs, [ i ] );
            else
                Add( vecs[pos], i );
            fi;
        od;
        SetWeightsAndVectors( Tprod, [ wts, vecs ] );
    fi;
    
    return Tprod;

end );


InstallMethod( UseTwistedHopfStructure,
        "for a quea, and an (anti-)automorphism", true,
        [ IsQuantumUEA, IsAlgebraHomomorphism, IsAlgebraHomomorphism ], 0,
        function( U, f, finv )

    if (not IsQUEAAutomorphism( f )) and (not IsQUEAAntiAutomorphism( f )) then
        Error("<f> must be an (anti-)automorphism");
    fi;
    if not IsIdenticalObj( U, Source(f) ) then
        Error("<f> is a homomorphism of the wrong algebra");
    fi;
    SetHopfStructureTwist( U, [ f, finv ] );
end );

       
InstallMethod( AntipodeMap,
        "for a qea", true, [ IsQuantumUEA ], 0,
        
        function( U )
    
    local   U0,  g,  R,  sim,  posR,  s,  rank,  imgs,  i,  pos,  S, antiaut;
    
    # Here we use the anti-automorphism S defined by 
    # S(E) = -K^-1E, S(F) = -FK, S(K) = K^-1. Its inverse is given by
    # S^-1(E) = -EK^-1, S^-1(F) = -KF, S^-1(K) = K^-1.
    # 
    # If the Hopf structure is non-twisted the antipode is S.
    # Otherwise, if it is twisted by an automorphism f, the antipode is
    # f*S*f^-1, and if it is twisted by an antiautomorphism f, then 
    # the antipode is f*S^-1*f^-1.
    
    # We first construct the antipode of the corresponding generic
    # quea:
    if IsGenericQUEA( U ) then
        U0:= U;
    else
        U0:= QuantizedUEA( RootSystem( U ) );
    fi;
    
    if HasHopfStructureTwist( U ) then
        if IsQUEAAutomorphism( HopfStructureTwist( U )[1] ) then
            antiaut:= false;
        else
            antiaut:= true;
        fi;
    else
        antiaut:= false;
    fi;
    
    g:= GeneratorsOfAlgebra( U0 );
    R:= RootSystem( U0 );
    sim:= SimpleSystemNF( R );
    posR:= PositiveRootsInConvexOrder( R );
    s:= Length( posR );
    rank:= Length( sim );
    imgs:= [ ];
    
    if not antiaut then
        
        # We construct S:
        for i in [1..rank] do
            pos:= Position( posR, sim[i] );
            imgs[i]:= -g[pos]*g[s+2*i-1];
            imgs[3*rank+i]:= -g[s+2*i]*g[s+2*rank+pos];
            imgs[rank+i]:= g[s+2*i];
            imgs[2*rank+i]:= g[s+2*i-1];
        od;
        S:= QEAAntiAutomorphism( U0, imgs );
        if not IsGenericQUEA( U ) then
            S:= QEAAntiAutomorphism( U, S );
        fi;
        
    else
        
        # We construct S^-1 (which we also call S):
        for i in [1..rank] do
            pos:= Position( posR, sim[i] );
            imgs[i]:= -g[s+2*i-1]*g[pos];
            imgs[3*rank+i]:= -g[s+2*rank+pos]*g[s+2*i];
            imgs[rank+i]:= g[s+2*i];
            imgs[2*rank+i]:= g[s+2*i-1];
        od;
        S:= QEAAntiAutomorphism( U0, imgs );
        if not IsGenericQUEA( U ) then
            S:= QEAAntiAutomorphism( U, S );
        fi;
        
    fi;
    
    if HasHopfStructureTwist( U ) then
        return HopfStructureTwist( U )[1]*S*HopfStructureTwist( U )[2];
    else
        return S;
    fi;  
    
end );


InstallMethod( CounitMap,
        "for a qea", true, [ IsQuantumUEA ], 0,
        
        function( U )
    
    local   F,  e;
    
    F:= LeftActingDomain( U );
    e:= function( u )
        
        local   eu,  res,  i,  a,  j;
        
        eu:= ExtRepOfObj( u );
        res:= Zero(F);
        for i in [1,3..Length(eu)-1] do
            if IsList( eu[i][1] ) and IsList( eu[i][ Length(eu[i])-1 ] ) then
                # begins and ends with K; possibly nonzero image.
                a:= One( F );
                for j in [1,3..Length(eu[i])-1] do
                    if eu[i][j+1] > 0 then
                        a:= 0*a;
                        break;
                    fi;
                od;
                res:= eu[i+1]*a+res;
            fi;
        od;
        return res;
    end;
    
    if HasHopfStructureTwist( U ) then
        
        return function( u ) return e( 
                              Image( HopfStructureTwist( U )[2], u ) );
               end;
    else
        return e;
    fi;
    
end );

# linear functionals know two things: a list of vecs, cfs giving the 
# function as a lin comb of indicator functions, and a basis, stuck in
# the family; all evcs appearing in the list *must* be basis vecs.

InstallMethod( ObjByExtRep,
        "make a dual element", true, 
        [ IsDualElementFamily, IsList ], 0,
        function( fam, list )
    local m;
    
    m:= Objectify( fam!.packedType, rec( val:=Immutable(list) ) );
    SetSource( m, fam!.source );
    SetRange( m, fam!.range );
    return m;
    
end );

InstallMethod( ExtRepOfObj,
        "for a dual element", true,
        [ IsDualElement ], 0, 
        function( d ) 
    return d!.val; 
end );
        

InstallMethod( PrintObj,
        "for dual elements", true, [ IsDualElement ], 0,
        function( df )
    
    local   ed,  i;
    
    ed:= ExtRepOfObj( df );
    if ed = [ ] then Print( "<zero function>" ); fi;
    for i in [1,3..Length(ed)-1] do
        if i > 1 then Print(" + "); fi;
        Print("(",ed[i],")*F@",ed[i+1]);
    od;
end );

#############################################################################
##
##  Spaces of elements of a dual space are handled by nice bases;
##  we use sparse vectors for that.
##
InstallHandlingByNiceBasis( "IsDualElementsSpace", rec(
    detect:= function( R, gens, V, zero )
      return IsDualElementCollection( V );
      end,

    NiceFreeLeftModuleInfo := ReturnFalse,

    NiceVector := function( V, v )
          local   ev,  nums,  cfs,  B,  i,  vec;

          ev:= ExtRepOfObj( v );
          nums:= [ ]; cfs:= [ ];
          B:= FamilyObj( v )!.basisV;
          
          for i in [1,3..Length(ev)-1] do
              Add( nums, Position( B, ev[i+1] ) );
              Add( cfs, ev[i] );
          od;
          SortParallel( nums, cfs );
          vec:= [ ];
          for i in [1..Length(nums)] do
              Add( vec, nums[i] ); Add( vec, cfs[i] );
          od;
          
          return ObjByExtRep( FamilyObj( v )!.niceVectorFam, vec );
      end,

    UglyVector := function( V, vec )
          local   ev,  vv,  cfs,  B,  i,  m;

          # We do the inverse of `NiceVector'.
          ev:= ShallowCopy( vec![1] );
          vv:= [ ]; cfs:= [ ];
          B:= ElementsFamily( FamilyObj( V ) )!.basisV;
          for i in [1,3..Length(ev)-1] do 
              Add( cfs, ev[i+1] );
              Add( vv, B[ ev[i] ] );
          od;
          
          SortParallel( vv, cfs );
          m:= [ ];
          for i in [1..Length(vv)] do
              Add( m, cfs[i] );
              Add( m, vv[i] );
          od;
          
          return ObjByExtRep(  ElementsFamily( FamilyObj( V ) ), m );
      end ) );
      
InstallMethod( DualSpace, 
        "for a vector space", true, [ IsLeftModule ], 0,        
        function( V )
        
    local   fam,  type,  niceVF,  B,  vecs,  one,  v;
    
    fam:= NewFamily( "DualEltsFam", IsDualElement );
    type:= NewType( fam, IsAttributeStoringRep );
    fam!.packedType:= type;
    fam!.source:= V;
    fam!.range:= LeftActingDomain( V );
    SetFamilySource( fam, ElementsFamily( FamilyObj( V ) ) );
    
    niceVF:= NewFamily( "NiceVectorFam", IsSparseRowSpaceElement );
    niceVF!.zeroCoefficient:= Zero( LeftActingDomain(V) );
    niceVF!.sparseRowSpaceElementDefaultType:=
                    NewType( niceVF, IsPackedElementDefaultRep );
    fam!.niceVectorFam:= niceVF;
    
    B:= Basis( V );
    fam!.basisV:= B;
    vecs:= [ ];
    one:= One( LeftActingDomain( V ) );
    for v in B do
        Add( vecs, ObjByExtRep( fam, [ one, v ] ) );
    od;
    fam!.basisVdual:= vecs;
    return VectorSpace( LeftActingDomain(V), vecs, "basis" );
    
end );


InstallMethod( \+,
        "for two dual elements", IsIdenticalObj,
        [ IsDualElement, IsDualElement ], 0,
        function( d1, d2 )
    
    local   e1,  e2,  m1,  c1,  m2,  c2,  i,  pos,  e;
    
    e1:= ExtRepOfObj( d1 );
    
    # Catch trivial case:
    if e1=[] then return d2; fi;
    
    e2:= ExtRepOfObj( d2 );
    m1:= e1{[2,4..Length(e1)]};
    c1:= e1{[1,3..Length(e1)-1]};
    m2:= e2{[2,4..Length(e2)]};
    c2:= e2{[1,3..Length(e2)-1]};

    for i in [1..Length( m2 )] do
        pos:= PositionSorted( m1, m2[i] );
        
        if pos > Length( m1 ) then
            Add( m1, m2[i] );
            Add( c1, c2[i] );
        else

            if m1[pos] = m2[i] then
                c1[pos]:= c1[pos]+c2[i];
                if c1[pos] = 0*c1[pos] then
                    Unbind( c1[pos] );
                    Unbind( m1[pos] );
                    m1:= Filtered( m1, x -> IsBound(x) );
                    c1:= Filtered( c1, x -> IsBound(x) );
                fi;                
            else
                InsertElmList( m1, pos, m2[i] );
                InsertElmList( c1, pos, c2[i] );
            fi;
        fi;
    od;

    e:= [ ];
    for i in [1..Length(m1)] do
        Add( e, c1[i] );
        Add( e, m1[i] );
    od;
    return ObjByExtRep( FamilyObj( d1 ), e );
end );


InstallMethod( \*,
        "for a scalar and a dual elt", true,
        [ IsScalar, IsDualElement ], 0,
        function( a, d )
        
    local   ed,  i;
    
    if IsZero( a ) then return Zero( d ); fi;
    ed:= ShallowCopy( ExtRepOfObj( d ) );
    for i in [1,3..Length(ed)-1] do
        ed[i]:= a*ed[i];
    od;
    return ObjByExtRep( FamilyObj( d ), ed );
end );

InstallMethod( \*,
        "for a dual elt and a scalar", true,
        [ IsDualElement, IsScalar ], 0,
        function( d, a )
        
    local   ed,  i;
    
    if IsZero( a ) then return Zero( d ); fi;
    ed:= ShallowCopy( ExtRepOfObj( d ) );
    for i in [1,3..Length(ed)-1] do
        ed[i]:= ed[i]*a;
    od;
    return ObjByExtRep( FamilyObj( d ), ed );
end );


InstallMethod( AdditiveInverseSameMutability,
        "for a dual element", true,
        [ IsDualElement ], 0,
        function( d )
        
    local   ed,  i;
        
    ed:= ShallowCopy( ExtRepOfObj( d ) );
    for i in [1,3..Length(ed)-1] do
        ed[i]:= -ed[i];
    od;
    return ObjByExtRep( FamilyObj( d ), ed );
end );

InstallMethod( AdditiveInverseMutable,
        "for a dual element", true,
        [ IsDualElement ], 0,
        function( d )
        
    local   ed,  i;
        
    ed:= ShallowCopy( ExtRepOfObj( d ) );
    for i in [1,3..Length(ed)-1] do
        ed[i]:= -ed[i];
    od;
    return ObjByExtRep( FamilyObj( d ), ed );
end );

InstallMethod( ZeroOp,
        "for a dual element", true,
        [ IsDualElement ], 0,
        function( d )
    return ObjByExtRep( FamilyObj( d ), [] );
end );

InstallMethod( IsZero,
        "for a dual element", true,
        [ IsDualElement ], 0,
        function( d )
    return d = Zero(d);
end );

InstallMethod( \<, 
        "for dual elements", true,
        [ IsDualElement, IsDualElement ], 0,
        function( d1, d2 )
    return ExtRepOfObj(d1) < ExtRepOfObj(d2);
end );

InstallMethod( \=, 
        "for dual elements", true,
        [ IsDualElement, IsDualElement ], 0,
        function( d1, d2 )
    return ExtRepOfObj(d1) = ExtRepOfObj(d2);
end );

InstallMethod( ImageElm,
        "for dual element and element from the underlying space",
        true, [ IsDualElement, IsObject ], 0,
        function( d, x )
    
    local   B,  cf,  res,  ed,  i,  pos;
    
    B:= FamilyObj(d)!.basisV;
    cf:= Coefficients( B, x );
    if cf = fail then return fail; fi;
    res:= Zero( cf[1] );
    ed:= ExtRepOfObj( d );
    for i in [1,3..Length(ed)-1] do
        pos:= Position( B, ed[i+1] );
        res:= res+ed[i]*cf[pos];
    od;
    return res;
end );


InstallMethod( DualAlgebraModule,
        "for a left module over a quantized uea", true,
        [ IsAlgebraModule and IsLeftAlgebraModuleElementCollection ], 0,
        function( M )
    
    local   U,  Mstr,  apode,  action,  gens,  R,  posR,  s,  sim,  
            rank,  g,  i,  ff,  vv,  imgs,  k,  u,  imu,  im,  j,  cf;
    
    U:= LeftActingAlgebra( M );
    if not IsQuantumUEA( U ) then TryNextMethod(); fi;
    Mstr:= DualSpace( M );
    
    apode:= AntipodeMap( U );
    
    if not IsGenericQUEA( U ) then
        # We cannot use DIYModule, so we just construct the dual module
        # with the action given by apode...
        
        action:= function( u, f )
            
            local   x,  cfs;
            
            x:= Image( apode, u );
            cfs:= List( FamilyObj( f )!.basisV, v -> Image( f, x^v ) );
            return cfs*FamilyObj( f )!.basisVdual;
        end;
        
        return LeftAlgebraModule( U, action, Mstr );
    fi;
    
    # Otherwise (in the generic case) we construct the action of the     
    # generators, and then construct the module by DIYModule; this gives
    # a module where the action can be calculated much faster.
    
    gens:= GeneratorsOfAlgebra( U );
    R:= RootSystem( U );
    posR:= PositiveRootsInConvexOrder( R );
    s:= Length( posR );
    sim:= SimpleSystemNF( R );
    rank:= Length( sim );
    g:= [ ];
    for i in [1..rank] do
        g[i]:= gens[ Position( posR, sim[i] ) ];
        g[rank+i]:= gens[ s+2*i-1 ];
        g[2*rank+i]:= gens[ s+2*i ];
        g[3*rank+i]:= gens[ s+2*rank+Position( posR, sim[i] ) ];
    od;
    
    ff:= BasisVectors( Basis( Mstr ) );
    vv:= List( ff, x -> ExtRepOfObj(x)[2] ); # i.e., corresponding basis vecs
                                             # of M.
    imgs:= [ ];
    for k in [1..Length(g)] do
        
        u:= Image( apode, g[k] );
        imu:= List( vv, v -> u^v );
        
        im:= [ ];
        for j in [1..Length(ff)] do
            # calculate the image g[k]^ff[j]
            cf:= List( [1..Length(vv)], i -> # j-th cft of imu[i]
                       Image( ff[j], imu[i] ) );
            Add( im, cf*ff );
        od;
        Add( imgs, im );
    od;

    return DIYModule( U, Mstr, imgs );
    
end );

InstallMethod( TrivialAlgebraModule,
        "for a quantized uea", true, [ IsQuantumUEA ], 0,
        function( U )
    
    local   F,  V;
    
    F:= LeftActingDomain(U);
    V:= F^1;
    return LeftAlgebraModule( U, function( u, v )
        return CounitMap(U)( u )*v; end, V );
        
end );
    
         

#############################################################################
##
#W  diymod.gi                  QuaGroup                       Willem de Graaf
##
##
##  A function for entering a module over a quantized enveloping algebra.
##


QGPrivateFunctions.DIYAction:= function( V, s, rank, B, posR, actlist, x, u0 )
    
    # Here V is a DIY U-module,
    # s the number of positive roots,
    # rank the rank of the root system,
    # B is the matrix of the bilinear form,
    # posR is the list of pos roots in convex order
    # actlist a list describing the actions of the generators,
    # x an element of U,
    # u0 an element of V;
    # this function returns x^u0.
    
    local   v,  rel,  k,  w,  lemon,  r,  pos,  exp,  i,  cfs,  t, qp, rtpos;
   
    v:= Zero( V );
    rel:= ExtRepOfObj( x );
    for k in [1,3..Length(rel)-1] do
        w:= u0;
        lemon:= Length(rel[k]);
        for r in [lemon-1,lemon-3..1] do
            if IsZero( w ) then break; fi;
            
            if IsList( rel[k][r] ) then
                # it is a `K'; special treatment for the binomial expressions.
                pos:= rel[k][r][1];
                qp:= _q^( B[pos-s][pos-s]/2 );
                for i in [1..rel[k][r+1]] do
                    if IsZero( w ) then break; fi;
                    cfs:= Coefficients( Basis(V), w );
                    w:= Zero( V );
                    for t in [1..Length(cfs)] do
                        if cfs[t]<>0*cfs[t] and 
                           IsBound( actlist[ pos ][t] ) then
                            w:= w+cfs[t]*(1/(qp^i-qp^(-i)))*
                                ( qp^(-i+1)*actlist[pos][t] -
                                  qp^(i-1)*actlist[pos+rank][t] );
                        fi;
                    od;
                od;
                if rel[k][r][2] > 0 then
                    # act also with lone K_{\alpha}:
                    cfs:= Coefficients( Basis(V), w );
                    w:= Zero( V );
                    for t in [1..Length(cfs)] do
                        if cfs[t]<>0*cfs[t] and
                           IsBound( actlist[ pos ][t] ) then
                            w:= w+cfs[t]*actlist[pos][t];
                        fi;
                    od;
                fi;
            else
                            
                # `pos' will be the position in the list `actlist' corr
                # to the variable `rel[k][r]';
                # `exp' will be the exponent with which it occurs.
                # `rtpos' ill be the position of the corr pos root in posR.
                if rel[k][r] <= s then
                    # it is an F...
                    pos:= rel[k][r];
                    rtpos:= pos;
                    exp:= rel[k][r+1];
                else
                    # it is an E...
                    pos:= rel[k][r]+rank;
                    rtpos:= rel[k][r]-s-rank;
                    exp:= rel[k][r+1];
                fi;
            
                for i in [1..exp] do
                    if IsZero( w ) then break; fi;
                    cfs:= Coefficients( Basis(V), w );
                    w:= Zero( V );
                    for t in [1..Length(cfs)] do
                        if cfs[t]<>0*cfs[t] and 
                           IsBound( actlist[ pos ][t] ) then
                            w:= w+cfs[t]*actlist[pos][t];
                        fi;
                    od;
                od;
                # need to divide by [exp]!
                qp:= _q^( posR[rtpos]*( B*posR[rtpos] )/2 );
                w:= w/GaussianFactorial( exp, qp );
            fi;
            
        od;
        v:= v+rel[k+1]*w;
    od;
    
    return v;
    
end;


QGPrivateFunctions.CompleteActList:= function( U, V, acts )
    
    # Here V is a U-module, and atcs is a list of lists, of length 4*l,
    # where l is the rank of te root system. acts describes the actions
    # of the generators [F_1,...,F_l,K_1,...,K_l,K_1^-1,...,K_l^-1, 
    # E_1,...,E_l ]. The action of each generator is described by a list
    # of length dim V, giving the images as elts of V; the zero elements
    # may be omitted: in that case there is a `hole' in the list.
    # This funtion returns a list with the actions of all PBW-generators.
    
    local   g,  fam,  actlist,  basV,  R,  B,  posR,  convR,  rank,  
            s,  i,  pos,  k,  k1,  k2,  pair,  rel,  cf,  qa,  aa,  j,  
            v,  w,  lemon,  r,  cfs,  t,  x,  sim;    
    
    g:= GeneratorsOfAlgebra( U );
    fam:= ElementsFamily( FamilyObj( U ) );
    
    # we compute an `actionlist' for each PBW-generator.
    
    actlist:= [ ];
    
    basV:= BasisVectors( Basis( V ) );
    
    R:= RootSystem( U );
    B:= BilinearFormMatNF( R );
    posR:= PositiveRootsNF( R );
    convR:= PositiveRootsInConvexOrder( R );

    rank:= Length( CartanMatrix(R) );
    s:= Length( posR );
    sim:= SimpleSystemNF( R );
    
    # first we do the F elements
    
    for i in [1..s] do

        x:= Position( sim, posR[i] );
        if x <> fail then
            # simple root; get action from the input...
            
            pos:= Position( convR, posR[i] );
            actlist[pos]:= acts[x];

        else
            # find a `definition' for F_{\alpha}

            # find a simple root r such that posR[i]-r is also a root
            for k in [1..rank ] do
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
            
            # Now compute the action of `rel' (which is the same as
            # the action of F_i).
            
            aa:= [ ];
            for j in [1..Length(basV)] do
                v:= Zero( V );
                for k in [1,3..Length(rel)-1] do
                    w:= basV[j];
                    lemon:= Length(rel[k]);
                    for r in [lemon-1,lemon-3..1] do
                        if IsZero( w ) then break; fi;
                        for x in [1..rel[k][r+1]] do
                            if IsZero( w ) then break; fi;
                            cfs:= Coefficients( Basis(V), w );
                            w:= Zero( V );
                            for t in [1..Length(cfs)] do
                                if IsBound( actlist[ rel[k][r] ][t] ) then
                                    w:= w+cfs[t]*actlist[rel[k][r]][t];
                                fi;
                            od;
                        od;
                        if rel[k][r+1] > 1 then
                            qa:= convR[ rel[k][r] ]*( B*convR[ rel[k][r] ] );
                            w:= w/GaussianFactorial( rel[k][r+1], qa );
                        fi;                    
                    od;
                    v:= v+rel[k+1]*w;
                od;
                if not IsZero( v ) then
                    aa[j]:= v;
                fi;                
            od;
            
            pos:= Position( convR, posR[i] );
            actlist[pos]:= aa;

        fi;
        
    od;

    # K-elements, just copy from the input....
    for i in [s+1..s+2*rank] do
        actlist[i]:= acts[ rank+i-s ];
    od;
    
    # then  we do the E elements

    for i in [1..s] do

        x:= Position( sim, posR[i] );
        if x <> fail then
            # simple root
            
            pos:= Position( convR, posR[i] );
            actlist[s+2*rank+pos]:= acts[ 3*rank+x ];

        else
            # find a `definition' for E_{\alpha}

            # find a simple root r such that posR[i]-r is also a root
            for k in [1..rank ] do
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
            
            # Compute the action of rel...
            
            aa:= [ ];
            for j in [1..Length(basV)] do
                v:= Zero( V );
                for k in [1,3..Length(rel)-1] do
                    w:= basV[j];
                    lemon:= Length(rel[k]);
                    for r in [lemon-1,lemon-3..1] do
                        if IsZero( w ) then break; fi;
                        # `pos' will be the psition of the action descr
                        # of generator with number rel[k][r], in the list
                        # `actlist'.
                        pos:= rel[k][r]+rank;
                        for x in [1..rel[k][r+1]] do
                            if IsZero( w ) then break; fi;
                            cfs:= Coefficients( Basis(V), w );
                            w:= Zero( V );
                            for t in [1..Length(cfs)] do
                                if IsBound( actlist[ pos ][t] ) then
                                    w:= w+cfs[t]*actlist[pos][t];
                                fi;
                            od;
                        od;
                        if rel[k][r+1] > 1 then
                            qa:= convR[ rel[k][r]-s-rank ]*( 
                                         B*convR[ rel[k][r]-s-rank ] );
                            w:= w/GaussianFactorial( rel[k][r+1], qa );
                        fi;
                    od;
                    v:= v+rel[k+1]*w;
                od;
                if not IsZero( v ) then
                    aa[j]:= v;
                fi;                
            od;
            
            pos:= Position( convR, posR[i] );
            actlist[s+2*rank+pos]:= aa;

        fi;
        
    od;    
    
    return actlist;
    
end;

InstallMethod( DIYModule,
        "for a quantum uea, a vector space, and a list", 
        true, [ IsQuantumUEA, IsLeftModule, IsList ], 0,
        
        function( U, V, acts )
    
    local   R,  s,  rank,  aa,  f, B,  posR;
    
    R:= RootSystem( U );
    B:= BilinearFormMatNF( R );
    s:= Length( PositiveRoots( R ) );
    rank:= Length( CartanMatrix( R ) );
    posR:= PositiveRootsInConvexOrder( R );
    aa:= QGPrivateFunctions.CompleteActList( U, V, acts );
    f:= function( x, u ) return 
      QGPrivateFunctions.DIYAction( V, s, rank, B, posR, aa, x, u ); end;
    return LeftAlgebraModule( U, f, V );
    
end );

#############################################################################
##
#W  isom.gi                  QuaGroup                           Willem de Graaf
##
##
##  Isomorphisms of quantized enveloping algebras.
##

#############################################################################
##
##  Functions for creating and working with automorphisms of quea:
##

QGPrivateFunctions.invertq:= function( qelt )
    
    local   num,  den,  en,  ed,  i;
    
    if not qelt in QuantumField then 
        Error("<qelt> does not lie in QuantumField");
    fi;
    num:= 0*_q; den:= 0*_q;
    en:= ExtRepNumeratorRatFun( qelt );
    ed:= ExtRepDenominatorRatFun( qelt );
    for i in [1,3..Length(en)-1] do
        if en[i] = [ ] then 
            num:= num+en[i+1]; 
        else
            num:= num + en[i+1]*_q^( -en[i][2] );
        fi;
    od;
    for i in [1,3..Length(ed)-1] do
        if ed[i] = [ ] then 
            den:= den+ed[i+1]; 
        else
            den:= den + ed[i+1]*_q^( -ed[i][2] );
        fi;
    od;
    return num/den;
end;

        

QGPrivateFunctions.makeImageList:= function( U, imgs, isrev )
    
    # imgs is a list of length 4*l; first the images of the F-gens,
    # then the images of the K-gens, then K^-1-gens, finally the E-gens.
    
    local   g,  fam,  imlist,  R,  B,  posR,  convR,  rank,  s,  sim,  
            i,  x,  pos,  k,  k1,  k2,  pair,  rel,  cf,  qa,  im,  u,  
            r,  qp,  one,  zero;
    
    g:= GeneratorsOfAlgebra( U );
    fam:= ElementsFamily( FamilyObj( U ) );
    
    # we compute an image for each PBW-generator.
    
    imlist:= [ ];
    
    one:= imgs[1]^0;
    zero:= imgs[1]*0;
    
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
            # simple root; get image from the input...
            
            pos:= Position( convR, posR[i] );
            imlist[pos]:= imgs[x];

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
            
            # Now compute the image of `rel' (which is the same as
            # the image of F_i).
            
            if isrev then
                for k in [2,4..Length(rel)] do
                    rel[k]:= QGPrivateFunctions.invertq( rel[k] );
                od;
            fi;
            
            im:= zero;
            for k in [1,3..Length(rel)-1] do
                u:= rel[k+1]*one;
                for r in [1,3..Length(rel[k])-1] do
                    qp:= _q^( posR[i]*( B*posR[i] ) );
                    u:= u*( imlist[rel[k][r]]^rel[k][r+1] )/GaussianFactorial(
                                rel[k][r+1], qp );
                od;
                im:= im+u;
            od;
            
            pos:= Position( convR, posR[i] );
            imlist[pos]:= im;

        fi;
        
    od;

    # K-elements, just copy from the input....
    for i in [s+1..s+2*rank] do
        imlist[i]:= imgs[ rank+i-s ];
    od;
    
    # then  we do the E elements

    for i in [1..s] do

        x:= Position( sim, posR[i] );
        if x <> fail then
            # simple root
            
            pos:= Position( convR, posR[i] );
            imlist[s+2*rank+pos]:= imgs[ 3*rank+x ];

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
            
            # Compute the image of rel...
            
            if isrev then
                for k in [2,4..Length(rel)] do
                    rel[k]:= QGPrivateFunctions.invertq( rel[k] );
                od;
            fi;
            im:= zero;
            for k in [1,3..Length(rel)-1] do
                u:= rel[k+1]*one;
                for r in [1,3..Length(rel[k])-1] do
                    qp:= _q^( posR[i]*( B*posR[i] ) );
                    u:= u*( imlist[rel[k][r]+rank]^rel[k][r+1] )/
                        GaussianFactorial( rel[k][r+1], qp );
                od;
                im:= im+u;
            od;
            
            pos:= Position( convR, posR[i] );
            imlist[s+2*rank+pos]:= im;

        fi;
        
    od;    
    
    return imlist;
end;

InstallMethod( QEAAutomorphism,
     "for a generic quea and a list", true,
     [ IsGenericQUEA, IsList ], 0,
    function( U, imgs )
    
    local imlist, map;
    
    imlist:= QGPrivateFunctions.makeImageList( U, imgs, false );    
    map:= Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := imlist,
                      rank:= Length( SimpleSystem( RootSystem(U) ) ),
                      noPosR:= Length( PositiveRoots( RootSystem(U) ) )
                      ) );
    SetIsqReversing( map, false );
    return map;
end );

InstallMethod( QEAAutomorphism,
        "for a quea and an autom. of the corr. generic quea", 
        true, [ IsQuantumUEA, IsGenericQUEAAutomorphism ], 0,
        function( U, f )
    
    if IsqReversing(f) then
        Error("<f> must not map q to q^-1");
    fi;

    return Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsInducedQUEAAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec( origMap:= f ) );
end );



InstallMethod( PrintObj,
        "for quea automorphism", true, [ IsQUEAAutomorphism ], 0,
        function( map )
    
    Print("<automorphism of ",Source( map ),">");
end );

InstallMethod( ImageElm,
        "for quea aut, and elm",
        true, [ IsGenericQUEAHomomorphism, IsQEAElement ], 0,
        function( map, x )

    local   rew_K_noninv,  rew_K_inv,  ex,  U,  R,  B,  posR,  sim,  
            noposR,  rank,  im,  i,  u,  j,  qp, zero, one;

    rew_K_noninv:= function( a, b, delta, s, qpar )

        local res, i;

        res:= a^delta;
        for i in [1..s] do
            res:= res*( qpar^(-i+1)*a-qpar^(i-1)*b )/( qpar^i-qpar^-i );
        od;
        
        return res;
    end;
     
    rew_K_inv:= function( a, b, delta, s, qpar )
        
        local res, i;
        
        res:= a^delta;
        for i in [1..s] do
            res:= res*( qpar^(i-1)*a-qpar^(-i+1)*b )/( qpar^-i-qpar^i );
        od;
        
        return res;
    end;
    
    ex:= ExtRepOfObj( x );
    U:= Source( map );
    R:= RootSystem( U );
    B:= BilinearFormMatNF( R );
    posR:= PositiveRootsInConvexOrder( R );
    sim:= SimpleSystemNF( R );
    noposR:= map!.noPosR;
    rank:= map!.rank;
    
    zero:= Zero( Range( map ) );
    one:= One( Range( map ) );
    im:= zero;
    for i in [1,3..Length(ex)-1] do
        if IsqReversing( map ) then
            u:= QGPrivateFunctions.invertq( ex[i+1] )*one;
        else
            u:= ex[i+1]*one;
        fi;
        
        for j in [1,3..Length(ex[i])-1] do
            if IsList( ex[i][j] ) then 
                #it is a K...; more difficult.
                qp:= _q^( sim[ ex[i][j][1]-noposR ]*
                          ( B*sim[ ex[i][j][1]-noposR ] )/2);
                if IsqReversing( map ) then
                    u:= u*rew_K_inv( map!.images[ ex[i][j][1] ], 
                                map!.images[ ex[i][j][1]+map!.rank ], 
                                ex[i][j][2], 
                                ex[i][j+1], qp );
                else
                   u:= u*rew_K_noninv( map!.images[ ex[i][j][1] ], 
                                map!.images[ ex[i][j][1]+map!.rank ], 
                                ex[i][j][2], 
                               ex[i][j+1], qp ); 
               fi;

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
        "for induced quea aut, and elm",
        true, [ IsInducedQUEAAutomorphism, IsQEAElement ], 0,
        function( map, x )

        local U, qp, U0, f0, im, ex, i, y, ey, j;  
        U:= Source( map );
        qp:= QuantumParameter( U );
        U0:= QuantizedUEA( RootSystem( U ) );
        f0:= map!.origMap;
        im:= Zero( U );
        ex:= ExtRepOfObj( x );

        for i in [1,3..Length(ex)-1] do
            y:= ObjByExtRep( ElementsFamily(FamilyObj(U0)), [ ShallowCopy(ex[i]), 
                    QuantumParameter(U0)^0 ] );
            y:= Image( f0, y );
            ey:= ShallowCopy( ExtRepOfObj(y) );
            for j in [2,4..Length(ey)] do
                ey[j]:= Value( ey[j], qp )*ex[i+1];
                if IsZero( ey[j] ) then
                   Unbind( ey[j] ); Unbind(ey[j-1]);
                fi;
            od;
            ey:= Filtered( ey, x -> IsBound(x) );
            im:= im + ObjByExtRep( ElementsFamily(FamilyObj(U)), ey );
        od;
        return im;
end );

InstallMethod( \*,
       "for two qea automorphisms", true,
       [ IsGenericQUEAAutomorphism, IsGenericQUEAAutomorphism ], 0,
      
       function( f, g )

          local U, ims,  map;

          if not IsIdenticalObj( Range(f), Source(g) ) then
              Error( "Range( <f> ) and Source( <g> ) do not match");
          fi;

          U:= Source( f );
          ims:= List( g!.images, x -> Image( f, x ) );
          map:= Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := ims,
                      rank:= f!.rank,
                      noPosR:= f!.noPosR
                      ) );
          # map is q-reversing iff exactly one of f, g is q-reversing.
          SetIsqReversing( map, ( IsqReversing(f) or IsqReversing(g) ) and
                  not ( IsqReversing(f) and IsqReversing(g) ) );
          return map;
          
end );


InstallMethod( \*,
       "for two induced qea automorphisms", true,
       [ IsInducedQUEAAutomorphism, IsInducedQUEAAutomorphism ], 0,
      
       function( f, g )
    
    if not IsIdenticalObj( Range(f), Source(g) ) then
        Error( "Range( <f> ) and Source( <g> ) do not match");
    fi;
    return QEAAutomorphism( Source(f), f!.origMap*g!.origMap );
          
end );

##################################################################################
##
##  Same as above, but now for aniautomorphisms:
##

InstallMethod( QEAAntiAutomorphism,
     "for a generic quea and an algebra, and a list", true,
     [ IsGenericQUEA, IsList ], 0,
    function( U, imgs )
    
    # imgs is a list of length 4*l; first the images of the F-gens,
    # then the images of the K-gens, then K^-1-gens, finally the E-gens.
    
    local   g,  fam,  imlist,  R,  B,  posR,  convR,  rank,  s,  sim,  
            i,  x,  pos,  k,  k1,  k2,  pair,  rel,  cf,  qa,  im,  u,  
            r,  qp,  map,  images;
    
    g:= GeneratorsOfAlgebra( U );
    fam:= ElementsFamily( FamilyObj( U ) );
    
    # we compute an image for each PBW-generator.
    
    imlist:= [ ];
    
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
            # simple root; get image from the input...
            
            pos:= Position( convR, posR[i] );
            imlist[pos]:= imgs[x];

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
            
            # Now compute the image of `rel' (which is the same as
            # the image of F_i).
            
            im:= Zero( U );
            for k in [1,3..Length(rel)-1] do
                u:= rel[k+1]*One( U );
                for r in [1,3..Length(rel[k])-1] do
                    qp:= _q^( posR[i]*( B*posR[i] ) );
                    u:= (( imlist[rel[k][r]]^rel[k][r+1] )/GaussianFactorial(
                                rel[k][r+1], qp ))*u;
                od;
                im:= im+u;
            od;
            
            pos:= Position( convR, posR[i] );
            imlist[pos]:= im;

        fi;
        
    od;

    # K-elements, just copy from the input....
    for i in [s+1..s+2*rank] do
        imlist[i]:= imgs[ rank+i-s ];
    od;
    
    # then  we do the E elements

    for i in [1..s] do

        x:= Position( sim, posR[i] );
        if x <> fail then
            # simple root
            
            pos:= Position( convR, posR[i] );
            imlist[s+2*rank+pos]:= imgs[ 3*rank+x ];

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
            
            # Compute the image of rel...
            
            im:= Zero( U );
            for k in [1,3..Length(rel)-1] do
                u:= rel[k+1]*One( U );
                for r in [1,3..Length(rel[k])-1] do
                    qp:= _q^( posR[i]*( B*posR[i] ) );
                    u:= ( ( imlist[rel[k][r]+rank]^rel[k][r+1] )/
                        GaussianFactorial( rel[k][r+1], qp ) )*u;
                od;
                im:= im+u;
            od;
            
            pos:= Position( convR, posR[i] );
            imlist[s+2*rank+pos]:= im;

        fi;
        
    od;    
    
    map:= Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAAntiAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := imlist,
                      rank:= rank,
                      noPosR:= s
                      ) );
    SetIsqReversing( map, false );
    return map;
end );

InstallMethod( QEAAntiAutomorphism,
   "for a quea and an anti atom. of the corr. generic quea",
   true, [ IsQuantumUEA, IsGenericQUEAAntiAutomorphism ], 0,
    function( U, f )


   return Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsInducedQUEAAntiAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec( origMap:= f ) );
end );


InstallMethod( PrintObj,
        "for quea anti automorphism", true, [ IsQUEAAntiAutomorphism ], 0,
        function( map )
    
    Print("<anti-automorphism of ",Source( map ),">");
end );

InstallMethod( ImageElm,
        "for quea aut, and elm",
        true, [ IsGenericQUEAAntiAutomorphism, IsQEAElement ], 0,
        function( map, x )

    local   rew_K_noninv,  rew_K_inv,  ex,  U,  R,  B,  posR,  sim,  
            noposR,  rank,  im,  i,  u,  j,  qp;
    
    rew_K_noninv:= function( a, b, delta, s, qpar )

         local res, i;

         res:= a^delta;
         for i in [1..s] do
            res:= res*( qpar^(-i+1)*a-qpar^(i-1)*b )/( qpar^i-qpar^-i );
         od;
         return res;
     end;
     
     rew_K_inv:= function( a, b, delta, s, qpar )

         local res, i;

         res:= a^delta;
         for i in [1..s] do
            res:= res*( qpar^(i-1)*a-qpar^(-i+1)*b )/( qpar^-i-qpar^i );
         od;
         return res;
    end;

    ex:= ExtRepOfObj( x );
    U:= Source( map );
    R:= RootSystem( U );
    B:= BilinearFormMatNF( R );
    posR:= PositiveRootsInConvexOrder( R );
    sim:= SimpleSystemNF( R );
    noposR:= map!.noPosR;
    rank:= map!.rank;
    
    im:= Zero( U );
    for i in [1,3..Length(ex)-1] do
        if IsqReversing( map ) then
            u:= QGPrivateFunctions.invertq( ex[i+1] )*One( U );
        else
            u:= ex[i+1]*One( U );
        fi;

        for j in [1,3..Length(ex[i])-1] do
            if IsList( ex[i][j] ) then 
                #it is a K...; more difficult.
                qp:= _q^( sim[ ex[i][j][1]-noposR ]*
                          ( B*sim[ ex[i][j][1]-noposR ] )/2 );
                if IsqReversing( map ) then
                    u:= rew_K_inv( map!.images[ ex[i][j][1] ], 
                                map!.images[ ex[i][j][1]+map!.rank ], 
                                ex[i][j][2], 
                                ex[i][j+1], qp )*u;
                else
                    u:= rew_K_noninv( map!.images[ ex[i][j][1] ], 
                                map!.images[ ex[i][j][1]+map!.rank ], 
                                ex[i][j][2], 
                                ex[i][j+1], qp )*u;
                fi;
                
            elif ex[i][j] <= map!.noPosR then
                #it is an F...
                qp:= _q^( posR[ ex[i][j] ]*( B*posR[ ex[i][j] ] )/2 );
                u:= (( map!.images[ ex[i][j] ]^ex[i][j+1] )/
                   GaussianFactorial( ex[i][j+1], qp ))*u;
            else
                #it is an E...
                qp:= _q^( posR[ ex[i][j]-noposR-rank ]*( 
                                    B*posR[ ex[i][j]-noposR-rank ] )/2 );
  
                u:= (( map!.images[ ex[i][j]+rank ]^ex[i][j+1] )/
                   GaussianFactorial( ex[i][j+1], qp ))*u;
            fi;
        od;
        im:= im+u;
    od;

    return im;

end );


InstallMethod( ImageElm,
        "for induced quea anti aut, and elm",
        true, [ IsInducedQUEAAntiAutomorphism, IsQEAElement ], 0,
        function( map, x )

        local U, qp, U0, f0, im, ex, i, y, ey, j;  
        U:= Source( map );
        qp:= QuantumParameter( U );
        U0:= QuantizedUEA( RootSystem( U ) );
        f0:= map!.origMap;
        im:= Zero( U );
        ex:= ExtRepOfObj( x );

        for i in [1,3..Length(ex)-1] do
            y:= ObjByExtRep( ElementsFamily(FamilyObj(U0)), [ ShallowCopy(ex[i]), 
                    QuantumParameter(U0)^0 ] );
            y:= Image( f0, y );
            ey:= ShallowCopy( ExtRepOfObj(y) );
            for j in [2,4..Length(ey)] do
                ey[j]:= Value( ey[j], qp )*ex[i+1];
                if IsZero( ey[j] ) then
                   Unbind( ey[j] ); Unbind(ey[j-1]);
                fi;
            od;
            ey:= Filtered( ey, x -> IsBound(x) );
            im:= im + ObjByExtRep( ElementsFamily(FamilyObj(U)), ey );
        od;
        return im;
end );

InstallMethod( \*,
       "for two qea anti automorphisms", true,
       [ IsGenericQUEAAntiAutomorphism, IsGenericQUEAAntiAutomorphism ], 0,
      
       function( f, g )

          local U, ims, map;
          
          if not IsIdenticalObj( Range(f), Source(g) ) then
              Error( "Range( <f> ) and Source( <g> ) do not match");
          fi;
          U:= Source( f );
          ims:= List( g!.images, x -> Image( f, x ) );
          map:= Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := ims,
                      rank:= f!.rank,
                      noPosR:= f!.noPosR
                      ) );
          # map is q-reversing iff exactly one of f, g is q-reversing.
          SetIsqReversing( map, ( IsqReversing(f) or IsqReversing(g) ) and
                  not ( IsqReversing(f) and IsqReversing(g) ) );
          return map;
end );


InstallMethod( \*,
       "for two induced qea automorphisms", true,
       [ IsInducedQUEAAntiAutomorphism, IsInducedQUEAAntiAutomorphism ], 0,
      
       function( f, g )
    
        
    if not IsIdenticalObj( Range(f), Source(g) ) then
        Error( "Range( <f> ) and Source( <g> ) do not match");
    fi;
    return QEAAutomorphism( Source(f), f!.origMap*g!.origMap );
          
end );


InstallMethod( \*,
       "for an automorphism and an antiautomorphism", true,
       [ IsGenericQUEAAutomorphism, IsGenericQUEAAntiAutomorphism ], 0,
      
       function( f, g )
          local U, ims, map;

          if not IsIdenticalObj( Range(f), Source(g) ) then
              Error( "Range( <f> ) and Source( <g> ) do not match");
          fi;
          U:= Source( f );
          ims:= List( g!.images, x -> Image( f, x ) );
          map:= Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAAntiAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := ims,
                      rank:= f!.rank,
                      noPosR:= f!.noPosR
                      ) );
          # map is q-reversing iff exactly one of f, g is q-reversing.
          SetIsqReversing( map, ( IsqReversing(f) or IsqReversing(g) ) and
                  not ( IsqReversing(f) and IsqReversing(g) ) );
          return map;
end );
       

InstallMethod( \*,
       "for an automorphism and an antiautomorphism", true,
       [ IsInducedQUEAAutomorphism, IsInducedQUEAAntiAutomorphism ], 0,
      
       function( f, g )

          if not IsIdenticalObj( Range(f), Source(g) ) then
              Error( "Range( <f> ) and Source( <g> ) do not match");
          fi;
          return QEAAntiAutomorphism( Source(f), 
                         f!.origMap*g!.origMap );
          
end );


InstallMethod( \*,
       "for an automorphism and an antiautomorphism", true,
       [ IsGenericQUEAAntiAutomorphism, IsGenericQUEAAutomorphism ], 0,
      
       function( f, g )
          local U, ims, map;
    
          if not IsIdenticalObj( Range(f), Source(g) ) then
              Error( "Range( <f> ) and Source( <g> ) do not match");
          fi;

          U:= Source( f );
          ims:= List( g!.images, x -> Image( f, x ) );
          map:= Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAAntiAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := ims,
                      rank:= f!.rank,
                      noPosR:= f!.noPosR
                      ) );
          # map is q-reversing iff exactly one of f, g is q-reversing.
          SetIsqReversing( map, ( IsqReversing(f) or IsqReversing(g) ) and
                  not ( IsqReversing(f) and IsqReversing(g) ) );
          return map;
end );
       

InstallMethod( \*,
       "for an automorphism and an antiautomorphism", true,
       [ IsInducedQUEAAntiAutomorphism, IsInducedQUEAAutomorphism ], 0,
      
       function( f, g )
    
          if not IsIdenticalObj( Range(f), Source(g) ) then
              Error( "Range( <f> ) and Source( <g> ) do not match");
          fi;
          return QEAAntiAutomorphism( Source(f), 
                         f!.origMap*g!.origMap );
          
end );

#################################################################################
##
##  Functions for creating some particular automorphisms:
##
InstallMethod( AutomorphismOmega,
       "for a quea", true, [IsQuantumUEA], 0,
       function( U )

         local U0, R, posR, sim, rank, noR, g, ims, i, f;

         if IsGenericQUEA( U ) then
             U0:= U;
         else
             U0:= QuantizedUEA( RootSystem( U ) );
         fi;

         R:= RootSystem( U0 );
         posR:= PositiveRootsInConvexOrder( R );
         sim:= SimpleSystemNF( R );
         rank:= Length( sim );
         noR:= Length( posR );

         g:= GeneratorsOfAlgebra( U0 );
         ims:= [ ];

         # F_alpha is mapped to E_alpha:
         for i in [1..rank] do
            Add( ims, g[ Position( posR, sim[i] )+2*rank+noR ] );
         od;

         # K_alpha --> K_alpha^-1
         for i in [1..rank] do
            Add( ims, g[ noR+2*i ] );
         od;
         # K_alpha^-1 --> K_alpha
         for i in [1..rank] do
            Add( ims, g[noR+2*i-1] );
         od;
         # E_alpha --> F_alpha
         for i in [1..rank] do
            Add( ims, g[ Position( posR, sim[i] ) ] );
         od;

         f:= QEAAutomorphism( U0, ims );

         if IsGenericQUEA( U ) then
             SetIsqReversing( f, false ); 
            return f;
         else
            return QEAAutomorphism( U, f );
         fi;
end );


InstallMethod( AntiAutomorphismTau,
       "for a quea", true, [IsQuantumUEA], 0,
       function( U )

         local U0, R, posR, sim, rank, noR, g, ims, i, f;

         if IsGenericQUEA( U ) then
             U0:= U;
         else
             U0:= QuantizedUEA( RootSystem( U ) );
         fi;

         R:= RootSystem( U0 );
         posR:= PositiveRootsInConvexOrder( R );
         sim:= SimpleSystemNF( R );
         rank:= Length( sim );
         noR:= Length( posR );

         g:= GeneratorsOfAlgebra( U0 );
         ims:= [ ];

         # F_alpha is mapped to F_alpha:
         for i in [1..rank] do
            Add( ims, g[ Position( posR, sim[i] ) ] );
         od;

         # K_alpha --> K_alpha^-1
         for i in [1..rank] do
            Add( ims, g[ noR+2*i ] );
         od;
         # K_alpha^-1 --> K_alpha
         for i in [1..rank] do
            Add( ims, g[noR+2*i-1] );
         od;
         # E_alpha --> E_alpha
         for i in [1..rank] do
            Add( ims, g[ Position( posR, sim[i] ) +2*rank+noR] );
         od;

         f:= QEAAntiAutomorphism( U0, ims );

         if IsGenericQUEA( U ) then
             SetIsqReversing( f, false );
             return f;
         else
            return QEAAntiAutomorphism( U, f );
         fi;
end );
   

InstallMethod( AutomorphismTalpha,
       "for a quea", true, [IsQuantumUEA,IsInt], 0,
       function( U, ind )

         local U0, R, posR, sim, rank, noR, g, ims, i, f, qp, a, u, r, b, j;

         if IsGenericQUEA( U ) then
             U0:= U;
         else
             U0:= QuantizedUEA( RootSystem( U ) );
         fi;

         R:= RootSystem( U0 );
         posR:= PositiveRootsInConvexOrder( R );
         sim:= SimpleSystemNF( R );
         rank:= Length( sim );
         noR:= Length( posR );
         qp:= QuantumParameter(U0)^( BilinearFormMatNF(R)[ind][ind]/2 );

         g:= GeneratorsOfAlgebra( U0 );
         ims:= [ ];

         # F_beta...
         a:= g[ Position( posR, sim[ind] ) ];
         for i in [1..rank] do
            if i = ind then
               # F_alpha is mapped to -K_alpha^-1 E_alpha:
               Add( ims, -g[ noR+2*i ]*g[ Position( posR, sim[i] )+2*rank+noR ] );
            else
               # F_alpha is mapped to a sum..
               u:= Zero( U0 );
               r:= -CartanMatrix(R)[i][ind];
               b:= g[ Position( posR, sim[i] ) ];
               for j in [0..r] do
                   u:= u + (-qp)^j*( a^j/GaussianFactorial(j,qp) )*b*
                                     a^(r-j)/GaussianFactorial(r-j,qp);
               od;
               Add( ims, u );
            fi;
         od;

         # K_alpha...
         for i in [1..rank] do
            if i = ind then
               Add( ims, g[ noR+2*i ] );
            else
               Add( ims, g[noR+2*i-1]*g[noR+2*ind-1]^-CartanMatrix(R)[i][ind] );
            fi;
         od;
         # K_alpha^-1:
         for i in [1..rank] do
            if i = ind then
               Add( ims, g[noR+2*i-1] );
            else
               Add( ims, g[noR+2*i]*g[noR+2*ind]^-CartanMatrix(R)[i][ind] );
            fi;
         od;

         # E_beta
         a:= g[ Position( posR, sim[ind] ) +2*rank+noR ];
         for i in [1..rank] do
            if i = ind then
               # E_alpha is mapped to -F_alpha K_alpha
               Add( ims, -g[ Position( posR, sim[i] ) ]*g[ noR+2*i-1 ] );
            else
               # E_alpha is mapped to a sum..
               u:= Zero( U0 );
               r:= -CartanMatrix(R)[i][ind];
               b:= g[ Position( posR, sim[i] )+noR+2*rank ];
               for j in [0..r] do
                   u:= u + (-qp^-1)^j*( a^(r-j)/GaussianFactorial(r-j,qp) )*b*
                                     a^(j)/GaussianFactorial(j,qp);
               od;
               Add( ims, u );
            fi;
         od;

         f:= QEAAutomorphism( U0, ims );

         if IsGenericQUEA( U ) then
             SetIsqReversing( f, false );
             return f;
         else
             return QEAAutomorphism( U, f );
         fi;
end );


InstallMethod( DiagramAutomorphism,
       "for a quea and a permutation", true, [IsQuantumUEA, IsPerm], 0,
       function( U, p )

         local U0, R, posR, sim, rank, noR, g, ims, i, f;

         if IsGenericQUEA( U ) then
             U0:= U;
         else
             U0:= QuantizedUEA( RootSystem( U ) );
         fi;

         R:= RootSystem( U0 );
         posR:= PositiveRootsInConvexOrder( R );
         sim:= SimpleSystemNF( R );
         rank:= Length( sim );
         noR:= Length( posR );

         g:= GeneratorsOfAlgebra( U0 );
         ims:= [ ];

         # F_alpha is mapped to F_p(\alpha):
         for i in [1..rank] do
            Add( ims, g[ Position( posR, sim[i^p] ) ] );
         od;

         # K_alpha --> K_p(alpha)
         for i in [1..rank] do
            Add( ims, g[ noR+2*(i^p)-1 ] );
         od;
         # K_alpha^-1 --> K_p(alpha)^-1
         for i in [1..rank] do
            Add( ims, g[noR+2*(i^p)] );
         od;
         # E_alpha --> E_p(alpha)
         for i in [1..rank] do
            Add( ims, g[ Position( posR, sim[i^p] ) +2*rank+noR ] );
         od;

         f:= QEAAutomorphism( U0, ims );

         if IsGenericQUEA( U ) then
             SetIsqReversing( f, false ); 
             return f;
         else
             return QEAAutomorphism( U, f );
         fi;
end );


InstallMethod( BarAutomorphism,
       "for a quea", true, [IsGenericQUEA], 0,
        function( U )
    
    local   imgs,  g,  R,  sim,  posR,  s,  rank,  i,  pos,  imlist,  
            map,  images,  noPosR;
    
    imgs:= [ ];
    g:= GeneratorsOfAlgebra( U );
    R:= RootSystem( U );
    sim:= SimpleSystemNF( R );
    posR:= PositiveRootsInConvexOrder( R );
    s:= Length( posR );
    rank:= Length(sim);
    for i in [1..rank] do
        pos:= Position( posR, sim[i] );
        imgs[i]:= g[ pos ];
        imgs[rank+i]:= g[ s+2*i ];
        imgs[ 2*rank+i ]:= g[ s+2*i-1 ];
        imgs[ 3*rank+i ]:= g[ s+2*rank+pos ];
    od;
    
    imlist:= QGPrivateFunctions.makeImageList( U, imgs, true );    
    map:= Objectify( TypeOfDefaultGeneralMapping( U, U,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAAutomorphism
                  and IsBijective
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := imlist,
                      rank:= rank,
                      noPosR:= s
                      ) );
    SetIsqReversing( map, true );
    return map;
end );


#############################################################################
##
##   Functions for creating homomorphisms:
##
##   We note that this only works "generically", in order to create 
##   non-generic homomorphisms U' --> A', we would need a generic map
##   U --> A, along with a map A --> A', somehow substituting the
##   quantum parameter. This seems rather cumbersome to do in general.
##   (Also it is not clear what A must be in general).
##
InstallMethod( QEAHomomorphism,
     "for a generic quea, an algebra and a list", true,
     [ IsGenericQUEA, IsObject, IsList ], 0,
    function( U, A, imgs )
    
    local imlist, map;
    
    imlist:= QGPrivateFunctions.makeImageList( U, imgs, false );    
    map:= Objectify( TypeOfDefaultGeneralMapping( U, A,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsGenericQUEAHomomorphism
                  and IsAlgebraHomomorphism),
                  rec(
                      images  := imlist,
                      rank:= Length( SimpleSystem( RootSystem(U) ) ),
                      noPosR:= Length( PositiveRoots( RootSystem(U) ) )
                      ) );
    SetIsqReversing( map, false );
    return map;
end );


InstallMethod( PrintObj,
        "for quea homomorphism", true, [ IsQUEAHomomorphism ], 0,
        function( map )
    
    Print("<homomorphism: ",Source( map )," -> ",Range(map),">");
end );

#############################################################################
##
#W  uea.gi                  QuaGroup                           Willem de Graaf
##
##
##  Methods for universal env algs.
##


##############################################################################
##
#M  UEA( <L> )
##
InstallMethod( UEA,
        "for a semisimple Lie algebra",
        true, [ IsLieAlgebra ], 0,
        function( L )
    
    local   g,  A;
    
    # get the generators:
    g:= LatticeGeneratorsInUEA( L );
    
    A:= Objectify( NewType( CollectionsFamily( FamilyObj( g[1] ) ),
                IsMagmaRingModuloRelations
                and IsAttributeStoringRep ),
                rec() );
    SetIsAssociative( A, true );
    SetLeftActingDomain( A, Rationals );
    SetGeneratorsOfLeftOperatorRing( A, g );
    SetGeneratorsOfLeftOperatorRingWithOne( A, g );
    SetOne( A, g[1]^0 );
    
    SetRootSystem( A, RootSystem(L) );
    SetUnderlyingLieAlgebra( A, L );
    
    return A;
end );

#############################################################################
##
#M  QUEAToUEAMap( <L> )
##
##
InstallMethod( QUEAToUEAMap,
        "for a semisimple Lie algebra", 
        true, [ IsLieAlgebra ], 0,

        function( L )
    
    local   R,  uu,  S,  B,  convR,  posR,  rank,  F,  f,  tab,  
            imgs,  i,  pos,  k,  k1,  k2,  pair,  rel,  cf,  qa,  im,  
            im1,  j,  E,  e,  s, MyVal, map, sim, U;    
    
    # We first calculate a list of images of the generators of U.
    # We have that Ki^d [ Ki : k ] --> ( hi / k ).
    # Furthermore the F_i corr to the simple roots are mapped to 
    # y_i, corr to the same simple root. Likewise for the Ei.
    
    MyVal:= function( qelt, val )
        
        return Value( NumeratorOfRationalFunction(qelt), val )/
               Value( DenominatorOfRationalFunction(qelt), val );
    end;

    U:= QuantizedUEA( L );
    R:= RootSystem( L );
    uu:= UEA( L );
    B:= BilinearFormMatNF( R );
    convR:= PositiveRootsInConvexOrder( R );
    posR:= PositiveRootsNF( R );
    sim:= SimpleSystemNF( R );
    rank:= Length( CartanMatrix(R) );
    s:= Length( posR );

    F:= GeneratorsOfAlgebra( U ){[1..Length(PositiveRoots(R))]};
    f:= GeneratorsOfAlgebra( uu ){[1..Length(PositiveRoots(R))]};
    
    # we map the F's to f's...
    
    tab:= ElementsFamily( FamilyObj( U ) )!.multTab;
    
    imgs:= [ ];
    for i in [1..s] do
        
        pos:= Position( sim, posR[i] );
        if pos <> fail then
            # simple root; first we find the position of the simple generator:
            pos:= Position( posR, sim[ pos ] );
            imgs[ Position( convR, posR[i] ) ]:= f[ pos ];
        else
            # find a definition
            
            for k in [1..rank] do
                
                # First we find a simple root r such that posR[i]-r 
                # is also a root
                
                k1:= Position( convR, posR[i] - sim[k] );
                if k1 <> fail then
                    k2:= Position( convR, sim[k] );

                    if k1 > k2 then
                        pair:= [ k1, k2 ];
                    else
                        pair:= [ k2, k1 ];
                    fi;

                    rel:= ShallowCopy( tab[ pair[1] ][ pair[2] ] );

                    # we establish whether F_i is in there
                    pos:= Position( rel, [ Position( convR, posR[i] ), 1 ] );
                    if pos <> fail then break; fi;
                fi;
            od;

            # We throw away the F_i in `rel'.
            cf:= rel[ pos+1];
            Unbind( rel[pos] ); Unbind( rel[pos+1] );
            rel:= Filtered( rel, x -> IsBound(x) );
            
            # Get the coefficients right:
            for k in [1,3..Length(rel)-1] do
                rel[k+1]:= -(1/cf)*rel[k+1];
            od;
            
            # Now we add the AB-q^*BA bit:
            
            Add( rel, [ pair[1], 1, pair[2], 1 ] );
            Add( rel, 1/cf );
            
            qa:=  _q^( -convR[k1]*( B*convR[k2] ) );
            Add( rel, [ pair[2], 1, pair[1], 1 ] );
            Add( rel, -qa/cf );
            
            # now `rel' is the `definition' of F_i (in terms of pbw
            # elts of lower level). 

            im:= Zero( f[1] );
      
            for k in [1,3..Length(rel)-1] do
                im1:= f[1]^0;
                for j in [1,3..Length(rel[k])-1] do
                    im1:=(1/Factorial( rel[k][j+1] ))*im1*
                         ( imgs[rel[k][j]]^rel[k][j+1] );
                od;
      
                im:= im+MyVal( rel[k+1], 1 )*im1;
            od;
            
            imgs[ Position( convR, posR[i] ) ]:= im;
        fi;
    od;
    
    # The K-elements; we just record the indices of the h-elements, which we
    # need for calculating the image of an elt...
    Append( imgs, List([1..rank], ii -> ii + 2*Length(posR) ) );
    
    # then  we do the E elements
    
    E:= GeneratorsOfAlgebra( U ){[Length(posR)+rank+1..2*Length(posR)+rank]};
    e:= GeneratorsOfAlgebra( uu ){[Length(posR)+1..2*Length(posR)]};

    for i in [1..s] do
        
        pos:= Position( sim, posR[i] );
        if pos <> fail then
            # simple root
            pos:= Position( posR, sim[ pos ] );
            imgs[ s+rank+Position( convR, posR[i] ) ]:= e[ pos ];
        else
            # find a `definition' for E_{\alpha}

            # find a simple root r such that posR[i]-r is also a root
            for k in [1.. rank ] do
                k1:= Position( convR, posR[i] - sim[k] );
                if k1 <> fail then
                    k2:= Position( convR, sim[k] );
                    
                    if k1 > k2 then
                        pair:= [ s+rank+k1, s+rank+k2 ];
                    else
                        pair:= [ s+rank+k2, s+rank+k1 ];
                    fi;
                    
                    rel:= List( tab[pair[1]][pair[2]], ShallowCopy );
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
            im:= Zero( e[1] );
      
            for k in [1,3..Length(rel)-1] do
                im1:= f[1]^0;
                for j in [1,3..Length(rel[k])-1] do
                    im1:=(1/Factorial( rel[k][j+1] ))*im1*
                         ( imgs[rel[k][j]]^rel[k][j+1] );
                od;
      
                im:= im+MyVal( rel[k+1], 1 )*im1;
            od;
            
            imgs[ s+rank+Position( convR, posR[i] ) ]:= im;
            
        fi;
        
    od;    
    
    map:= Objectify( TypeOfDefaultGeneralMapping( U, uu,
                  IsSPGeneralMapping
                  and IsAlgebraGeneralMapping
                  and IsAlgebraHomomorphism
                  and IsQUEAtoUEAmap ),
                  rec( images:= imgs ) );
    
    return map;
end );

############################################################################
##
#M  ImageElm( <f>, <a> )
##
##
InstallMethod( ImageElm,
        "for a QUEAtoUEAmap",
        FamSourceEqFamElm, [ IsQUEAtoUEAmap, IsQEAElement ], 0, 
        function( f, a )
    
    local   MyVal,  ea,  imgs,  im,  k,  im1,  i;
    
    MyVal:= function( qelt, val )
    
        return Value( NumeratorOfRationalFunction(qelt), val )/
               Value( DenominatorOfRationalFunction(qelt), val );
    end;
    
    ea:= ExtRepOfObj( a );
    imgs:= f!.images;
    im:= 0*imgs[1];
    
    for k in [1,3..Length(ea)-1] do
        im1:= imgs[1]^0;
        for i in [1,3..Length(ea[k])-1] do
            if IsList( ea[k][i] ) then
                # we note that K_i -> 1; so we don't care about the
                # value of ea[k][i][2]...
                im1:= im1*ObjByExtRep( FamilyObj(imgs[1]),
                              [ [ imgs[ea[k][i][1]], ea[k][i+1] ], 1 ] );
            else
                im1:= im1*( imgs[ ea[k][i] ]^ea[k][i+1] )/Factorial( 
                              ea[k][i+1] );
            fi;
            
        od;
        im:= im + im1*MyVal( ea[k+1], 1 );
    od;
    return im;
    
end );

############################################################################
##
#M  \^( <x>, <u> )
##
##  Method for computing the action of uea elements; much the same as the
##  method for computing the action of elts of the corresponding Lie algebra
##  contained in the library.
##
InstallOtherMethod(\^,
        "for a UEA Lattice element and a weight rep element",
        true,
        [ IsUEALatticeElement, 
          IsWeightRepElement and IsPackedElementDefaultRep], 
        0,
        function( x, u )

    local   fam,  G,  L,  wvecs,  j,  hwv,  hw,  g,  elt,  lu,  m,  k,  
            n,  em,  er,  i,  len,  cf,  mon,  pos,  f,  mons,  cfts,  
            p,  im;

    fam:= FamilyObj( u );
    G:= fam!.grobnerBasis;
    L:= fam!.algebra;

    wvecs:= fam!.weightVectors;
    for j in [1..Length(wvecs)] do
        if wvecs[j]![1][1][1] = 1 then
            hwv:= wvecs[j];
            break;
        fi;
    od;
    hw:= hwv![1][1][3];

    g:= LatticeGeneratorsInUEA( L );

    # `elt' will be the acting element `x' written as UEALattice element.
    elt:= x;

    # `m' will be the UEALattice element corresponding to `x^u'.
    lu:= u![1];
    m:= Zero( g[1] );

    for k in [1,3..Length(lu)-1] do
        m:= m + lu[k+1]*elt*lu[k][2];
    od;

    n:= Length( PositiveRoots( RootSystem( L ) ) );

    # Now `m' is a linear combination of monomials of the form
    # `yhx', where `x' is a product of positive root vectors,
    # `h' is a product of Cartan elements, and `y' is a product of negative
    # root vectors. We know that `x' maps the highest weight vector to
    # zero. So only those monomials will give a contribution that do not
    # contain the x-part. Furthermore, `h' acts on the highest weight
    # vector as multiplication by a scalar. For all monomials that do
    # not contain the x-part, we replace the h-part by the appropriate scalar,
    # and we left-reduce the rest modulo `G'.

    em:= m![1];
    er:= [ ];
    for i in [1,3..Length(em)-1] do
        len:= Length(em[i])-1;
        if em[i][len] > n then

            if em[i][len] > 2*n then

                # The monomial ends with the h-part. We calculate the scalar.
                j:= len;
                while j-2 >= 1 and em[i][j-2] > 2*n do j:= j-2; od;
                cf:= em[i+1];
                for k in [j,j+2..len] do
                    cf:= cf*Binomial( hw[ em[i][k]-2*n ], em[i][k+1] );
                od;
                if cf <> 0*cf then
                    mon:= em[i]{[1..j-1]};
                    pos:= Position( er, mon );
                    if pos = fail then
                        Add( er, mon ); Add( er, cf );
                    else
                        er[pos+1]:= er[pos+1]+cf;
                        if er[pos+1] = 0*er[pos+1] then
                            Unbind( er[pos] ); Unbind( er[pos+1] );
                            er:= Filtered( er, x -> IsBound( x ) );
                        fi;
                    fi;
                fi;
            fi;

        else
            mon:= em[i]; cf:= em[i+1];
            pos:= Position( er, mon );
            if pos = fail then
                Add( er, mon ); Add( er, cf );
            else
                er[pos+1]:= er[pos+1]+cf;
                if er[pos+1] = 0*er[pos+1] then
                    Unbind( er[pos] ); Unbind( er[pos+1] );
                    er:= Filtered( er, x -> IsBound( x ) );
                fi;
            fi;
        fi;

    od;
    f:= ObjByExtRep( FamilyObj( m ), er );
    m:= LeftReduceUEALatticeElement( n, G[1], G[2], G[3], f );

    # Write `m' as a weight rep element again...
    mons:= [ ];
    cfts:= [ ];
    em:= m![1];

    for k in [1,3..Length(em)-1] do
        p:= PositionProperty( wvecs, x -> x![1][1][2]![1][1] = em[k] );
        Add( mons, ShallowCopy( wvecs[p]![1][1] ) );
        Add( cfts, em[k+1] );
    od;

    SortParallel( mons, cfts, function( a, b ) return a[1] < b[1]; end );
    im:= [ ];
    for k in [1..Length(mons)] do
        Add( im, mons[k] );
        Add( im, cfts[k] );
    od;
    return ObjByExtRep( FamilyObj( hwv ), im );

end );

##############################################################################
##
#M  HighestWeightModule( <U>, <hw> )
##
##  take the module over the Lie algebra, and let the elements of 
##  <U> act:
##
InstallMethod( HighestWeightModule,
        "for a uea corresponding to a root system",
        true, [ IsAlgebra and IsUEALatticeElementCollection,
                IsList ], 0,
        function( U, hw )
    
    local   V,  wvecs,  W,  B,  delmod,  delB;
    
    V:= HighestWeightModule( UnderlyingLieAlgebra( U ), hw );
    wvecs:= List( Basis(V), ExtRepOfObj );
    W:= LeftAlgebraModuleByGenerators( U, \^, wvecs );
    SetGeneratorsOfLeftModule( W, GeneratorsOfAlgebraModule( W ) );

    B:= Objectify( NewType( FamilyObj( W ),
                            IsBasis and
                            IsBasisOfAlgebraModuleElementSpace and
                            IsAttributeStoringRep ),
                   rec() );
    SetUnderlyingLeftModule( B, W );
    SetBasisVectors( B, GeneratorsOfLeftModule( W ) );
    delmod:= VectorSpace( LeftActingDomain(W), wvecs);
    delB:= BasisOfWeightRepSpace( delmod, wvecs );
    delB!.echelonBasis:= wvecs;
    delB!.heads:= List( [1..Length(wvecs)], x -> x );
    delB!.baseChange:= List( [1..Length(wvecs)], x -> [[ x, 1 ]] );
    B!.delegateBasis:= delB;
    SetBasis( W, B );
    SetDimension( W, Length( wvecs ) );
    return W;
    
end );

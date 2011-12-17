############################################################################
##
#W  rmat.gi                  QuaGroup                         Willem de Graaf
##
##
##  Function for computing R-matrices.
##


QGPrivateFunctions.TensorIsomData:=  function( V, W )
    
    #  Here <V>, <W> are two modules over the same quantized enveloping 
    #  algebra <A>.
    #  This function returns a linear map $\theta : V\otimes W\to V\otimes W$ 
    #  such that $\theta\circ P$ is an isomorphism of the $A$-modules
    #  $W\otimes V$ and $V\otimes W$. Here $P : W\otimes V\to V\otimes W$
    #  is the map defined by $P(w\otimes v) = v\otimes w$.
    #
    #  More precisely: a record is returned containing the tensor space,
    #  and a lit of images. This data is used in the two subsequent functions.


    local   basis_of_wtspace,  theta_mu,  A,  R,  sim,  bas,  B,  
            wtsV,  wtsW,  cc,  i,  j,  mu,  cands,  VW,  bVW,  theta,  
            sm,  Q,  S,  d,  reps,  inds,  v,  the_fct_f,  vec,  pos,  
            w1,  w2,  qpar,  Qi;

     basis_of_wtspace:= function( rt )
    
         # `rt' is a positive weight, represented as a list of cfts,
         # [k1,..,kn] such that wt = \sum ki \alpha_i (sum of simple
         # roots). 
         
         # This function returns all monomials of weight `rt' in the
         # positive (or negative) part of the uea. The same algorithm
         # as in canbas.gi (GetCanonicalElements) is used.
         
         local   posR,  nu,  i,  oldlev,  mlist,  deg,  newlev,  mon,  
                 rts,  j,  rr,  pos,  mn1;
         
         posR:= PositiveRootsInConvexOrder( R );
         nu:= 0*[1..Length(posR)];
         for i in [1..Length(rt)] do
             nu[ Position( posR , SimpleSystemNF(R)[i] ) ]:= rt[i];
         od;
         oldlev:= [ nu ];
         mlist:= [ nu ];
         deg:= Sum( rt )-1;
         while deg >= 1 do
             newlev:= [ ];
             for mon in oldlev do
                 rts:= [ ];
                 for i in [1..Length(mon)] do
                     if mon[i] <> 0 then
                         Add( rts, [ i, posR[i] ] );
                     fi;
                 od;
                 for i in [1..Length(rts)] do
                     for j in [i+1..Length(rts)] do
                         rr:= rts[i][2]+rts[j][2];
                         pos := Position( posR, rr );
                         if pos <> fail then
                             mn1:= ShallowCopy( mon );
                             mn1[rts[i][1]]:= mn1[rts[i][1]]-1;
                             mn1[rts[j][1]]:= mn1[rts[j][1]]-1;
                             mn1[pos]:= mn1[pos]+1;
                             if not mn1 in newlev then
                                 Add( newlev, mn1 );
                             fi;
                         fi;
                     od;
                 od;
             od;
             oldlev:= newlev;
             Append( mlist, newlev );
             deg:= deg-1;
         od;
    
          return mlist;
     end;


     theta_mu:= function( mu )
    
         local   g,  bas_mu,  theta,  ww,  im,  k,  mn1,  mn2,  i,  f,  
                 e,  cf,  w0,  lenw0,  qa,  vec,  pos,  w1,  w2,  et;
    
         # We construct the action of theta_mu on the tensor product VW, 
         # as a list of images...

         g:= GeneratorsOfAlgebra( A );
         bas_mu:= basis_of_wtspace( mu );
         theta:= [ ];

         ww:= mu*CartanMatrix( R ); # i.e., mu written as linear combination 
                                    # of fundamental weights.
    
         im:= List( [1..Length(bVW)], x -> ExtRepOfObj( Zero(VW) ) );

         for k in [1..Length(bas_mu)] do

              # We construct the monomials corresponding to `bas_mu[k]', `mn1'
              # will represent the monomial in the negative part, 
              # `mn2' the monomial in the positive part.
              mn1:= [ ];
              mn2:= [ ];
              for i in [1..Length(bas_mu[k])] do
                  if bas_mu[k][i] <> 0 then
                      Add( mn1, bas_mu[k][i] ); Add( mn1, i );
                      Add( mn2, bas_mu[k][i] );
                      Add( mn2, i+Length( PositiveRoots(R) ) +
                           Length( CartanMatrix(R) ) );
                  fi;
              od;
             
              f:= ObjByExtRep( FamilyObj( g[1] ), [ Reversed(mn1), qpar^0] );
              e:= ObjByExtRep( FamilyObj( g[1] ), [ Reversed(mn2), qpar^0] );

              # Now we calculate the coefficient `cf' such that 
              # (cf*f,e)=1 (cf. Jantzen, p. 168).
        
              cf:= qpar^0;
              w0:= LongestWeylWord( R );
              lenw0:= Length( w0 );
        
              for i in [1..lenw0] do
                  cf:= cf*( ( -1 )^bas_mu[k][i] );
                  qa:= qpar^( B[w0[i]][w0[i]]/2 );
                  cf:= cf*( qa^( -bas_mu[k][i]*(bas_mu[k][i]-1)/2 ) );
                  cf:= cf*( (qa-qa^-1)^bas_mu[k][i] );
                  cf:= cf*GaussianFactorial( bas_mu[k][i], qa );
              od;
              f:= f*cf;

              for i in [1..Length(bVW)] do
                  
                  vec:= ExtRepOfObj( ExtRepOfObj( bVW[i] ) )[1][1];
                  pos:= PositionProperty( wtsV[2], ll -> vec in ll );
                  w1:= wtsV[1][pos];
                  vec:= ExtRepOfObj( ExtRepOfObj( bVW[i] ) )[1][2];
                  pos:= PositionProperty( wtsW[2], ll -> vec in ll );
                  w2:= wtsW[1][pos];

            # w1 is the weight of the first component of the tensor element,
            # and w2 the weight of the seond component. If w1-mu is not a 
            # weight of V, or w2+mu is not a weight of W, then 
            # theta_mu(bVW[i])=0, so that we do not have to calculate it.

                  if w1-ww in wtsV[1] and w2+ww in wtsW[1] then

                     # We act with f<x>e on bVW[i], and normalize the result.

                     et:= List( ExtRepOfObj( ExtRepOfObj( bVW[i] ) ), 
                                 ShallowCopy );
                     et[1][1]:= f^et[1][1];
                     et[1][2]:= e^et[1][2];
                     et:= ObjByExtRep( FamilyObj(ExtRepOfObj(bVW[i])), et );
                     et![2]:= false;
                     im[i]:= im[i]+ConvertToNormalFormMonomialElement(et);
                  fi;
              od;
        
          od;   
          return List( im, x -> ObjByExtRep( FamilyObj( bVW[1] ), x ) );
     end;

     A:= LeftActingAlgebra( V );
     qpar:= QuantumParameter( A );
     
     # Some easy tests....
     if A <> LeftActingAlgebra( W ) then
        Error( "both modules must have the same left acting algebra" );
     fi;

     if not IsQuantumUEA( A ) then
        Error( "the modules must be defined over a quantized uea" );
     fi;

     R:= RootSystem( A );
     sim:= SimpleRootsAsWeights( R );
     bas:= Basis( VectorSpace( Rationals, sim ), sim );
     B:= BilinearFormMatNF( R );
 
     # We extract the set of weights from V and W; note that here we
     # use the fact that we know the representation of elements of V,W... 
     wtsV:= WeightsAndVectors( V );

     wtsW:= WeightsAndVectors( W );

     # We have that the result \theta is a sum of \theta_mu, where mu > 0
     # is a difference of two weights in wtsV, and a difference of two weights
     # in wtsW. We calculate the set of such mu; they will be represented as
     # linear combinations of the simple roots.

     cc:= [ ];
     for i in [1..Length(wtsV[1])] do
         for j in [1..Length(wtsV[1])] do
             mu:= wtsV[1][i]-wtsV[1][j];
             # Write mu as a lin co of simple roots:
             mu:= Coefficients( bas, mu );
             # Add mu if mu > 0:
             if ForAll( mu, x -> x >=0 ) and mu <> 0*mu then
                 AddSet( cc, mu );
             fi;
         od;
     od;
    
     # Now the set of candidates is formed by differences of weights of W,
     # that also appear in `cc':
     cands:= [ ];
     for i in [1..Length(wtsW[1])] do
         for j in [1..Length(wtsW[1])] do
             mu:= wtsW[1][i]-wtsW[1][j];
             mu:= Coefficients( bas, mu );
             if ForAll( mu, x -> x >= 0) and mu <> 0*mu and mu in cc then
                 AddSet( cands, mu );
             fi;
         od;
     od; 

     VW:= TensorProductOfAlgebraModules( V, W );
     bVW:= Basis( VW );
     theta:= Sum( List( cands, x -> theta_mu( x ) ) ) + 
                  List( Basis(VW), x -> x );   # i.e., adding the identity...

         
     # Let P denote the weight lattice and T the root latice. Then
     # P/T is a finite Abelian group. We calculate a set of representatives of 
     # that group. Then we construct a 
     # function for writing an arbitrary element of 
     # P as one of these elements plus an element of T.

     # We calculate the Smith normal form on the Cartan matrix, and use 
     # Sims, Prop. 3.3 of Chapter 8.
    
     sm:= NormalFormIntMat( CartanMatrix( R ), 13 );
     Q:= sm.coltrans;
     S:= sm.normal;
    
     d:= List( [1..Length(S)], x -> S[x][x] );

     # We have that P/T = Z_{d1} + ... + Z_{dr}, where r=Length(d).
     # A representative of a weight w is calculated by taking w*Q, and
     # mapping each component into Z_{di}. So the set of all representatives
     # is formed by [ k1,...,kr ], where 0 <= ki <= di.
     # `reps' will be a set of weights, the i-th element of reps is zero
     # if di=0, otherwise it will be a pre-image of [0,0...,0,1,0,...0]
     # (1 on the i-th position).
     # Then in the function the_fct_f a canonical pre-image can be calculated
     # by taking the appropriate linear combination of the elements from reps.
    
     reps:= [ ];
     Qi:= Q^-1;
     for i in [1..Length(d)] do

         if d[i] = 0 then

             Add( reps, ListWithIdenticalEntries( Length(d), 0 ) );

         else
              
             v:= ListWithIdenticalEntries( Length(d), 0 );
             v[i]:= 1;
             Add( reps, v*Qi );
             
         fi;
     od;   

     # `the_fct_f' will be a function as in Jantzen, \S 7.3
    
     the_fct_f:= function( w1, w2 )
        
         local   v,  j,  wt1,  wt2,  nu1,  nu2,  cfwt1,  cfwt2,  cfnu1,  cfnu2, 
                 ip;
        
         # First we map `w1' to a representative
         v:= w1*Q;
         for j in [1..Length( v )] do
             if v[j] >= d[j] then
                 while v[j] >= d[j] do v[j]:= v[j]-d[j]; od;
             elif v[j] < 0 then
                 while v[j] < 0 do v[j]:= v[j]+d[j]; od;
             fi;
         od;

         # Then we take a linear combination of elements of `reps':
         wt1:= 0*w1;
         for j in [1..Length(v)] do
             wt1:= wt1+v[j]*reps[j];
         od;
        
         # Now we map w2 to a representative
         v:= w2*Q;
         for j in [1..Length( v )] do
             if v[j] >= d[j] then
                 while v[j] >= d[j] do v[j]:= v[j]-d[j]; od;
             elif v[j] < 0 then
                 while v[j] < 0 do v[j]:= v[j]+d[j]; od;
             fi;
         od;
        
         # Then we take a linear combination of elements of `reps':
         wt2:= 0*w2;
         for j in [1..Length(v)] do
             wt2:= wt2+v[j]*reps[j];
         od;

         # Write wt1, wt2, etc as linear combinations of simple roots, and get
         # their inner product.        

         nu1:= w1-wt1;
         nu2:= w2-wt2;

         cfwt1:= Coefficients( bas, wt1 );
         cfwt2:= Coefficients( bas, wt2 );
         cfnu1:= Coefficients( bas, nu1 );
         cfnu2:= Coefficients( bas, nu2 );
     
         ip:= -cfwt1*( B*cfnu2 );
         ip:= ip - cfwt2*( B*cfnu1 );
         ip:= ip - cfnu1*( B*cfnu2 );
        
         return qpar^ip;

     end;

     # We compose theta and f, and get the result.

     for i in [1..Length( bVW )] do
         vec:= ExtRepOfObj( ExtRepOfObj( bVW[i] ) )[1][1];
         pos:= PositionProperty( wtsV[2], ll -> vec in ll );
         w1:= wtsV[1][pos];
         vec:= ExtRepOfObj( ExtRepOfObj( bVW[i] ) )[1][2];
         pos:= PositionProperty( wtsW[2], ll -> vec in ll );
         w2:= wtsW[1][pos];
         theta[i]:= the_fct_f( w1, w2 )*theta[i];        
     od;

     return rec( space:= VW, images:= theta );
       
       

end;


InstallMethod( IsomorphismOfTensorModules,
        "for two modules over a qea",
        true, [ IsAlgebraModule, IsAlgebraModule ], 0,
        function( V, W )
    
    local   data,  hom,  VW,  bVW,  images,  fam2,  fam1,  i,  e;
    
    data:= QGPrivateFunctions.TensorIsomData( W, V );
    hom:= LeftModuleHomomorphismByImagesNC( data.space, data.space, 
                  AsList( Basis(data.space) ), data.images );
    
    VW:= TensorProductOfAlgebraModules( V, W );
    # note that data.space is W<x>V!
    
    bVW:= AsList( Basis(VW) );
    images:= [];
    fam2:= FamilyObj( Basis(data.space)[1] );
    fam1:= FamilyObj( ExtRepOfObj( Basis(data.space)[1] ) );
    
    for i in [1..Length(bVW)] do
        e:= ShallowCopy( ExtRepOfObj( ExtRepOfObj( bVW[i] ) ) );
        e[1]:= Reversed( e[1] ); # this constitutes the action of P...
        e:= ObjByExtRep( fam1, e );
        e:= ObjByExtRep( fam2, e );
        Add( images, Image( hom, e ) );
    od;
    
    return LeftModuleHomomorphismByImagesNC( VW, data.space, bVW, images );
    
end );

InstallMethod( RMatrix, 
        "for a module over a quea",
        true, [ IsAlgebraModule ], 0,
        function( V )
    
    local   data;
    
    data:= QGPrivateFunctions.TensorIsomData( V, V );
    return List( data.images, x -> Coefficients( Basis( data.space ), x ) );
end );

    
  


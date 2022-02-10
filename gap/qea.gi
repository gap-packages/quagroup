#############################################################################
##
#W  qea.gi                  QuaGroup                           Willem de Graaf
##
##
##  Constructors for quantized enveloping algebras, and highest
##  weight modules.
##

############################################################################
##
## Some functions for dealing with "generalised binomials" as they 
## appear in the basis of the Lusztig Z-form of the quea. These functions
## rewrite elements as linear combinations of basis elements.
## 
## A binomial as the one below is expressed as [ delta, s ], where
## delta = 0,1 according to whether we multiply by K or not.
## An expression is a linear combination of such things.
##
QGPrivateFunctions.Multiply_Bin_Expr:= function( s, exx )

     # expresses
     #
     #    / K \ 
     #    |   | * exx
     #    \ s / 
     #
     # as a linear combination of such things...
     # The algorithm is simply based on the definition of the binomial,
     # and om some relations found in Lusztig, J. Amer math Soc. 1990
     # 278.

     local add_elm, expr, i, j, newexp, m, n, cf;

     add_elm:= function( ee, elm, cf )

          local pos;

          pos:= Position( ee, elm );
          if pos = fail then
             Add( ee, elm ); Add( ee, cf );
          else
             ee[pos+1]:= ee[pos+1]+ cf;
             if ee[pos+1]=0*ee[pos+1] then
                Unbind( ee[pos] ); Unbind( ee[pos+1] );
                ee:= Filtered( ee, x -> IsBound(x) );
             fi;
          fi;
          return ee;
     end;

     expr:= exx;
     for i in [1..s] do
         # multiply expr by q^(-i+1)K-q^(i-1)K^-1:
         
         newexp:= [ ];
         for j in [1,3..Length(expr)-1] do
             m:= expr[j];
             if m[1] = 0 then
                n:= ShallowCopy( m );
                n[1]:= 1;
                newexp:= add_elm( newexp, n, expr[j+1]*_q^(-i+1) );
             else
                n:= ShallowCopy( m );
                n[2]:= n[2]+1;
                newexp:= add_elm( newexp, n,
                    expr[j+1]*_q^(-i+1)*_q^m[2]*(_q^n[2]-_q^-n[2]) );
                n:= ShallowCopy( m );
                n[1]:= 0;
                newexp:= add_elm( newexp, n,
                    expr[j+1]*_q^(-i+1)*_q^(2*m[2]) );
             fi;
             
             if m[1]=0 then
                n:= ShallowCopy( m );
                n[2]:= n[2]+1;
                newexp:= add_elm( newexp, n,
                    expr[j+1]*_q^(i-1)*_q^-m[2]*(_q^n[2]-_q^-n[2]) );
                n:= ShallowCopy( m );
                n[1]:= 1;
                newexp:= add_elm( newexp, n,
                    -expr[j+1]*_q^(i-1)*_q^(-2*m[2]) );
             else   
                n:= ShallowCopy( m );
                n[1]:= 0;
                newexp:= add_elm( newexp, n, -expr[j+1]*_q^(i-1) );
             fi;
         od;
         expr:= newexp;
     od;

     cf:= (_q-_q^-1)^s*GaussianFactorial( s, _q );
     for i in [2,4..Length(expr)] do
         expr[i]:= expr[i]/cf;
     od;
     return expr;
end;    

QGPrivateFunctions.Multiply_K_Expr:= function( exx )

     # multiply exx by K...

     local add_elm, expr, i, m;

     add_elm:= function( ee, elm, cf )

          local pos;

          pos:= Position( ee, elm );
          if pos = fail then
             Add( ee, elm ); Add( ee, cf );
          else
             ee[pos+1]:= ee[pos+1]+ cf;
             if ee[pos+1]=0*ee[pos+1] then
                Unbind( ee[pos] ); Unbind( ee[pos+1] );
                ee:= Filtered( ee, x -> IsBound(x) );
             fi;
          fi;
          return ee;
     end;

     expr:= [ ];
     for i in [1,3..Length(exx)-1] do
         m:= ShallowCopy( exx[i] );
         if m[1] = 0 then
            m[1]:= 1;
            expr:= add_elm( expr, m, exx[i+1] );
         else
            m[2]:= m[2]+1;
            expr:= add_elm( expr, m, exx[i+1]*_q^(m[2]-1)*(_q^m[2]-_q^-m[2]) );
            m:= ShallowCopy( exx[i] );
            m[1]:= 0;
            expr:= add_elm( expr, m, exx[i+1]*_q^(2*m[2]) );
         fi;
     od;

     return expr;
end;

QGPrivateFunctions.Multiply_Exp_Exp:= function( ex1, ex2 )

      # multiply the two expressions ex1, ex2.

     local add_elm, res, expr, i, j, m;

     add_elm:= function( ee, elm, cf )

          local pos;

          pos:= Position( ee, elm );
          if pos = fail then
             Add( ee, elm ); Add( ee, cf );
          else
             ee[pos+1]:= ee[pos+1]+ cf;
             if ee[pos+1]=0*ee[pos+1] then
                Unbind( ee[pos] ); Unbind( ee[pos+1] );
                ee:= Filtered( ee, x -> IsBound(x) );
             fi;
          fi;
          return ee;
     end;

     res:= [ ];
     for i in [ 1, 3 .. Length(ex1)-1] do
         expr:= ex2;
         m:= ex1[i];
         if m[1] <> 0 then
            expr:= QGPrivateFunctions.Multiply_K_Expr( expr );
         fi;
         expr:= QGPrivateFunctions.Multiply_Bin_Expr( m[2], expr );
         for j in [1,3..Length(expr)-1] do
            res:= add_elm( res, expr[j], expr[j+1]*ex1[i+1] );
         od;
     od;

     return res;
end;


############################################################################

############################################################################
##
#M   PrintObj( <wr> )
##
##   We need a new PrintObj method for weight rep elements because in the one
##   in the library there is a statement e[k+1] > 0, which will fail for
##   q-elements. 
##
InstallMethod( PrintObj,
        "for weight rep element",
        true,
       [ IsWeightRepElement and IsPackedElementDefaultRep ], 0,
       function( v )

    local e,k;

    e:= v![1];
    if e = [] then
        Print( "0*v0" );
    else
        for k in [1,3..Length(e)-1] do
            if k>1 and not (IsRat(e[k+1]) and e[k+1]<0) then
                Print("+" );
            fi;
            Print( e[k+1]*e[k][2], "*v0" );
        od;
    fi;

end );



############################################################################
##
#M  ObjByExtRep( <fam>, <list> )
#M  ExtRepOfObj( <obj> )
##
InstallMethod( ObjByExtRep,
   "for family of QEA elements, and list",
   true, [ IsQEAElementFamily, IsList ], 0,
   function( fam, list )
#+
    return Objectify( fam!.packedQEAElementDefaultType,
                    [ Immutable(list) ] );
end );

InstallMethod( ExtRepOfObj,
   "for an QEA element",
   true, [ IsQEAElement ], 0,
   function( obj )
#+
   return obj![1];

end );

###########################################################################
##
#M  PrintObj( <m> ) . . . . . . . . . . . . . . . . for an QEA element
##
InstallMethod( PrintObj,
        "for QEA element",
        true, [IsQEAElement and IsPackedElementDefaultRep], 0,
        function( x )

    local   lst,  k, i, n, rank;

    # This function prints an element of a quantized enveloping algebra.

    lst:= x![1];
    n:= FamilyObj( x )!.noPosRoots;
    rank:= FamilyObj( x )!.rank;
    if lst=[] then
        Print("0");
    else
        for k in [1,3..Length(lst)-1] do
            if k>1 then
                Print("+");
            fi;
            if lst[k+1] <> lst[k+1]^0 then
                Print( "(",lst[k+1],")*");
            fi;
            if lst[k] = [] then
                Print("1");
            else

                for i in [1,3..Length(lst[k])-1] do
                    if IsList( lst[k][i] ) then
                       if lst[k][i][2] > 0 then
                          Print( "K", lst[k][i][1]-n );
                       fi;
                       if lst[k][i+1] > 0 then
                          Print( "[ K",lst[k][i][1]-n," ; ", 
                                              lst[k][i+1], " ]");
                       fi;
                    elif lst[k][i] <=n then
                        Print("F",lst[k][i]);
                        if lst[k][i+1]>1 then
                            Print("^(",lst[k][i+1],")");
                        fi;
                    else
                        Print("E",lst[k][i]-n-rank);
                        if lst[k][i+1]>1 then
                            Print("^(",lst[k][i+1],")");
                        fi;
                    fi;
                    if i <> Length(lst[k])-1 then
                        Print("*");
                    fi;
                od;
            fi;

        od;

    fi;

end );

#############################################################################
##
#M  OneOp( <m> ) . . . . . . . . . . . . . . . . for a QEA element
#M  ZeroOp( <m> ) . . . . . . . . . . . . . . .  for a QEA element
#M  \<( <m1>, <m2> ) . . . . . . . . . . . . . . for two QEA elements
#M  \=( <m1>, <m2> ) . . . . . . . . . . . . . . for two QEA elements
#M  \+( <m1>, <m2> ) . . . . . . . . . . . . . . for two QEA elements
#M  \-( <m> )     . . . . . . . . . . . . . . for a QEA element
#M  \in( <U>, <u> )  . . . . . . . . . . . . . . for QEA, and element
##
InstallMethod( OneOp,
        "for QEA element",
        true, [ IsQEAElement and IsPackedElementDefaultRep ], 0,
        function( x )

    return ObjByExtRep( FamilyObj( x ), [ [], FamilyObj(x)!.quantumPar^0 ] );

end );

InstallMethod( ZeroOp,
        "for QEA element",
        true, [ IsQEAElement and IsPackedElementDefaultRep ], 0,
        function( x )

    return ObjByExtRep( FamilyObj( x ), [ ] );

end );


InstallMethod( \<,
                "for two QEA elements",
        IsIdenticalObj, [ IsQEAElement and IsPackedElementDefaultRep,
                IsQEAElement and IsPackedElementDefaultRep ], 0,
        function( x, y )
    return x![1]< y![1];
end );

InstallMethod( \=,
                "for two QEA elements",
        IsIdenticalObj, [ IsQEAElement and IsPackedElementDefaultRep,
                IsQEAElement and IsPackedElementDefaultRep ], 0,
        function( x, y )


    return x![1] = y![1];
end );


InstallMethod( \+,
        "for two QEA elements",
        true, [ IsQEAElement and IsPackedElementDefaultRep,
                IsQEAElement and IsPackedElementDefaultRep], 0,
        function( x, y )

    local   ex,  ey,  mons,  cfs,  i,  lst, len;
    
    # Insert one sorted list in the second one; 
    # can be done much more efficiently!
    
    ex:= x![1]; ey:= y![1];
    mons:= [ ]; cfs:= [ ];
    for i in [1,3..Length(ex)-1] do
        Add( mons, ex[i] ); Add( cfs, ex[i+1] );
    od;

    for i in [1,3..Length(ey)-1] do
        Add( mons, ey[i] ); Add( cfs, ey[i+1] );
    od;
    SortParallel( mons, cfs );
    lst:= [ ];
    for i in [1..Length( mons )] do
        len:= Length(lst);
        if len > 0 and lst[len-1] = mons[i] then
            lst[len]:= lst[len]+cfs[i];
            if lst[len] = 0*lst[len] then
                Unbind( lst[len-1] ); Unbind( lst[len] );
                lst:= Filtered( lst, x -> IsBound(x) );
            fi;

        else
            Add( lst, mons[i] ); Add( lst, cfs[i] );
        fi;
    od;
    return ObjByExtRep( FamilyObj(x), lst );
end );


InstallMethod( AdditiveInverseSameMutability,
        "for QEA element",
        true, [ IsQEAElement and IsPackedElementDefaultRep ], 0,
        function( x )

    local   ex,  i;

    ex:= ShallowCopy(x![1]);
    for i in [2,4..Length(ex)] do
        ex[i]:= -ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end );

InstallMethod( AdditiveInverseMutable,
        "for QEA element",
        true, [ IsQEAElement and IsPackedElementDefaultRep ], 0,
        function( x )

    local   ex,  i;

    ex:= ShallowCopy(x![1]);
    for i in [2,4..Length(ex)] do
        ex[i]:= -ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end );

#############################################################################
##
#M  \*( <scal>, <m> ) . . . . . . . . .for a scalar and a QEA element
#M  \*( <m>, <scal> ) . . . . . . . . .for a scalar and a QEA element
##
InstallMethod( \*,
        "for scalar and QEA element",
        true, [ IsScalar, IsQEAElement and
                IsPackedElementDefaultRep ], 0,
        function( scal, x )

    local   ex,  i;
    
    if IsZero( scal ) then return Zero(x); fi;
    ex:= ShallowCopy( x![1] );
    for i in [2,4..Length(ex)] do
        ex[i]:= scal*ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end);

InstallMethod( \*,
        "for QEA element and scalar",
        true, [ IsQEAElement and IsPackedElementDefaultRep,
                IsScalar ], 0,
        function( x, scal )

    local   ex,  i;
    
    if IsZero( scal ) then return Zero(x); fi;
    ex:= ShallowCopy( x![1] );
    for i in [2,4..Length(ex)] do
        ex[i]:= scal*ex[i];
    od;
    return ObjByExtRep( FamilyObj(x), ex );
end);

InstallMethod( \in,
        "for QEA element and QEA",
        true, [ IsQEAElement, IsQuantumUEA ], 0,
        function( u, U )
    
    return IsIdenticalObj( ElementsFamily( FamilyObj(U) ), FamilyObj(u) );
end );

#############################################################################
##
#F  IsSpaceOfQEAElements( <V> )
##
##  If <V> is a space of elements of a quantized universal enveloping algebra,
##  then the `NiceFreeLeftModuleInfo' value of <V> is a record with the
##  following components.
##  \beginitems
##  `family' &
##     the elements family of <V>,
##
##  `monomials' &
##     a list of monomials occurring in the generators of <V>,
##
##  `zerocoeff' &
##     the zero coefficient of elements in <V>,
##
##  `zerovector' &
##     the zero row vector in the nice free left module,
##
##  \enditems
##  The `NiceVector' value of $v \in <V>$ is defined as the row vector of
##  coefficients of $v$ w.r.t. the list `monomials'.
##
##
##  This code is based on code by Thomas Breuer for the similar case
##  of vector spaces spanned by polynomials.
##
DeclareHandlingByNiceBasis( "IsSpaceOfQEAElements",
    "for free left modules of elements of a quantized uea" );

#############################################################################
##
#M  NiceFreeLeftModuleInfo( <V> )
#M  NiceVector( <V>, <v> )
#M  UglyVector( <V>, <r> )
##
InstallHandlingByNiceBasis( "IsSpaceOfQEAElements", rec(
        detect := function( F, gens, V, zero )
                  return IsQEAElementCollection( V );
        end,

          NiceFreeLeftModuleInfo := function( V )
            local gens,
                  monomials,
                  gen,
                  list,
                  zero,
                  info;

            gens:= GeneratorsOfLeftModule( V );

            monomials:= [];

            for gen in gens do
                list:= ExtRepOfObj( gen );
                UniteSet( monomials, list{ [ 1, 3 .. Length( list ) - 1 ] } );
            od;
            
            zero:= Zero( LeftActingDomain( V ) );
            info:= rec( monomials := monomials,
                        zerocoeff := zero,
                        family    := ElementsFamily( FamilyObj( V ) ) );
            
        # For the zero row vector, catch the case of empty `monomials' list.
            if IsEmpty( monomials ) then
                info.zerovector := [ zero ];
            else
                info.zerovector := ListWithIdenticalEntries( 
                                           Length( monomials ), zero );
            fi;
            
            return info;
        end,
          
        NiceVector := function( V, v )
            local info, c, monomials, i, pos;
            info:= NiceFreeLeftModuleInfo( V );
            c:= ShallowCopy( info.zerovector );
            v:= ExtRepOfObj( v );
            monomials:= info.monomials;
            for i in [ 2, 4 .. Length( v ) ] do
                pos:= Position( monomials, v[ i-1 ] );
                if pos = fail then
                    return fail;
                fi;
                c[ pos ]:= v[i];
            od;
            return c;
        end,
          
        UglyVector := function( V, r )
            local info, list, i;
            info:= NiceFreeLeftModuleInfo( V );
            if Length( r ) <> Length( info.zerovector ) then
                return fail;
            elif IsEmpty( info.monomials ) then
                if IsZero( r ) then
                    return Zero( V );
                else
                    return fail;
                fi;
            fi;
            list:= [];
            for i in [ 1 .. Length( r ) ] do
                if r[i] <> info.zerocoeff then
                    Add( list, info.monomials[i] );
                    Add( list, r[i] );
                fi;
            od;
            return ObjByExtRep( info.family, list );
        end ) );


#############################################################################
##
#F  CollectQEAElement( <sim>, <rts>, <B>, <s>, <rank>, <Mtab>, <expr> )
##
##
InstallGlobalFunction( CollectQEAElement,
        
        function( fam, expr )

    # `sim' are the simple roots.
    # `rts' are the roots in convex order.
    # `B' is the matrix of the bilinear form.
    # `s' is the number of positive roots.
    # `rank' is the rank of the root system.
    # `Mtab' is the multiplication table.
    # `qpar' is the quantum parameter.
    # `expr' is the thing that needs to be collected.
    
    local   comm_rule,  todo,  res,  m,  cf,  k,  found,  pos,  k1,  
            k2,  r,  rel,  start,  tail,  i,  mn,  m1,  j, qp, coef, 
            list1, list2, binomial_with_cst, kbit, k_normal, ee, store,
            R, sim, rts, B, s, rank, Mtab, qpar, isgeneric;

    comm_rule:= function( rel, j, i, m, n, r )
        
        # commutation rule for x_j^mx_i^n, where x_jx_i=qpar^rx_ix_j+rel
  
        # We use the following formula (easily proved by induction):
        #
        # x_j^mx_i^n = q^{nmr}x_i^nx_j^m + \sum_{l=0}^{n-1} \sum_{k=0}^{m-1}
        #     q^{(lm+k)r} xi^l xj^{m-1-k}Rx_j^kx_i^{n-1-l}, where R = rel.
        
        local   rule,  l,  k,  cf,  u,  mn, start, tail, qi, qj, den, t;
        
        if j > s + rank then
            qj:= _q^( rts[j-s-rank]*( B*rts[j-s-rank] )/2 );
        else
            qj:= _q^( rts[j]*( B*rts[j] )/2 );
        fi;
        if i > s +rank then
            qi:= _q^( rts[i-s-rank]*( B*rts[i-s-rank] )/2 );
        else
            qi:= _q^( rts[i]*( B*rts[i] )/2 );
        fi;
        
        den:= GaussianFactorial( m, qj )*GaussianFactorial( n, qi );

        rule:= [ [ i, n, j, m], qpar^(n*m*r) ];
        for l in [0..n-1] do
            for k in [0..m-1] do
                cf:= _q^((l*m+k)*r)/den;
                start:= [ ];
                if l <> 0 then
                    Add( start, i ); Add( start, l );
                    cf:= cf*GaussianFactorial( l, qi );
                fi;
                if m-1-k <> 0 then
                    Add( start, j ); Add( start, m-1-k );
                    cf:= cf*GaussianFactorial( m-1-k, qj );
                fi;
                tail:= [];
                if k <> 0 then
                    Add( tail, j ); Add( tail, k );
                    cf:= cf*GaussianFactorial( k, qj );
                fi;
                if n-1-l <> 0 then
                    Add( tail, i ); Add( tail, n-1-l );
                    cf:= cf*GaussianFactorial( n-1-l, qi );
                fi;

                for u in [1,3..Length(rel)-1] do
                    mn:= ShallowCopy( start );
                    Append( mn, rel[u] );
                    Append( mn, tail );
                    Add( rule, mn ); Add( rule, cf*rel[u+1] );
                od;
            od;
        od;

        return rule;
    end;
    
    binomial_with_cst:= function( c, t )

     # The binomial
     #
     #     / K; c \
     #     |      |
     #     \  t   /
     #
     # expressed in the integral basis. We use relations from Lusztig's 
     # paper.

     local add_elm, i, j, res, Kmin, expr;

     add_elm:= function( ee, elm, cf )

          local pos;

          if cf = 0*cf then return ee; fi;

          pos:= Position( ee, elm );
          if pos = fail then
             Add( ee, elm ); Add( ee, cf );
          else
             ee[pos+1]:= ee[pos+1]+ cf;
             if ee[pos+1]=0*ee[pos+1] then
                Unbind( ee[pos] ); Unbind( ee[pos+1] );
                ee:= Filtered( ee, x -> IsBound(x) );
             fi;
          fi;
          return ee;
     end;


     res:= [ ];
     if c <= -1 then
        c:= -c;
        for j in [0..t] do
            expr:= [ [ 0, t-j ], (-1)^j*_q^( c*(t-j) )*
                        GaussianBinomial(  c+j-1, j, _q ) ];
            for i in [1..j] do
                expr:= QGPrivateFunctions.Multiply_K_Expr( expr );
            od;
            for i in [1,3..Length(expr)-1] do
                res:= add_elm( res, expr[i], expr[i+1] );
            od;
        od;
     else
        Kmin:= [ [ 1, 0 ], _q^0, [ 0, 1], _q^-1-_q ];
        for j in [0..t] do
            expr:= [ [ 0, t-j ],  _q^( c*(t-j) )*
                        GaussianBinomial(  c, j, _q ) ];
            for i in [1..j] do
                expr:= QGPrivateFunctions.Multiply_Exp_Exp( Kmin, expr );
            od;
            for i in [1,3..Length(expr)-1] do
                res:= add_elm( res, expr[i], expr[i+1] );
            od;
        od;
      fi;
      return res;
    end;

    R:= fam!.rootSystem;
    sim:= SimpleSystemNF(R);
    rts:= fam!.convexRoots;
    B:= BilinearFormMatNF(R);
    s:= fam!.noPosRoots;
    rank:= fam!.rank;
    Mtab:= fam!.multTab;
    qpar:= fam!.quantumPar;

    if qpar = _q then 
        isgeneric:= true;
    else
        isgeneric:= false;
    fi;

    # In the program we use ... [ i, d, a ], s ... for
    #
    #       / Ki; a \
    #  Ki^d |       |
    #       \   s   /
    #

    todo:= expr;

    for k in [1,3..Length(todo)-1] do
        for i in [1,3..Length(todo[k])-1] do
            if IsList( todo[k][i] ) and Length( todo[k][i] ) = 2 then
               todo[k][i]:= ShallowCopy( todo[k][i] );
               Add( todo[k][i], 0 );
            fi;
        od;
    od;

    res:= [ ];
    while todo <> [] do

        m:= todo[1];
        cf:= todo[2];

        for i in [1,3..Length(m)-1] do
            if IsList( m[i] ) and Length( m[i] ) = 2 then
               m[i]:= ShallowCopy( m[i] );
               Add( m[i], 0 );
            fi;
        od;

        # We try to find indices in the `wrong' order.

        k:= 1; found:= false;
        while k < Length(m)-2 do

            if IsList( m[k] ) then
               k1:= m[k][1];
               list1:= true;
            else
               k1:= m[k];
               list1:= false;
            fi;
            if IsList( m[k+2] ) then
               k2:= m[k+2][1];
               list2:= true;
            else
               k2:= m[k+2];
               list2:= false;
            fi;

            if k1 > k2 then
                found:= true;
                break;
            elif k1 = k2 then

                if not list1 then
                
                   if m[k] <= s then
                       qp:= qpar^( rts[m[k]]*(B*rts[m[k]])/2 );
                       cf:= cf*GaussianBinomial( m[k+1]+m[k+3], m[k+1], qp );
                   fi;
                
                   if m[k] > s + rank then
                       qp:= qpar^( rts[m[k]-s-rank]*(B*rts[m[k]-s-rank])/2 );
                       cf:= cf*GaussianBinomial( m[k+1]+m[k+3], m[k+1], qp );
                   fi; 
                
                   m[k+1]:= m[k+1]+m[k+3];
                
                   if m[k+1] = 0*m[k+1] then
                       Unbind( m[k] ); Unbind( m[k+1] );
                       Unbind( m[k+2] ); Unbind( m[k+3] );
                       m:= Filtered( m, x -> IsBound(x) );
                       if k > 1 then
                        
                           # there is a new elt on pos k, we have to check
                           # whether it is in the correct order with 
                           # the previous element.
                           k:= k-2;
                       fi;
                   else
                       Unbind( m[k+2] ); Unbind( m[k+3] );
                       m:= Filtered( m, x -> IsBound(x) );
                   fi;
                else
                   # both are K-elements, coming from the same K_{\alpha}
                   # we do nothing (for the moment).
                   k:= k+2;
                fi;
            else
                k:= k+2;
            fi;
            
        od;

        if not found then

            # We add the monomial to `res'. However, we must still 
            # normalise the K-part...

            start:= [ ];
            k:= 1;
            while k < Length( m ) and not IsList( m[k] ) do
               Add( start, m[k] );
               Add( start, m[k+1] );
               k:= k+2;
            od;

            kbit:= [ ];
            while k < Length( m ) and IsList( m[k] ) do 
               Add( kbit, m[k] );
               Add( kbit, m[k+1] );
               k:= k+2;
            od; 

            tail:= [ ];
            while k < Length( m ) do
               Add( tail, m[k] );
               Add( tail, m[k+1] );
               k:= k+2;
            od;  

            k_normal:= [ [], qpar^0];
            ee:= [ ];
            k:= 1;
            while k < Length( kbit ) do

               rel:= binomial_with_cst( kbit[k][3], kbit[k+1] );
               if kbit[k][2] > 0 then 
                  rel:= QGPrivateFunctions.Multiply_K_Expr( rel );
               fi;
               if ee <> [ ] then
                  ee:= QGPrivateFunctions.Multiply_Exp_Exp( ee, rel );
               else
                  ee:= rel;
               fi;
               
               if k = Length(kbit)-1 or kbit[k][1] <> kbit[k+2][1] then
                  # add everything in `ee' to `k_normal',
                  # and start a new `ee':

                  qp:= qpar^( B[kbit[k][1]-s][kbit[k][1]-s]/2 );
                  store:= [ ];
                  for i in [1,3..Length(k_normal)-1] do
                      for j in [1,3..Length(ee)-1] do
                          mn:= ShallowCopy( k_normal[i] );
                          if ee[j] <> [ 0, 0 ] then
                             # Otherwise we multiply by one....
                             Add( mn, [ kbit[k][1], ee[j][1] ] );
                             Add( mn, ee[j][2] );
                          fi;
                          Add( store, mn );
                          Add( store, k_normal[i+1]*Value( ee[j+1], qp ) );
                      od;
                   od;
                   k_normal:= store;
                   ee:= [ ];
               fi;
               k:= k+2;
            od;   

            for k in [1,3..Length(k_normal)-1] do
                
                m:= ShallowCopy( start );
                Append( m, k_normal[k] );
                Append( m, tail );
                coef:= cf*k_normal[k+1];

                pos:= Position( res, m );
                if pos <> fail then
                   res[pos+1]:= res[pos+1]+coef;
                   if res[pos+1] = 0*coef then
                      Unbind( res[pos] ); Unbind( res[pos+1] );
                      res:= Filtered( res, x -> IsBound(x) );
                   fi;
                else    
                   Add( res, m );
                   Add( res, coef );
                fi;
            od; 
            
            Unbind( todo[1] );
            Unbind( todo[2] );
            todo:= Filtered( todo, x -> IsBound(x) );
        else
            
            # we know k1 > k2...
            
            if k1 > s+rank then
                
                # i.e., k1 is an E
                
                if k2 > s+rank then
                    
                    # i.e., k2 is also an E, commutation from Mtab
                    
                    if isgeneric then
                       r:= rts[k1-s-rank]*( B*rts[k2-s-rank]);                 
                       rel:= comm_rule( Mtab[k1][k2], m[k], m[k+2], 
                                    m[k+1], m[k+3], -r );
                    else
                       rel:= CollectQEAElement( ElementsFamily( 
                                    FamilyObj( fam!.genericQUEA ) ), 
                                    [ m{[k..k+3]}, _q^0 ] );
                       for i in [2,4..Length(rel)] do
                           rel[i]:= Value( rel[i], qpar );
                       od;
                    fi;

                    start:= m{[1..k-1]};
                    tail:= m{[k+4..Length(m)]};

                    for i in [1,3..Length(rel)-1] do
                        mn:= ShallowCopy( start );
                        Append( mn, rel[i] ); Append( mn, tail );
                        if i = 1 then
                            todo[1]:= mn;
                            todo[2]:= cf*rel[i+1];
                        else
                            Add( todo, mn ); Add( todo, cf*rel[i+1] );
                        fi;

                    od;
                    
                elif k2 > s then

                    # i.e., k2 is a K:
                    r:= -2*rts[k1-s-rank]*( B*sim[k2-s] )/B[k2-s][k2-s];
                    r:= r*m[k+1];
                    qp:= qpar^(B[k2-s][k2-s]/2);
                    coef:= qp^(r*m[k+2][2]);
                    mn:= m{[1..k-1]};
                    Add( mn, ShallowCopy(m[k+2]) );
                    mn[k][3]:= mn[k][3] + r; 
                    Add( mn, m[k+3] );
                    Add( mn, m[k] ); Add( mn, m[k+1] );
                    Append( mn,m{[k+4..Length(m)]} );
                    todo[1]:= mn;
                    todo[2]:= cf*coef;

                else
                    # k2 is an F, commutation from Mtab
                    
                    if isgeneric then
                       rel:= comm_rule( Mtab[k1][k2], m[k], m[k+2], 
                                     m[k+1], m[k+3], 0 );
                    else
                       rel:= CollectQEAElement( ElementsFamily( 
                                    FamilyObj( fam!.genericQUEA ) ), 
                                    [ m{[k..k+3]}, _q^0 ] );
                       for i in [2,4..Length(rel)] do
                           rel[i]:= Value( rel[i], qpar );
                       od;
                       # change the K-elements back to slightly strange form...
                       for j in [1,3..Length(rel)-1] do
                           for i in [1,3..Length(rel[j])-1] do
          
                    if IsList( rel[j][i] ) and Length( rel[j][i] ) = 2 then
                       Add( rel[j][i], 0 );
                    fi;
                            od;
                       od;
                    fi;
      
                    start:= m{[1..k-1]};
                    tail:= m{[k+4..Length(m)]};
                    
                    for i in [1,3..Length(rel)-1] do
                        mn:= ShallowCopy( start );
                        Append( mn, rel[i] ); Append( mn, tail );
                        if i = 1 then
                            todo[1]:= mn;
                            todo[2]:= cf;
                        else
                            Add( todo, mn ); Add( todo, cf*rel[i+1] );
                        fi;
                        
                    od;                        
                    
                fi;
            elif k1 > s then
                    
                # i.e., k1 is a K, 
                
                if k2 > s then
                    
                    # i.e., k2 is also a K; they commute
                    
                    mn:= m{[1..k-1]};
                    Add( mn, m[k+2] ); Add( mn, m[k+3] );
                    Add( mn, m[k] ); Add( mn, m[k+1] );
                    Append( mn,m{[k+4..Length(m)]} );
                    todo[1]:= mn;
                    todo[2]:= cf;
                else
                    
                    # i.e., k2 is an F:

                    r:= -2*rts[k2]*( B*sim[k1-s] )/B[k1-s][k1-s];
                    r:= r*m[k+3];
                    qp:= qpar^(B[k1-s][k1-s]/2);
                    coef:= qp^(r*m[k][2]);
                    mn:= m{[1..k-1]};
                    Add( mn, m[k+2] );
                    Add( mn, m[k+3] );
                    Add( mn, ShallowCopy(m[k]) );
                    mn[k+2][3]:= mn[k+2][3] + r; 
                    Add( mn, m[k+1] );
                    Append( mn,m{[k+4..Length(m)]} );
                    todo[1]:= mn;
                    todo[2]:= cf*coef;

                fi;
            else
                # i.e., k1, k2 are both F's. 
                # commutation from Mtab

                if isgeneric then

                   r:= rts[k1]*( B*rts[k2]);
                
                   rel:= comm_rule( Mtab[k1][k2], m[k], m[k+2], 
                                     m[k+1], m[k+3], -r );
                else
                   rel:= CollectQEAElement( ElementsFamily( 
                                 FamilyObj( fam!.genericQUEA ) ), 
                                    [ m{[k..k+3]}, _q^0 ] );
                   for i in [2,4..Length(rel)] do
                       rel[i]:= Value( rel[i], qpar );
                   od;
                fi;
                
                start:= m{[1..k-1]};
                tail:= m{[k+4..Length(m)]};
                        
                for i in [1,3..Length(rel)-1] do
                    mn:= ShallowCopy( start );
                    Append( mn, rel[i] ); Append( mn, tail );
                    if i = 1 then
                        todo[1]:= mn; todo[2]:= cf*rel[i+1];
                    else
                        Add( todo, mn ); Add( todo, cf*rel[i+1] );
                    fi;
                    
                od;
                
                
            fi;
            
        fi;
    od;

    return res;
end);


#############################################################################
##
#M  \*( <x>, <y> ) . . . . . . . . . . . . . . for two QEA elements
##
##
InstallMethod( \*,
        "for two QEA elements",
        IsIdenticalObj, [ IsQEAElement and IsPackedElementDefaultRep,
                IsQEAElement and IsPackedElementDefaultRep ], 0,
        function( x, y )
    
    local   ex,  ey,  expr,  i,  j,  m,  mons,  cfs,  len;    
   
    ex:= ExtRepOfObj(x);
    ey:= ExtRepOfObj(y);

    # We build the expression that needs to be collected.

    expr:= [ ];
    for i in [1,3..Length(ex)-1] do
        for j in [1,3..Length(ey)-1] do
            m:= ShallowCopy( ex[i] );
            Append( m, ey[j] );
            Add( expr, m );
            Add( expr, ex[i+1]*ey[j+1] );
        od;
    od;    
    
    # We collect it.
    
    expr:= CollectQEAElement( FamilyObj( x ), expr );
    
    mons:= [ ]; cfs:= [ ];
    for i in [1,3..Length(expr)-1] do
        if not IsZero( expr[i+1] ) then
           Add( mons, expr[i] ); Add( cfs, expr[i+1] );
        fi;
    od;

    # Sort everything, take equal things together, wrap it up and return.

    SortParallel( mons, cfs );

    expr:= [ ];
    len:= 0;
    for i in [1..Length( mons )] do
        if len > 0 and expr[len-1] = mons[i] then
            expr[len]:= expr[len]+cfs[i];
            if expr[len] = 0*expr[len] then
                Unbind( expr[len-1] ); Unbind( expr[len] );
                expr:= Filtered( expr, x -> IsBound(x) );
                len:= len-2;
            fi;

        else
            Add( expr, mons[i] ); Add( expr, cfs[i] );
            len:= len+2;
        fi;
    od;

    return ObjByExtRep( FamilyObj(x), expr );
end );

#########################################################################
##
#M  QuantizedUEA( <R> )
##
InstallMethod( QuantizedUEA,
        "for a root system",
        true, [ IsRootSystem ], 0,
        function( R )
    
    local   n,  rank,  B,  fam,  mm,  Ftab,  FEtab,  tt,  k,  rel,  i,  
            j,  qp,  ii,  gens,  A, normalise_rel;    

     # This function returns the quantized uea with respect to the root
     # system R. This algebra is generated by F1...Fn, K1, K1^-1,
     # ... Kr, Kr^-1, E1...En, where 
     #    Fk = T_{i_1}...T_{i_{k-1}}(F_{\alpha_{ik}})
     #    Ek = T_{i_1}...T_{i_{k-1}}(E_{\alpha_{ik}}),
     # where [ i_1,....,i_n ] is a redcued expression for the longest element
     # in the Weyl group. 

     # The elements are represented as elements of the Lusztig
     # Z-form of the quantized uea. The elements of this basis have the form
     #
     #   F1^(k1)...Fn^(kn) K1^d1 [K1;m1] ... Kr^dr [Kr;mr] E1^(p1)..En^(pn)
     #
     # where di=0,1 and [Ki;mi] is the "binomial"
     #
     #   / Ki; 0 \
     #   |       |
     #   \  mi   /
     #
     # Internally, such a monomial is represented as a list of indices
     # and exponents: the F-s have indices 1,..,n and the E-s have indices
     # n+r+1...2*n+r. Furthermore, an element Ki^di [Ki;mi] is represented as
     # .... , [ i, di ], mi .... So, for example the monomial 
     # F2^(3) K2 [ K2;4 ] E6^(8) (in type G2) is represented as 
     # [ 2, 3, [ 2, 1 ], 4, 14, 8 ].
     # Finally, a general element is represented as a list of monomials
     # and coefficients.

     normalise_rel:= function( s, rank, B, rel )

     # writes the relation rel using the generalised binomials in Lusztig's
     # Z-form of the quea.

     local add_elm, i, j, k, l, res, m, mon, e, f, ks, k_piece,
           new_piece, elm, ee, qp;

     add_elm:= function( ee, elm, cf )

          local pos;

          pos:= Position( ee, elm );
          if pos = fail then
             Add( ee, elm ); Add( ee, cf );
          else
             ee[pos+1]:= ee[pos+1]+ cf;
             if ee[pos+1]=0*ee[pos+1] then
                Unbind( ee[pos] ); Unbind( ee[pos+1] );
                ee:= Filtered( ee, x -> IsBound(x) );
             fi;
          fi;
          return ee;
     end;
      
     res:= [ ];
     for i in [1,3..Length(rel)-1] do
         m:= rel[i];
         k:= 1;
         f:= [ ];
         while k <= Length( m ) and m[k] <= s do 
            Add( f, m[k] );
            Add( f, m[k+1] );
            k:= k+2;
         od;
         ks:= [ ];
         while k <= Length( m ) and m[k] <= s+rank do 
            Add( ks, m[k] );
            Add( ks, m[k+1] );
            k:= k+2;
         od;
         e:= [ ];
         while k <= Length( m ) do
            Add( e, m[k] );
            Add( e, m[k+1] );
            k:= k+2;
         od;

         k_piece:= [ [], _q^0 ];
         for j in [1,3..Length(ks)-1] do
             if ks[j+1] > 0 then
                elm:= [ [1,0], _q^0 ];
                ee:= elm;
                for k in [2..ks[j+1]] do
                    ee:= QGPrivateFunctions.Multiply_Exp_Exp( ee, elm );
                od;
             else
                elm:= [ [1,0], _q^0, [0,1], _q^-1-_q ];
                ee:= elm;
                for k in [2..-ks[j+1]] do
                    ee:= QGPrivateFunctions.Multiply_Exp_Exp( ee, elm );
                od;
             fi;

             qp:= _q^( B[ks[j]-s][ks[j]-s]/2 );
             for k in [2,4..Length(ee)] do
                 ee[k]:= Value( ee[k], qp );
             od;
             new_piece:= [ ];
             for k in [1,3..Length(ee)-1] do
                 if ee[k] <> [ 0, 0 ] then 
                    m:= [ ks[j], ee[k][1] ];
                    for l in [1,3..Length(k_piece)-1] do 
                        mon:= ShallowCopy( k_piece[l] );
                        Add( mon, m );
                        Add( mon, ee[k][2] );
                        Add( new_piece, mon );
                        Add( new_piece, ee[k+1]*k_piece[l+1] );
                    od; 
                 else
                    # we multiply by a scalar, effectively
                    for l in [1,3..Length(k_piece)-1] do 
                        mon:= ShallowCopy( k_piece[l] );
                        Add( new_piece, mon );
                        Add( new_piece, ee[k+1]*k_piece[l+1] );
                    od; 
                 fi;
             od;
             k_piece:= new_piece;
         od;

         for j in [1,3..Length(k_piece)-1] do
             m:= ShallowCopy( f );
             Append( m, k_piece[j] );
             Append( m, e );
             res:= add_elm( res, m, k_piece[j+1]*rel[i+1] );
         od;

     od;
     return res;
    end;
    
    # First we produce the PBW generators of the quantized enveloping 
    # algebra corresponding to R. It mainly boils down to installing a 
    # lot of data in the family.

    n:= Length(PositiveRoots(R));
    rank:= Length( CartanMatrix(R) );
    B:= BilinearFormMatNF( R );
    
    fam:= NewFamily( "QEAEltFam", IsQEAElement );
    fam!.packedQEAElementDefaultType:=
                  NewType( fam, IsPackedElementDefaultRep );
    fam!.noPosRoots:= Length( PositiveRoots(R) );
    fam!.rank:= Length( CartanMatrix(R) );
    fam!.rootSystem:= R;
    
    mm:= QGPrivateFunctions.E_Tab( R );
    
    fam!.convexRoots:= mm[1]; # i.e., pos roots in convex order...
    
    Ftab:= QGPrivateFunctions.F_tab( R, mm[2], mm[1] );
    FEtab:= QGPrivateFunctions.FE_table( R, mm[2], Ftab, mm[1] );
    
    # `tt' will contain all commutation relations (Etab, Ftab, FEtab) 
    tt:= List([1..n], x -> [] );  
    for k in [1..n] do
        tt[k+rank+n]:= [];
    od;
    
    # We normalise the relations in the tables (by using 
    # E_a^{(k)} = E_a^n/[k]_a!
    
    for k in [1..Length(mm[2])] do
        rel:= List( mm[2][k][2], ShallowCopy );
        for i in [1,3..Length(rel)-1] do
            for j in [1,3..Length(rel[i])-1] do
                qp:= _q^( mm[1][ rel[i][j] ]*(B*mm[1][rel[i][j]])/2);
                rel[i][j]:= rel[i][j] + n + rank; 
                rel[i+1]:= rel[i+1]*
                           GaussianFactorial(rel[i][j+1],qp);
            od;
        od; 

        ii:= mm[2][k][1];
        tt[ii[1]+rank+n][ii[2]+rank+n]:= rel;
    od;
    
    for k in [1..Length(Ftab)] do
        rel:= List( Ftab[k][2], ShallowCopy );
        for i in [1,3..Length(rel)-1] do
            for j in [1,3..Length(rel[i])-1] do
                qp:= _q^( mm[1][ rel[i][j] ]*(B*mm[1][rel[i][j]])/2); 
                rel[i+1]:= rel[i+1]*
                           GaussianFactorial(rel[i][j+1],qp);
            od;
        od; 
        tt[Ftab[k][1][1]][Ftab[k][1][2]]:= rel;
    od;
    
    for k in [1..Length(FEtab)] do
        rel:= List( FEtab[k][2], ShallowCopy );
        for i in [1,3..Length(rel)-1] do
            for j in [1,3..Length(rel[i])-1] do
                if rel[i][j] <= n then
                    qp:= _q^( mm[1][ rel[i][j] ]*
                             (B*mm[1][rel[i][j]])/2); 
                    rel[i+1]:= rel[i+1]*
                               GaussianFactorial(rel[i][j+1],qp);
                fi;
                
                if rel[i][j] > n+rank then
                    qp:= _q^( mm[1][ rel[i][j]-n-rank ]*
                             (B*mm[1][rel[i][j]-n-rank])/2); 
                    rel[i+1]:= rel[i+1]*
                               GaussianFactorial(rel[i][j+1],qp);
                fi;                         
            od;
        od;                    
        tt[FEtab[k][1][1]][FEtab[k][1][2]]:= 
                    normalise_rel( n, rank, B, rel );
    od;              
        
    fam!.multTab:= tt;

    fam!.quantumPar:= _q;
    
    # Finally construct the generators.

    gens:= [ ];
    for i in [1..n] do
        gens[i]:= ObjByExtRep( fam, [ [ i, 1 ], _q^0 ] );
    od;
    for i in [1..Length( CartanMatrix(R) )] do
        Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], _q^0 ] ) );
        qp:= _q^(B[i][i]/2);
        
        # we need to sort the monomials in K^-1, to accomodate
        # for changes in the sorting algorithm, which may lead to
        # surprises otherwise...
        if [ [n+i,1], 0 ] < [ [ n+i, 0 ], 1 ] then
            Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], _q^0, 
                    [ [ n+i, 0 ], 1 ], qp^-1-qp ] ) );
        else
            Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 0 ], 1 ], qp^-1-qp, 
                    [ [ n+i, 1 ], 0 ], _q^0 ] ) );
        fi;
        
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
end);

#########################################################################
##
#M  QuantizedUEA( <R> )
##
InstallOtherMethod( QuantizedUEA,
        "for a root system a ring, and a parameter",
        true, [ IsRootSystem, IsField, IsObject ], 0,
        function( R, F, v )
    
    local   n,  rank,  B,  fam,  tt,  tt_new,  k,  rel,  i,  
            j,  qp,  gens,  A,  uu;    


    n:= Length(PositiveRoots(R));
    rank:= Length( CartanMatrix(R) );
    B:= BilinearFormMatNF( R );
    
    fam:= NewFamily( "QEAEltFam", IsQEAElement );
    fam!.packedQEAElementDefaultType:=
                  NewType( fam, IsPackedElementDefaultRep );
    fam!.noPosRoots:= Length( PositiveRoots(R) );
    fam!.rank:= Length( CartanMatrix(R) );
    fam!.rootSystem:= R;
    
    uu:= QuantizedUEA( R );

    fam!.genericQUEA:= uu;

    tt:= ElementsFamily( FamilyObj( uu ) )!.multTab;
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
    fam!.convexRoots:= ElementsFamily( FamilyObj( uu ) )!.convexRoots;
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
           # we need to sort the monomials in K^-1, to accomodate
            # for changes in the sorting algorithm, which may lead to
            # surprises otherwise...
           if [ [n+i,1], 0 ] < [ [ n+i, 0 ], 1 ] then
               Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 1 ], 0 ], qp^0, 
                       [ [ n+i, 0 ], 1 ], qp^-1-qp ] ) );
           else
               Add( gens,  ObjByExtRep( fam, [ [ [ n+i, 0 ], 1 ], qp^-1-qp, 
                       [ [ n+i, 1 ], 0 ], qp^0 ] ) );
           fi;
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
end);

#########################################################################
##
#M  QuantizedUEA( <L> )
##
InstallOtherMethod( QuantizedUEA,
        "for a semisimple Lie algebra",
        true, [ IsLieAlgebra ], 0,
        function( L )
    return QuantizedUEA( RootSystem(L) );
end );

#########################################################################
##
#M  QuantizedUEA( <L> )
##
InstallOtherMethod( QuantizedUEA,
        "for a semisimple Lie algebra, a ring and a parameter",
        true, [ IsLieAlgebra, IsField, IsObject ], 0,
        function( L, F, qp )
    return QuantizedUEA( RootSystem(L), F, qp );
end );

############################################################################
##
#M  PrintObj( <QA> )
#M  ViewObj( <QA> )
##
InstallMethod( PrintObj,
        "for a QuantumUEA",
        true, [ IsQuantumUEA ], 0,
        
        function( A )
    
    Print("QuantumUEA( ",RootSystem(A),", Qpar = ",QuantumParameter(A)," )" );
end );

InstallMethod( ViewObj,
        "for a QuantumUEA",
        true, [ IsQuantumUEA ], 0,
        
        function( A )
    
    PrintObj( A );
end );

#############################################################################
##
#M  LeadingUEALatticeMonomial( <novar>, <f> )
##
##
InstallMethod( LeadingQEAMonomial,
        "for an integer and a QEA element",
        true, [ IS_INT, IsQEAElement ], 0,

        function ( novar, p )

    local e,max,cf,m,n,j,k,o,pos,deg,ind, degn;

    # Reverse lexicographical ordering...

    e:= p![1];
    max:= e[1];
    ind:= 1;
    cf:= e[2];
    m:= ListWithIdenticalEntries( novar, 0 );
    for k in [1,3..Length(max)-1] do
        m[max[k]]:= max[k+1];
    od;

    for k in [3,5..Length(e)-1] do

        n:= ListWithIdenticalEntries( novar, 0 );
        for j in [1,3..Length(e[k])-1] do
            n[e[k][j]]:= e[k][j+1];
        od;

        o:= n-m;
        
        # pos will be the last nonzero position
        pos:= PositionProperty( Reversed(o), x -> x <> 0 );
        pos:= novar-pos+1;
        if o[pos] > 0 then
            max:= e[k];
            ind := k;
            cf:= e[k+1];
            m:= n;
        fi;
    od;

    return [max, m, cf, ind];
end );


#############################################################################
##
#F  LeftReduceQEEALatticeElement( <novar>, <G>, <lms>, <lmtab>, <p> )
##
##
##
InstallGlobalFunction( LeftReduceQEAElement,
        function( novar, G, lms, lmtab, p )

    local   fam,  reduced,  rem,  res,  m1,  k,  g,  diff,  cme,  mon,  
            cflmg,  j,  fac,  fac1,  cf,  lm;

    # We left-reduce the QUEA element `p' modulo the elements in `G'.
    # Here `lms' is a list of leading monomial-indices; if the index `k'
    # occurs somewhere in `lms', then g![1][k] is the leading monomial
    # of `g', where `g' is the corresponding element of `G'. `novar'
    # is the number of variables.

    fam:= FamilyObj( p );
    reduced:= false;
    rem:= p;
    res:= 0*p;

    while rem <> 0*rem do

        m1:= LeadingQEAMonomial( novar, rem );
        k:= 1;
            
        k:= Search( lmtab, m1[2] );
        if k <> fail then
            
            g:= G[k];
            diff:= ShallowCopy( m1[2] );
            cme:= g![1];
            mon:= cme[ lms[k] ];
            cflmg:= cme[ lms[k]+1 ];
            for j in [1,3..Length(mon)-1] do
                diff[mon[j]]:= diff[mon[j]] - mon[j+1];
            od;

            fac:= [ ];
            for j in [1..novar] do
                if diff[j] <> 0 then
                    Add( fac, j ); Add( fac, diff[j] );
                fi;
            od;
            fac1:= ObjByExtRep( fam, [ fac, _q^0 ] )*g;
            cf:= LeadingQEAMonomial( novar, fac1 )[3];
            rem:= rem - (m1[3]/cf)*fac1;
            
        else
            lm:= ObjByExtRep( fam, [ m1[1], m1[3] ] );
            res:= res + lm;
            rem:= rem-lm; 
        fi;
        
            
    od;

    return res;

end );


QGPrivateFunctions.ActionCollect:=
        function( sim, rts, B, s, rank, Mtab, qpar, expr )

    # `sim' are the simple roots.
    # `rts' are the roots in convex order.
    # `B' is the matrix of the bilinear form.
    # `s' is the number of positive roots.
    # `rank' is the rank of the root system.
    # `Mtab' is the multiplication table.
    # `qpar' is the quantum parameter.
    # `expr' is the thing that needs to be collected.

    # Does the same as normal collection, except that monomials
    # ending on an E are immediately discarded, and K-elements are
    # not normalised...
    
    local   comm_rule,  todo,  res,  m,  cf,  k,  found,  pos,  k1,  
            k2,  r,  rel,  start,  tail,  i,  mn,  m1,  j, qp, coef, 
            list1, list2;

    comm_rule:= function( rel, j, i, m, n, r )
        
        # commutation rule for x_j^mx_i^n, where x_jx_i=qpar^rx_ix_j+rel
        
        local   rule,  l,  k,  cf,  u,  mn, start, tail, qi, qj, den, t;
        
        if j > s + rank then
            qj:= qpar^( rts[j-s-rank]*( B*rts[j-s-rank] )/2 );
        else
            qj:= qpar^( rts[j]*( B*rts[j] )/2 );
        fi;
        if i > s +rank then
            qi:= qpar^( rts[i-s-rank]*( B*rts[i-s-rank] )/2 );
        else
            qi:= qpar^( rts[i]*( B*rts[i] )/2 );
        fi;
        
        den:= GaussianFactorial( m, qj )*GaussianFactorial( n, qi );

        rule:= [ [ i, n, j, m], qpar^(n*m*r) ];
        for l in [0..n-1] do
            for k in [0..m-1] do
                cf:= qpar^((l*m+k)*r)/den;
                start:= [ ];
                if l <> 0 then
                    Add( start, i ); Add( start, l );
                    cf:= cf*GaussianFactorial( l, qi );
                fi;
                if m-1-k <> 0 then
                    Add( start, j ); Add( start, m-1-k );
                    cf:= cf*GaussianFactorial( m-1-k, qj );
                fi;
                tail:= [];
                if k <> 0 then
                    Add( tail, j ); Add( tail, k );
                    cf:= cf*GaussianFactorial( k, qj );
                fi;
                if n-1-l <> 0 then
                    Add( tail, i ); Add( tail, n-1-l );
                    cf:= cf*GaussianFactorial( n-1-l, qi );
                fi;

                for u in [1,3..Length(rel)-1] do
                    mn:= ShallowCopy( start );
                    Append( mn, rel[u] );
                    Append( mn, tail );
                    Add( rule, mn ); Add( rule, cf*rel[u+1] );
                od;
            od;
        od;

        return rule;
    end;
    
    # In the program we use ... [ i, d, a ], s ... for
    #
    #       / Ki; a \
    #  Ki^d |       |
    #       \   s   /
    #

    todo:= expr;

    for k in [1,3..Length(todo)-1] do
        for i in [1,3..Length(todo[k])-1] do
            if IsList( todo[k][i] ) and Length( todo[k][i] ) = 2 then
               todo[k][i]:= ShallowCopy( todo[k][i] );
               Add( todo[k][i], 0 );
            fi;
        od;
    od;

    res:= [ ];
    while todo <> [] do

        found:= false;
        while todo <> [] and not found do
           m:= todo[1];
           cf:= todo[2];
           if m = [ ] then
              found:= true;
              break;
           fi;
           k:= m[Length(m)-1];
           if IsList( k ) or k <= s then
              # m ends with K or F:
              found:= true;
           else
              Unbind( todo[1] ); Unbind( todo[2] );
              todo:= Filtered( todo, x -> IsBound(x) );
           fi;
        od;
        if todo = [ ] then break; fi;

        for i in [1,3..Length(m)-1] do
            if IsList( m[i] ) and Length( m[i] ) = 2 then
               m[i]:= ShallowCopy( m[i] );
               Add( m[i], 0 );
            fi;
        od;

        # We try to find indices in the `wrong' order.

        k:= 1; found:= false;
        while k < Length(m)-2 do

            if IsList( m[k] ) then
               k1:= m[k][1];
               list1:= true;
            else
               k1:= m[k];
               list1:= false;
            fi;
            if IsList( m[k+2] ) then
               k2:= m[k+2][1];
               list2:= true;
            else
               k2:= m[k+2];
               list2:= false;
            fi;

            if k1 > k2 then
                found:= true;
                break;
            elif k1 = k2 then

                if not list1 then
                
                   if m[k] <= s then
                       qp:= qpar^( rts[m[k]]*(B*rts[m[k]])/2 );
                       cf:= cf*GaussianBinomial( m[k+1]+m[k+3], m[k+1], qp );
                   fi;
                
                   if m[k] > s + rank then
                       qp:= qpar^( rts[m[k]-s-rank]*(B*rts[m[k]-s-rank])/2 );
                       cf:= cf*GaussianBinomial( m[k+1]+m[k+3], m[k+1], qp );
                   fi; 
                
                   m[k+1]:= m[k+1]+m[k+3];
                
                   if m[k+1] = 0*m[k+1] then
                       Unbind( m[k] ); Unbind( m[k+1] );
                       Unbind( m[k+2] ); Unbind( m[k+3] );
                       m:= Filtered( m, x -> IsBound(x) );
                       if k > 1 then
                        
                           # there is a new elt on pos k, we have to check
                           # whether it is in the correct order with 
                           # the previous element.
                           k:= k-2;
                       fi;
                   else
                       Unbind( m[k+2] ); Unbind( m[k+3] );
                       m:= Filtered( m, x -> IsBound(x) );
                   fi;
                else
                   # both are K-elements, coming from the same K_{\alpha}
                   # we do nothing (for the moment).
                   k:= k+2;
                fi;
            else
                k:= k+2;
            fi;
            
        od;

        if not found then

            # We add the monomial to `res'. 

            pos:= Position( res, m );
            if pos <> fail then
               res[pos+1]:= res[pos+1]+cf;
               if res[pos+1] = 0*cf then
                  Unbind( res[pos] ); Unbind( res[pos+1] );
                  res:= Filtered( res, x -> IsBound(x) );
               fi;
            else    
               Add( res, m );
               Add( res, cf );
            fi;

            Unbind( todo[1] );
            Unbind( todo[2] );
            todo:= Filtered( todo, x -> IsBound(x) );
        else
            
            # we know k1 > k2...
            
            if k1 > s+rank then
                
                # i.e., k1 is an E
                
                if k2 > s+rank then
                    
                    # i.e., k2 is also an E, commutation from Mtab
                    
                    r:= rts[k1-s-rank]*( B*rts[k2-s-rank]);
                    
                    rel:= comm_rule( Mtab[k1][k2], m[k], m[k+2], 
                                  m[k+1], m[k+3], -r );
                    start:= m{[1..k-1]};
                    tail:= m{[k+4..Length(m)]};

                    for i in [1,3..Length(rel)-1] do
                        mn:= ShallowCopy( start );
                        Append( mn, rel[i] ); Append( mn, tail );
                        if i = 1 then
                            todo[1]:= mn;
                            todo[2]:= cf*rel[i+1];
                        else
                            Add( todo, mn ); Add( todo, cf*rel[i+1] );
                        fi;

                    od;
                    
                elif k2 > s then

                    # i.e., k2 is a K:
                    r:= -2*rts[k1-s-rank]*( B*sim[k2-s] )/B[k2-s][k2-s];
                    r:= r*m[k+1];
                    qp:= qpar^(B[k2-s][k2-s]/2);
                    coef:= qp^(r*m[k+2][2]);
                    mn:= m{[1..k-1]};
                    Add( mn, ShallowCopy(m[k+2]) );
                    mn[k][3]:= mn[k][3] + r; 
                    Add( mn, m[k+3] );
                    Add( mn, m[k] ); Add( mn, m[k+1] );
                    Append( mn,m{[k+4..Length(m)]} );
                    todo[1]:= mn;
                    todo[2]:= cf*coef;

                else
                    # k2 is an F, commutation from Mtab
                    
                    rel:= comm_rule( Mtab[k1][k2], m[k], m[k+2], 
                                  m[k+1], m[k+3], 0 );
                    start:= m{[1..k-1]};
                    tail:= m{[k+4..Length(m)]};
                    
                    for i in [1,3..Length(rel)-1] do
                        mn:= ShallowCopy( start );
                        Append( mn, rel[i] ); Append( mn, tail );
                        if i = 1 then
                            todo[1]:= mn;
                            todo[2]:= cf;
                        else
                            Add( todo, mn ); Add( todo, cf*rel[i+1] );
                        fi;
                        
                    od;                        
                    
                fi;
            elif k1 > s then
                    
                # i.e., k1 is a K, 
                
                if k2 > s then
                    
                    # i.e., k2 is also a K; they commute
                    
                    mn:= m{[1..k-1]};
                    Add( mn, m[k+2] ); Add( mn, m[k+3] );
                    Add( mn, m[k] ); Add( mn, m[k+1] );
                    Append( mn,m{[k+4..Length(m)]} );
                    todo[1]:= mn;
                    todo[2]:= cf;
                else
                    
                    # i.e., k2 is an F:

                    r:= -2*rts[k2]*( B*sim[k1-s] )/B[k1-s][k1-s];
                    r:= r*m[k+3];
                    qp:= qpar^(B[k1-s][k1-s]/2);
                    coef:= qp^(r*m[k][2]);
                    mn:= m{[1..k-1]};
                    Add( mn, m[k+2] );
                    Add( mn, m[k+3] );
                    Add( mn, ShallowCopy(m[k]) );
                    mn[k+2][3]:= mn[k+2][3] + r; 
                    Add( mn, m[k+1] );
                    Append( mn,m{[k+4..Length(m)]} );
                    todo[1]:= mn;
                    todo[2]:= cf*coef;

                fi;
            else
                # i.e., k1, k2 are both F's. 
                # commutation from Mtab
                
                r:= rts[k1]*( B*rts[k2]);
                
                rel:= comm_rule( Mtab[k1][k2], m[k], m[k+2], 
                                  m[k+1], m[k+3], -r );
                start:= m{[1..k-1]};
                tail:= m{[k+4..Length(m)]};
                        
                for i in [1,3..Length(rel)-1] do
                    mn:= ShallowCopy( start );
                    Append( mn, rel[i] ); Append( mn, tail );
                    if i = 1 then
                        todo[1]:= mn; todo[2]:= cf*rel[i+1];
                    else
                        Add( todo, mn ); Add( todo, cf*rel[i+1] );
                    fi;
                    
                od;
                
                
            fi;
            
        fi;
    od;

    return res;
end;


QGPrivateFunctions.Calc_Image:=  function( qpar, x, v )

        # a function for calculating the image of v under x. This is used
        # at the end for calculating a list of images of the generators,
        # if the dimension of the module is not too big. 
        # If the dimension is higher,
        # then this function is also called from the method for \^.

         local   rank,  s,  hw,  ev,  qelm,  ee,  eres,  k,  i,  cf,  pos,  
                 gb,  p,  wvecs,  mons,  cfts,  ep,  im, B, ind, qp,
                 ex, fam, R, m, j;
    
         if IsZero( v ) then return v; fi;
         rank:= FamilyObj( x )!.rank;
         s:= FamilyObj( x )!.noPosRoots;
         hw:= FamilyObj( v )!.highestWeight;
    
         B:= BilinearFormMatNF( FamilyObj( x )!.rootSystem );
    
         # qelm will be x*v1, where v1 is the corresponding element in U^-
         # (corresponding to v). We reduce this element modulo the Groebner
         # basis.
         ev:= ExtRepOfObj( v );    
         qelm:= Sum( [1,3..Length(ev)-1], ii -> ev[ii+1]*ev[ii][2] );
         qelm:= ExtRepOfObj( qelm );
         ex:= ExtRepOfObj( x );

         # We build the expression that needs to be collected.

         ee:= [ ];
         for i in [1,3..Length(ex)-1] do
            for j in [1,3..Length(qelm)-1] do
               m:= ShallowCopy( ex[i] );
               Append( m, qelm[j] );
               Add( ee, m );
               Add( ee, ex[i+1]*qelm[j+1] );
           od;
         od;    

         fam:= FamilyObj(x);
         R:= fam!.rootSystem;

         # We collect it.

         ee:= QGPrivateFunctions.ActionCollect(SimpleSystemNF(R), 
                   fam!.convexRoots, 
                   BilinearFormMatNF(R), fam!.noPosRoots, fam!.rank, 
                   fam!.multTab, fam!.quantumPar, ee );

         eres:= [ ];
         for k in [1,3..Length(ee)-1] do
        
            if ee[k] = [] then
            
               # i.e., the monomial is 1, can go straight to eres
               pos:= Position( eres, ee[k] );
               if pos = fail then
                  Add( eres, ee[k] ); Add( eres, ee[k+1] );
               else
                  eres[pos+1]:= eres[pos+1]+ee[k+1];
                  if eres[pos+1] = 0*eres[pos+1] then
                      Unbind( eres[pos] ); Unbind( eres[pos+1] );
                      eres:= Filtered( eres, x -> IsBound( x ) );
                  fi;
               fi;
        
            elif IsList( ee[k][Length(ee[k])-1] ) or 
                                 ee[k][Length(ee[k])-1] <= s  then
            
               # if not, then the monomial ends with an E;
               # we can discard those...
            
               # we eat off the K's, and multiply with the corr scalar
            
               ee[k]:= ShallowCopy( ee[k] );
               i:= Length(ee[k])-1;
               cf:= ee[k+1];
               while i>=1 and IsList( ee[k][i] ) do
                
                   ind:= ee[k][i][1]-s;
                   qp:= qpar^( B[ind][ind]/2 );
                   cf:= cf*GaussianBinomial( hw[ind]+ee[k][i][3], 
                                                       ee[k][i+1], qp );
                   if ee[k][i][2] > 0 then
                      cf:= cf*qp^hw[ind];
                   fi;
                   Unbind( ee[k][i+1] ); Unbind( ee[k][i] );
                   i:= i-2;
               od;
               if cf <> 0*cf then
                  pos:= Position( eres, ee[k] );
                  if pos = fail then
                     Add( eres, ee[k] ); Add( eres, cf );
                  else
                     eres[pos+1]:= eres[pos+1]+cf;
                     if eres[pos+1] = 0*eres[pos+1] then
                         Unbind( eres[pos] ); Unbind( eres[pos+1] );
                         eres:= Filtered( eres, x -> IsBound( x ) );
                     fi;
                  fi;
               fi;   
            fi;
         od;

         gb:= FamilyObj(v)!.grobnerBasis;
         p:= ObjByExtRep( FamilyObj( x ), eres );

         p:= LeftReduceQEAElement( s, gb[1], gb[2], gb[3], p );    
    
         wvecs:= FamilyObj( v )!.weightVectors;
         mons:= [ ];
         cfts:= [ ];
         ep:= p![1];

         for k in [1,3..Length(ep)-1] do
            pos:= PositionProperty( wvecs, y -> y![1][1][2]![1][1] = ep[k] );
            Add( mons, ShallowCopy( wvecs[pos]![1][1] ) );
            Add( cfts, ep[k+1] );
         od;

         SortParallel( mons, cfts, function( a, b ) return a[1] < b[1]; end );
         im:= [ ];
         for k in [1..Length(mons)] do
            Add( im, mons[k] );
            Add( im, cfts[k] );
         od;
         return ObjByExtRep( FamilyObj( v ), im );

end;


#############################################################################
##
#F     GenericWeightVecAction( <q>, <x>, <v> )
##
##  The action of a qea element on a weight rep element. 
##  
##
##
QGPrivateFunctions.GenericWeightVecAction:= function( qpar, x, u )

    local   imgs,  v,  vecs2,  cfs2,  i,  ex,  vvv,  ccc,  m,  vecs,  
            cfs,  im,  j,  v1,  cfs1,  k,  ii,  cc,  l,  pos,  vv,  
            exrep, B, rt, qp, delta, mu;

    if not IsBound( FamilyObj( u )!.images ) then
       return QGPrivateFunctions.Calc_Image( qpar, x, u );
    fi;

    # Otherwise we use the faster method for calculating images. 
    # The way in which the images are stored is described in the comments
    # at the end of `HighestWeightModule'.

    B:= BilinearFormMatNF( FamilyObj( x )!.rootSystem );
    imgs:= FamilyObj( u )!.images;
    v:= u![1];
    vecs2:= [ ]; cfs2:= [ ]; 
    for i in [1,3..Length(v)-1] do
        Add( vecs2, v[i][1] ); Add( cfs2, v[i+1] );
    od;
    
    ex:= x![1];
    vv:= FamilyObj( u )!.baselms;    
    vvv:= [ ]; ccc:= [ ];
    
    for m in [1,3..Length(ex)-1] do

        # We calculate the image of `vecs2' undex `ex[m]'. At the end all
        # images are combined in the lists `vvv' and `ccc'.

        vecs:= ShallowCopy( vecs2 ); cfs:= ShallowCopy( cfs2 );
        for i in [Length(ex[m])-1,Length(ex[m])-3..1] do

            if IsList( ex[m][i] ) then 

               # it is a K, and hence we have to multiply every coefficient
               # by a certain scalar. 
     
               j := ex[m][i][1] - FamilyObj( x )!.noPosRoots;
               qp:= qpar^( B[j][j]/2 );
               delta:= ex[m][i][2];
               for k in [1..Length(vecs)] do
                  mu:= vv[vecs[k]][3];

                  cfs[k]:= cfs[k]*qp^( mu[j]*delta )*GaussianBinomial( mu[j],
                              ex[m][i+1], qp );

               od;

            else

               # It is an F or an E, we get the image from the list.
        
               im:= imgs[ex[m][i]];
            
               for j in [1..ex[m][i+1]] do

                   v1:= [ ]; cfs1:=[];
                   for k in [1..Length(vecs)] do

                       # `ii' will contain the indices of the basis vectors
                       # contained in the image, `cc' contains their 
                       # coefficients.
                       # We insert this in the sorted list `v1'.
 
                       ii:= im[vecs[k]][1];
                       cc:= cfs[k]*im[vecs[k]][2];
                       for l in [1..Length(ii)] do
                           pos:= PositionSorted( v1, ii[l] );
                           if pos>Length(v1) or v1[pos] <> ii[l] then
                               InsertElmList( v1, pos, ii[l] );
                               InsertElmList( cfs1, pos, cc[l] );
                           else
                               cfs1[pos]:= cfs1[pos]+cc[l];
                               if IsZero( cfs1[pos] ) then
                                   Unbind( cfs1[pos] ); Unbind( v1[pos] );
                                   cfs1:= Filtered( cfs1, x -> IsBound(x) );
                                   v1:= Filtered( v1, x -> IsBound(x) );
                               fi;
                           fi;
                       od;
                   od;
                   vecs:= v1; cfs:= cfs1;
               od;
               
               if ex[m][i+1] > 1 then

                  # Need to compensate for the fact that we are using divided 
                  # powers...

                  if ex[m][i] <= FamilyObj( x )!.noPosRoots then
                     k:= ex[m][i]; 
                  else
                     k:= ex[m][i] - FamilyObj( x )!.noPosRoots -
                          FamilyObj( x )!.rank;
                  fi;
                  rt:= FamilyObj( x )!.convexRoots[k];
                  qp:= qpar^( rt*(B*rt)/2 );
                  cfs:= (1/GaussianFactorial( ex[m][i+1], qp ) )*cfs;
               fi;
            fi;
        od;

        cfs:= cfs*ex[m+1];

        # Now we add everything to `ccc' and `vvv'.
        for l in [1..Length(vecs)] do
            if cfs[l] <> 0*cfs[l] then
               pos:= PositionSorted( vvv, vecs[l] );
               if pos > Length(vvv) or vvv[pos] <> vecs[l] then
                  InsertElmList( vvv, pos, vecs[l] );
                  InsertElmList( ccc, pos, cfs[l] );
               else
                  ccc[pos]:= ccc[pos]+cfs[l];
                  if IsZero( ccc[pos] ) then
                     Unbind( ccc[pos] ); Unbind( vvv[pos] );
                     ccc:= Filtered( ccc, x -> IsBound(x) );
                     vvv:= Filtered( vvv, x -> IsBound(x) );
                  fi;
               fi;
            fi;
        od;
        
    od;
    
    # We produce the resulting vector.
    exrep:= [];
    for i in [1..Length(vvv)] do
        Add( exrep, vv[vvv[i]] ); Add( exrep, ccc[i] );
    od;
    return ObjByExtRep( FamilyObj( u ), exrep );
end;



############################################################################
##
#M   HighestWeightModule( <QA>, <hw> )
##
##
##
InstallMethod( HighestWeightModule,
     "for a quantized enveloping algebra and a list of nonnegative integers",
     true, [ IsGenericQUEA, IsList ], 0,   
#+
#+   Let <A> be a quantized enveloping algebra, and <wt> a dominant weight
#+   in the weight lattice of the root system of <A>. This function returns
#+   the highest-weight module with highest weight <wt> over <A>.
#+
#+   The function calculates
#+   the sparse matrices of the actions of the (PBW) generators of the 
#+   quantized enveloping algebra. This will significantly speed up 
#+   further calculations of the image of a vector under the action of 
#+   an element of <A>. 
        
  function( A, hw )

    local   lexord,  R,  ggg,  famU,  n,  posR,  V,  lcombs,  fundB,  
            novar,  rank,  char,  orbs,  k,  it,  orb,  www,  levels,  
            weights,  wd,  levwd,  i,  w,  j,  w1,  lev,  lents,  
            maxlev,  cfs,  G,  Glms,  paths,  GB,  lms,  lmtab,  
            curlev,  ccc,  mons,  pos,  m,  em,  z,  pos1,  Glmsk,  
            Gk,  isdone,  mmm,  lm,  longmon,  l,  multiplicity,  sps,  
            sortmn,  we_had_enough,  le,  f,  m1a,  prelcm,  g,  m2a,  
            lcm,  pp,  w2,  e1,  e2,  fac1,  fac2,  comp,  vec,  
            ecomp,  vecs,  cfsc,  ec,  wvecs,  no,  fam,  B,  delmod,  
            delB,  act,  ims,  im,  e;
    
    lexord:= function( novar, m1, m2 )
    
        # m1, m2 are two monomials in extrep, rev lex order...
    
        local   d1,  d2,  n1,  k,  n2,  o,  pos;
        
        n1:= ListWithIdenticalEntries( novar, 0 );
        for k in [1,3..Length(m1)-1] do
            n1[m1[k]]:= m1[k+1];
        od;
        n2:= ListWithIdenticalEntries( novar, 0 );
        for k in [1,3..Length(m2)-1] do
            n2[m2[k]]:= m2[k+1];
        od;
        
        o:= n2-n1;
        pos:= PositionProperty( Reversed(o), x -> x <> 0 );
        pos:= novar-pos+1;
        return o[pos] > 0;
    end;


    if PositionProperty( hw, x -> x<0 ) <> fail then
        Error( "the weight <hw> must be dominant" );
    fi;

    R:= RootSystem( A );
    ggg:=  GeneratorsOfAlgebra( A );
    famU:= FamilyObj( ggg[1] );

    n:= Length(PositiveRoots( R ));
    posR:= FamilyObj( ggg[1] )!.convexRoots;
    V:= VectorSpace( Rationals, SimpleSystemNF( R ) );
    lcombs:= List( posR, r -> Coefficients( Basis( V, SimpleSystemNF(R)),r));
    posR:= List( lcombs, c -> LinearCombination( CartanMatrix(R), c ) );

    fundB:= Basis( VectorSpace( Rationals, CartanMatrix( R ) ),
                 CartanMatrix( R ) );
    
    
    novar:= n;
    rank:= Length( CartanMatrix(R) );

    # `orbs' will be a list of lists of the form [ mult, wts ], where
    # `wts' is a list of weights, and `mult' is their multiplicity.
    # Every element is an orbit under the Weyl group of a dominant weight.

    char:= DominantCharacter( R, hw );
    orbs:= [ ];

    for k in [1..Length( char[1] )] do
        it:= WeylOrbitIterator( WeylGroup( R ), char[1][k] );
        orb:= [ ];
        while not IsDoneIterator( it ) do
            Add( orb, NextIterator( it ) );
        od;
        Add( orbs, [ char[2][k], orb ] );
    od;


    # `levels' will be a list of lists, and `levels[k]' is the list of
    # weights of level `k-1'.
    # `weights' will be the list of all weights, sorted according to level.
    # `wd' will be the list of the weights of the extended weight diagram,
    # also sorted according to level.
    # `levwd' will be the list of the levels of the elements of `wd'.

    www:= [ ];
    for k in orbs do Append( www, k[2] ); od;
    levels:= [ [ hw ] ];
    weights:= [ ];
    k:=1;
    wd:= [ hw ];
    levwd:= [ 0 ];

    while k <= Length( levels ) do
        for i in [1..Length(levels[k])] do
            w:= levels[k][i];
            for j in [1..Length(posR)] do
                w1:= w - posR[j];
                lev:= k + Sum(lcombs[j]);
                if w1 in www then
                    if IsBound( levels[lev] ) then
                        if not w1 in levels[lev] then
                            Add( levels[lev], w1 );
                        fi;

                    else
                        levels[lev]:= [ w1 ];
                    fi;
                fi;
                if not w1 in wd then
                    Add( wd, w1 );
                    Add( levwd, lev );
                fi;

            od;
        od;
        k:= k+1;
    od;
    SortParallel( levwd, wd );
    for k in levels do
        Append( weights, k );
    od;

    # `lents' is a list of the lengths of the elements of `levels'; this is
    # used to calculate the position of an element of the list `weights'
    # efficiently.

    lents:= List(levels, Length );
    maxlev:= Length(levels);

    # `cfs' will be a list of coefficient-lists. The k-th element of `cfs'
    # are the coefficients $k_i$ in the expression `wd[k] = hw - \sum_i k_i
    # \alpha_i', where the \alpha_i are the fundamental roots.

    cfs:= List( wd, x -> Coefficients( fundB, hw - x ) );

    # `G' will be the Groebner basis, where the elements are grouped
    # in lists; for every weight of the extended diagram `wd' there is
    # a list. `Glms' is the list of leading monomials of the elements of `G'.
    # The leading monomials in this list are represented by indices j such that
    # f![1][j] is the leading monomial of f.
    # `paths' is the list of normal monomials of each weight in `weights'.
    # `GB' is the Groebner basis, now as a flat list, `lms' are the
    # corresponding leading monomials.
    # `lmtab' will be the search table of leading monomials of `G'. 
    # 

    G:= [ [ ] ];
    Glms:= [ [ ] ];

    paths:= [ [ ggg[1]^0 ] ];
    GB:= [ ];
    lms:= [ ];
    lmtab:= VectorSearchTable( );

    k:= 2;
    while k <= Length(wd) do

        # We take all weights of level equal to the level of `wd[k]'
        # together, and construct the corresponding parts of the Groebner
        # basis simultaneously.

        w:= [ ]; curlev:= levwd[k];
        ccc:= [ ];
        while k <= Length(wd) and levwd[k] = curlev do
            Add( w, wd[k] );
            Add( ccc, cfs[k] );
            k:= k+1;
        od;

        # `mons' will be a list of sets of monomials of the QUEA.
        # They are candidates for the normal monomials of the weights in `w'.

        mons:= [ ];
        for j in [1..Length(w)] do
            mons[j]:= [ ];
            for i in [1..Length(posR)] do
                
                # We construct all weights of lower levels (that already have
                # been taken care of), connected to the weight `w'.

                w1:= w[j] + posR[i];
                lev:= curlev-Sum(lcombs[i]);

                if lev>0 and lev <= maxlev then
                    pos:= Position( levels[lev], w1 );
                else
                    pos:= fail;
                fi;

                if pos <> fail then # `w1' is a weight of the representation.

                    # `pos' will be the position of `w1' in the list `weights'.

                    pos:= pos + Sum( lents{[1..lev-1]} );
                    for m in paths[pos] do

                        # fit F_i in m (commutatively)
                        em:= ShallowCopy(m![1][1]);

                        z:= em{[1,3..Length(em)-1]};

                      # We search for the position in `z' where to insert y_i.

                        pos1:= PositionSorted( z, i );
                        if pos1 > Length( z ) then
                            Add( em, i );
                            Add( em, 1 );
                        elif z[pos1] <> i then

                            # There is no y_i in `m', so insert it.
                            InsertElmList( em, 2*pos1-1, i );
                            InsertElmList( em, 2*pos1, 1 );
                        else
                            # We increase the exponent of y_i by 1.
                            em[2*pos1]:= em[2*pos1]+1;
                        fi;

                        AddSet( mons[j], ObjByExtRep( famU, [ em, _q^0 ] ) );
                    od;
                fi;
            od;
        od;

        # `Gk' will contain the part of the Groebner basis corresponding
        # to the weights in `w'. `Glmsk' are the corresponding leading
        # monomials. The list `isdone' keeps track of the positions
        # with a complete part of the GB. `mmm' are the corresponding
        # normal monomials.

        Glmsk:= [ ];
        Gk:= [ ];
        isdone:= [ ];
        mmm:= [ ];

        for j in [1..Length(w)] do

            for i in [1..Length(mons[j])] do
                
                lm:= mons[j][i]![1][1];
                longmon:= ListWithIdenticalEntries( n, 0 );
                for l in [1,3..Length(lm)-1] do
                    longmon[lm[l]]:= lm[l+1];
                od; 
                if Search( lmtab, longmon ) <> fail then
                    
                    # This means that `longmon' reduces modulo `G', 
                    # so we get rid of it.
                    Unbind( mons[j][i] );
                fi;
            od;                
            mons[j]:= Filtered( mons[j], x -> IsBound(x) );

            Glmsk[j]:= [ ];
            Gk[ j ]:= [ ];
            if curlev > maxlev or not w[j] in levels[ curlev ] then

            # `w[j]' is not a weight of the representation; this means that
            # there are no normal monomials of weight `w[j]'. Hence we can
            # add all candidates in `mons' to the Groebner basis.
                
                
                Gk[j]:= mons[j];
                Glmsk[j]:= List( Gk[j], x -> 1 );

                # Normal monomials; empty in this case.
                mmm[j]:= [ ];
                isdone[j]:= true;
            fi;
        od;

        for j in [1..Length(w)] do
            if not IsBound( isdone[j] ) then isdone[j]:= false; fi;
        od;

        # For all remaining weights we know the dimension
        # of the corresponding weight space, and we calculate Groebner
        # basis elements of weight `w' until we can reduce all monomials
        # except a number equal to this dimension.
        # `mmm' will contain the lists of normal monomials, from which we
        # erase elements if they are reducible.

        pos:= List( w, ww -> PositionProperty( orbs, x -> ww in x[2] ) );
        multiplicity:= List( pos, function( j )
                                     if j <> fail then
                                         return orbs[j][1];
                                     fi;
                                     return 0;
                                 end );
                                 
        # Let `a', `b' be two monomials of the same weight; then `a' can only
        # be a factor of `b' if we have `a=b'. So reduction within a
        # weight component is the same as linear algebra. We use the 
        # mutable bases in `sps' to perform the linear algebra.

        sps:= [ ];
        sortmn:= [ ];                         
        for j in [1..Length(w)] do
            if not isdone[j] then
                mmm[j]:= mons[j];
                if Length( mmm[j] ) = multiplicity[j] then
                    isdone[j]:= true;
                else
                    
                    sps[j]:= [ ];
                    sortmn[j]:= List( mmm[j], x -> ExtRepOfObj(x)[1] );
                    Sort( sortmn[j], function(x,y) return
                             lexord( novar, y, x ); end );
                      
                fi;
            fi;
        od;


        we_had_enough:= ForAll( isdone, x -> x );
        le:= Length(GB);

        for i in [1..le] do
            if we_had_enough then break; fi;
            f:= GB[i];

            # `prelcm' will be the leading monomial of `f', represented as
            # a list of lengt `n', if prelcm[i] = k, then the leading
            # monomial contains a factor y_i^k.
            m1a:= f![1][lms[i]];
            prelcm:= ListWithIdenticalEntries( n, 0 );
            for l in [1,3..Length(m1a)-1] do
                prelcm[m1a[l]]:= m1a[l+1];
            od;

            for j in [le,le-1..i] do

                if we_had_enough then break; fi;
                g:= GB[j];
                # `lcm' will be the least common multiple of the LM of `f'
                # and the LM of `g', represented as a list of length n.
                m2a:= g![1][lms[j]];
                lcm:= ShallowCopy( prelcm );
                for l in [1,3..Length(m2a)-1] do
                    lcm[m2a[l]]:= Maximum(lcm[m2a[l]],m2a[l+1]);
                od;

                # We check whether `lcm' is of the correct
                # weight; only in that case we form the S-element.
                pp:= Position( ccc, LinearCombination( lcm, lcombs ) );

                if pp <> fail and not isdone[pp] then

                    # w1*f-w2*g will be the S-element of `f' and `g'.
                    w1:= lcm-prelcm;
                    w2:= lcm;
                    for l in [1,3..Length(m2a)-1] do
                        w2[m2a[l]]:= w2[m2a[l]]-m2a[l+1];
                    od;

                    # We make `w1' and `w2' into QEA elements,
                    # `fac1' and `fac2' respectively.
                    e1:= []; e2:= [];
                    for l in [1..n] do
                        if w1[l] <> 0 then
                            Add( e1, l ); Add( e1, w1[l] );
                        fi;
                        if w2[l] <> 0 then
                            Add( e2, l ); Add( e2, w2[l] );
                        fi;
                    od;

                    fac1:= ObjByExtRep( famU, [ e1, _q^0 ] )*f;
                    fac2:= ObjByExtRep( famU, [ e2, _q^0 ] )*g;

                    # `comp' will be the S-element of `f' and `g'.
                    # We reduce it modulo the elements we already have,
                    # and if it does not reduce to 0 we add it, and remove
                    # its leading monomial from the list of normal
                    # monomials.

                    comp:= LeadingQEAMonomial(novar,fac2)[3]*fac1 -
                           LeadingQEAMonomial(novar,fac1)[3]*fac2;

                    comp:= LeftReduceQEAElement( novar, GB, lms, lmtab,
                                   comp );

                    if comp <> 0*comp then

                        vec:= ListWithIdenticalEntries( Length( sortmn[pp] ), 
                                      0*_q );
                        ecomp:= comp![1];
                        for l in [1,3..Length(ecomp)-1] do
                            vec[ Position( sortmn[pp], ecomp[l] )]:=
                              ecomp[l+1];
                        od;

                        Add( sps[pp], vec );

                        if multiplicity[pp] = 
                           Length( mmm[pp] )-Length(sps[pp]) then
                            vecs:= sps[pp];
                            TriangulizeMat( vecs );
                            vecs:= Filtered( vecs, x -> x <> 0*x );
                            sps[pp]:= vecs;
                        fi;    
                        isdone[pp]:=  multiplicity[pp] = 
                                      Length( mmm[pp] )-Length(sps[pp]);

                        if isdone[pp] then
                            we_had_enough:= ForAll( isdone, x -> x );
                        fi;
                    fi;
                fi;   # done processing this S-element.

            od;   # loop over j
        od;     # loop over i

        for j in [1..Length(w)] do
            
            if multiplicity[j] > 0 then
                
                # We add the elements that we get from the mutable bases to 
                # the Groebner basis. We have to use the order of monomials
                # that is used by GAP to multiply, i.e., not the rev lex order.
                # (Otherwise everything messes up.)
                
                if IsBound( sps[j] ) then              
                    vecs:= sps[j];
                else
                    vecs:= [ ];
                fi;
                
                for l in [1..Length(vecs)] do
                    ecomp:= [ ];
                    cfsc:= [ ];
                    for i in [1..Length(vecs[l])] do
                        if vecs[l][i] <> 0*vecs[l][i] then
                            
                            Add( ecomp, sortmn[j][i] );
                            Add( cfsc, vecs[l][i] );
                        fi;
                        
                    od;
                    SortParallel( ecomp, cfsc );
                    ec:= [ ];
                    for i in [1..Length(ecomp)] do
                        Add( ec, ecomp[i] ); 
                        Add( ec, cfsc[i] );
                    od;
                    
                    Add( Gk[j], ObjByExtRep( famU, ec ) ); 
                od;
                
                Glmsk[j]:= List( Gk[j], x -> LeadingQEAMonomial(
                                  novar, x )[ 4 ] );
                
                le:= Length(GB);
                Append( GB, Gk[j] );
                Append( lms, Glmsk[j] );
                
                # Update the search table....
                
                for i in [1..Length(Gk[j])] do
                    lm:= Gk[j][i]![1][ Glmsk[j][i] ];
                    longmon:= ListWithIdenticalEntries( n, 0 );
                    for l in [1,3..Length(lm)-1] do
                        longmon[lm[l]]:= lm[l+1];
                    od; 
                    Insert( lmtab, longmon, le+i ); 
                od;
                
                # Get rid of the monomials that reduce....
                
                for i in [1..Length(mmm[j])] do
                    lm:= mmm[j][i]![1][1];
                    longmon:= ListWithIdenticalEntries( n, 0 );
                    for l in [1,3..Length(lm)-1] do
                        longmon[lm[l]]:= lm[l+1];
                    od; 
                    if Search( lmtab, longmon ) <> fail then
                        Unbind( mmm[j][i] );
                    fi;
                od;
                mmm[j]:= Filtered( mmm[j], x -> IsBound(x) );
                paths[Position(weights,w[j])]:= mmm[j];
            else
                
                # In this case the weight is not a weight of the 
                # representation;
                # we only update the Groebner basis, and the search table.
                
                le:= Length(GB);
                Append( GB, Gk[j] );
                Append( lms, Glmsk[j] );
                
                for i in [1..Length(Gk[j])] do
                    lm:= Gk[j][i]![1][ Glmsk[j][i] ];
                    longmon:= ListWithIdenticalEntries( n, 0 );
                    for l in [1,3..Length(lm)-1] do
                        longmon[lm[l]]:= lm[l+1];
                    od;
                    Insert( lmtab, longmon, le+i ); 
                od;
            fi;
            
            
            
        od;
        Append( G, Gk );

    od; #loop over k, we now looped through the entire extended weight diagram.


# We construct the module spanned by the normal monomials....

    wvecs:= [ ];
    no:= 0;
    fam:= NewFamily( "WeightRepElementsFamily", IsWeightRepElement );
    fam!.weightRepElementDefaultType:= NewType( fam,
                                               IsPackedElementDefaultRep );

    for k in [1..Length(weights)] do
        mmm:= paths[k];
        for m in mmm do
            no:= no+1;
            Add( wvecs, ObjByExtRep( fam , [ [ no, m, weights[k] ], _q^0 ] ) );
        od;
    od;

    fam!.grobnerBasis:= [ GB, lms, lmtab ];
    fam!.hwModule:= V;
    fam!.weightVectors:= wvecs;
    fam!.dimension:= Length( wvecs );
    fam!.highestWeight:= hw;
    fam!.zeroCoeff:= 0*_q;
    V:= LeftAlgebraModuleByGenerators( A, 
             function(x,v) 
       return QGPrivateFunctions.GenericWeightVecAction(_q,x,v); end, wvecs );
    SetGeneratorsOfLeftModule( V, GeneratorsOfAlgebraModule( V ) );
    
    # to get V from the elements:
    ElementsFamily( FamilyObj( V ) )!.ambientModule:= V;

    B:= Objectify( NewType( FamilyObj( V ),
                            IsBasis and
                            IsBasisOfAlgebraModuleElementSpace and
                            IsAttributeStoringRep ),
                   rec() );
    SetUnderlyingLeftModule( B, V );
    SetBasisVectors( B, GeneratorsOfLeftModule( V ) );
    delmod:= VectorSpace( LeftActingDomain(V), wvecs);
    delB:= BasisOfWeightRepSpace( delmod, wvecs );
    delB!.echelonBasis:= wvecs;
    delB!.heads:= List( [1..Length(wvecs)], x -> x );
    delB!.baseChange:= List( [1..Length(wvecs)], x -> [[ x, _q^0 ]] );
    SetBasis( delmod, delB );
    B!.delegateBasis:= delB;
    SetBasis( V, B );
    SetDimension( V, Length( wvecs ) );

    # If the dimension of V is "small", then we calculate images of the 
    # generators, and store them. Subsequent calculations of images will 
    # use the fast method.
    # If the dimension is higher the slow Calc_Image will be used.
    #
    # The images are stored using two lists: `images' and `baselms'.
    # The second contains the basis elements of `V' in extrep. The first
    # list consists of two parts, one occurring on positions 1..s,
    # and the second one occurring at positions s+rank+1...2*s+rank.
    # The first part contains the images of the F-elements, the second part
    # the images of the E-elements. An image of an element F_i (say) is a list
    # of `dim V' elements, the k-th element of which describes the image 
    # F_i^v_k, where v_k is the k-th basis vector of V. This description 
    # is done by giving
    # two lists [ inds, cfs ], where inds contains the indices of the basis 
    # elements of the image, and cfs their coefficients. Note that the 
    # index is 
    # part of the exrep of a weight vector. So if the k-th element of the
    # list at position i of `images' is [ [3, 15], [q, q^-1] ], then
    # F_i^v_k = q*v_3+q^-1*v_15.   




    # We calculate a list of images of the generators (F,E: the K-action
    # is easily calculated on the fly). We do his by calculating the 
    # images of the generators, and then completing the list by a call
    # to  QGPrivateFunctions.CompleteActList. 
    
    posR:= PositiveRootsInConvexOrder( R );
    act:= List( [1..rank],  ii -> List( wvecs, v -> 
                  QGPrivateFunctions.Calc_Image(_q, 
                          ggg[ Position( posR, SimpleSystemNF(R)[ii] ) ], v ) ) );
    Append( act, List( [1..2*rank], ii -> List( wvecs, v -> 0*v ) ) );
    Append( act, List( [1..rank],  ii -> List( wvecs, v -> 
            QGPrivateFunctions.Calc_Image(_q,
                    ggg[ novar+2*rank+Position( posR, SimpleSystemNF(R)[ii] ) ], v ) ) ) );
    act:= QGPrivateFunctions.CompleteActList( A, delmod, act );
    ims:= [ ];
    for i in [1..novar] do
        im:= [ ];
        for j in [1..Dimension(V)] do
            if IsBound( act[i][j] ) then
                e:= act[i][j]![1];
            else
                e:= 0*wvecs[1];
                e:= e![1];
            fi;
            
            vecs:= [ ]; cfs:= [ ];
            for k in [1,3..Length(e)-1] do
                Add( vecs, e[k][1] );
                Add( cfs, e[k+1] );
            od;
            im[j]:= [ vecs, cfs ];
        od;
        ims[i]:= im;
        im:= [ ];
        l:= novar+rank+i;
        for j in [1..Dimension(V)] do
            if IsBound( act[l+rank][j] ) then
                e:= act[l+rank][j]![1];
            else
                e:= 0*wvecs[1];
                e:= e![1];
            fi;
            
            vecs:= [ ]; cfs:= [ ];
            for k in [1,3..Length(e)-1] do
                Add( vecs, e[k][1] );
                Add( cfs, e[k+1] );
            od;
            im[j]:= [ vecs, cfs ];
        od;
        ims[l]:= im;
    od;
    
    fam!.images:= ims;
    fam!.baselms:=
      List( List( Basis(V), x -> x![1]![1] ), y -> y[1] );
    
    # Set the attributes `WeightsAndVectors', and `HighestWeightsAndVectors'.
    wvecs:= [ ];
    weights:= [ ];
    for i in Basis(V) do
        w:= i![1]![1][1][3];
        pos:= Position( weights, w );
        if pos = fail then
            Add( weights, w );
            Add( wvecs, [ i ] );
        else
            Add( wvecs[pos], i );
        fi;
    od;
    SetWeightsAndVectors( V, [ weights, wvecs ] );
    SetHighestWeightsAndVectors( V, [ [ Basis(V)[1]![1]![1][1][3] ], 
            [ [ Basis(V)[1] ] ] ] );

    return V;
    
end );


############################################################################
##
#M   HighestWeightModule( <QA>, <hw> )
##
##
##
InstallMethod( HighestWeightModule,
     "for a quantized enveloping algebra and a list of nonnegative integers",
     true, [ IsQuantumUEA, IsList ], 0,  
     function( U, hw )

    local   action,  U0,  V,  qpar,  wvecs,  fam,  k,  v,  m,  W,  B,  
            delmod,  delB,  weights,  w,  pos,  map;

       # Here U is non-generic; we construct the highest-weight
       # module over the generic quea, and compute the action by
       # mapping to this one, and mapping back. We note that it is 
       # not possible (in general) to do a Groebner basis thing, because
       # if qpar is a root of 1, then there are zero divisors.     

       action:= function( qpar, famU0, x, v )

           local Vwv, Wwv, ev, ex, im, vi, j, m, vvi, evv, i, k;
           
            Vwv:= FamilyObj( v )!.originalWVecs;
            Wwv:= FamilyObj( v )!.weightVectors;
   
            ev:= ExtRepOfObj( v );
            ex:= ExtRepOfObj( x );
            im:= 0*v;

            for i in [1,3..Length(ev)-1] do
                # calculate the image x^vi, map it back, add it to im.
                vi:= Vwv[ ev[i][1] ];
                for j in [1,3..Length(ex)-1] do
                    m:= ObjByExtRep( famU0, [ ex[j], _q^0 ] );
                    vvi:= m^vi;
                    # map vvi back to the module W:
                    evv:= ExtRepOfObj( ExtRepOfObj( vvi ) );
                    for k in [1,3..Length(evv)-1] do
                        im:= im+Wwv[ evv[k][1] ]*Value( evv[k+1], qpar )*
                                  ex[j+1]*ev[i+1];
                    od;
                od;
            od;
            return im;
       end;

       U0:= QuantizedUEA( RootSystem( U ) );
       V:= HighestWeightModule( U0, hw );
       
       # create the new module
       qpar:= QuantumParameter( U );
       wvecs:= [ ];
       fam:= NewFamily( "WeightRepElementsFamily", IsWeightRepElement );
       fam!.weightRepElementDefaultType:= NewType( fam,
                                                  IsPackedElementDefaultRep );

       for k in [1..Dimension(V)] do
            v:= ExtRepOfObj( ExtRepOfObj( Basis(V)[k] ) );
            m:= ShallowCopy( ExtRepOfObj( v[1][2] ) );
            m[2]:= qpar^0;
            m:= ObjByExtRep( ElementsFamily( FamilyObj(U) ), m );
            Add( wvecs, ObjByExtRep( fam , [ [v[1][1],m,v[1][3]], qpar^0 ]));
       od;

       fam!.hwModule:= V;
       fam!.weightVectors:= wvecs;
       fam!.dimension:= Length( wvecs );
       fam!.highestWeight:= hw;
       fam!.originalWVecs:= BasisVectors( Basis( V ) );
       fam!.zeroCoeff:= 0*qpar;
       W:= LeftAlgebraModuleByGenerators( U, function(x,v) return 
                   action( qpar, ElementsFamily( FamilyObj(U0) ), x, v ); end,
                                           wvecs ); 
       SetGeneratorsOfLeftModule( W, GeneratorsOfAlgebraModule( W ) );

       # We produce a basis directly of weight vectors:
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
       delB!.baseChange:= List( [1..Length(wvecs)], x -> [[ x, qpar^0 ]] );
       B!.delegateBasis:= delB;
       SetBasis( W, B );
       SetDimension( W, Length( wvecs ) );

       # Set the attributes `WeightsAndVectors', and 
       # `HighestWeightsAndVectors'.
       wvecs:= [ ];
       weights:= [ ];
       for k in Basis(W) do
           w:= k![1]![1][1][3];
           pos:= Position( weights, w );
           if pos = fail then
               Add( weights, w );
               Add( wvecs, [ k ] );
           else
               Add( wvecs[pos], k );
           fi;
       od;

       SetWeightsAndVectors( W, [ weights, wvecs ] );
       SetHighestWeightsAndVectors( W, [ [ Basis(W)[1]![1]![1][1][3] ], 
               [ [ Basis(W)[1] ] ] ] );
       
       SetGenericModule( W, V );
       
       map:= function( qp, famW, v )
           
           local   ev,  i;
           
           ev:= List( ExtRepOfObj( ExtRepOfObj( v ) ), ShallowCopy );
           for i in [2,4..Length(ev)] do
               ev[i]:= Value( ev[i], qp );
           od;
           
           return Objectify( famW!.packedType, [ 
                          ObjByExtRep( famW!.underlyingModuleEltsFam, ev ) ] );
       end;
       
       SetCanonicalMapping( W, MappingByFunction( V, W, function( v ) 
           return map( qpar, FamilyObj( Zero(W) ), v ); end ) );
       
       return W;
       
end );


#############################################################################
##
#M  IrreducibleQuotient( <V> )
##
##
InstallMethod( IrreducibleQuotient,
        "for a highest-weight module",
        true, [ IsAlgebraModule ], 0,
        
    function( V )
    
    local   action,  U,  qpar,  R,  vv,  offset,  veclist,  
            leading_elms,  k,  list,  ef,  mons,  e,  d,  i,  dim,  
            mat,  j,  vij,  nullv,  basV,  fam,  wvecs,  W,  B,  
            delmod,  delB,  weights,  w,  pos;
    
    # The idea is to mainly use the action of the original module V;
    # We calculate some extra relations (i.e., elements that are zero in
    # the quotient module), and these are stored in two lists:
    # fam!.rels and fam!.leadingElmNos. The second of these contains the
    # numbers of the weight vectors that reduce, and the first the elements
    # (in extrep) to which they reduce. In the function `action'
    # we first map the vector v to the original module, compute the action 
    # there (using the funcion also stored in the family of v), and reduce
    # using this data.
    
    action:= function( x, v )
        
        local   v1,  lc,  len,  i,  pos,  rr,  j,  vv,  cf;
        
        # v1 will be the same vector in the original module...
        v1:= ObjByExtRep( FamilyObj(v)!.originalModuleElmFam, 
                     ExtRepOfObj( v ) );
        v1:= FamilyObj(v)!.originalAction( x, v1 );
        lc:= ShallowCopy( ExtRepOfObj( v1 ) );
        
        # Now we reduce...
        len:= Length( lc );
        i:= 1;
        while i < Length( lc ) do
            pos:= Position( FamilyObj( v )!.leadingElmNos, lc[i][1] );
            if pos <> fail then
                # the vector rewrites...
                rr:= ShallowCopy( FamilyObj( v )!.rels[pos] );
                for j in [2,4..Length(rr)] do
                    rr[j]:= rr[j]*lc[i+1];
                od;
                for j in [1,3..Length(rr)-1] do
                    pos:= PositionProperty( lc, x -> IsList(x) and 
                                  x[1] = rr[j][1] );
                    if pos <> fail then
                        lc[pos+1]:= lc[pos+1] + rr[j+1];
                        if lc[pos+1] = 0*lc[pos+1] then
                            Unbind( lc[pos] );
                            Unbind( lc[pos+1] );
                            lc:= Filtered( lc, x -> IsBound( x ) );
                        fi;
                    else
                        Add( lc, rr[j] ); Add( lc, rr[j+1] );
                    fi;    
                od;
                Unbind( lc[i] );
                Unbind( lc[i+1] );
                lc:= Filtered( lc, x -> IsBound(x) );
            else
                i:= i+2;
            fi;
            
        od;
        
        # final sorting, and creating of the output:
        vv:= lc{[1,3..Length(lc)-1]};
        cf:= lc{[2,4..Length(lc)]};
        SortParallel( vv, cf, function( a, b ) return a[1] < b[1]; end );
        lc:= [ ];
        for i in [1..Length(vv)] do
            Add( lc, vv[i] ); Add( lc, cf[i] );
        od;
        return ObjByExtRep( FamilyObj( v ), lc );
    end;
    
    if not IsWeightRepElement( ExtRepOfObj( Zero(V) ) ) then
        Error( "IrreducibleQuotient is currently only installed for modules created by HighestWeightModule( )" );
    fi;
    
    U:= LeftActingAlgebra( V );
    qpar:= QuantumParameter( U );
    R:= RootSystem( U );
    vv:= WeightsAndVectors( V )[2];
    offset:= Length( PositiveRoots(R) )+Length( CartanMatrix(R) );
    veclist:= [ ];
    leading_elms:= [ ];
    
    # We compute the elements that are zero in the quotient.
    # These are vectors v such that e_i^v=0, for all e_i monomials in the
    # E's of the same weight as v.
    for k in [1..Length(vv)] do
        list:= vv[k];
        ef:= List( list, x -> ExtRepOfObj( ExtRepOfObj(x)![1][1][2] ) );
        mons:= [ ];
        for e in ef do
            d:= ShallowCopy(e[1]);
            for i in [1,3..Length(d)-1] do
                d[i]:= d[i]+offset;
            od;
            
            Add( mons, [ d, e[2] ] );
        od;
        mons:= List( mons, x -> ObjByExtRep( ElementsFamily( FamilyObj(
                       U ) ), x ) );
        dim:= Length( list );
        mat:= List( [1..dim], x -> List( [1..dim], y -> 0*qpar ) );
        for i in [1..Length(list)] do
            for j in [1..Length(list)] do
                vij:= mons[i]^list[j];
                if vij<>0*vij then
                    mat[j][i]:= vij![1]![1][2];
                else
                    mat[j][i]:= 0*qpar;
                fi;
                
            od;
        od;
        
        nullv:= List( TriangulizedNullspaceMatDestructive( mat ), 
                      x -> LinearCombination( x, list ) );
        # record the `numbers' of the vectors that reduce:
        Append( leading_elms, List( nullv, 
                x -> ExtRepOfObj( ExtRepOfObj(x) )[1][1] ) );
        # Get the list of `right hand sides':
        for i in [1..Length(nullv)] do
            vij:= ShallowCopy( ExtRepOfObj( ExtRepOfObj( -nullv[i] ) ) );
            Unbind( vij[1] ); Unbind( vij[2] );
            vij:= Filtered( vij, x -> IsBound(x) );
            nullv[i]:= vij;
        od;
        Append( veclist, nullv );
        
    od;
    basV:= List( Basis(V), ExtRepOfObj );
    for i in [1..Length( basV )] do
        if ExtRepOfObj( basV[i] )[1][1] in leading_elms then
            Unbind( basV[i] );
        fi;
    od;
    basV:= Filtered( basV, x -> IsBound(x) );
    
    # We make the elements of basV into new weight vectors (now with a
    # different family); to get a clear distinction between the elements
    # of the new module and the old one.
    
    fam:= NewFamily( "WeightRepElementsFamily", IsWeightRepElement );
    fam!.weightRepElementDefaultType:= NewType( fam,
                                                  IsPackedElementDefaultRep );
    wvecs:= List( basV, v -> ObjByExtRep( fam, ExtRepOfObj( v ) ) );
    
    qpar:= QuantumParameter( U );
    fam!.hwModule:= V;
    fam!.weightVectors:= wvecs;
    fam!.dimension:= Length( wvecs );
    fam!.originalModuleElmFam:= FamilyObj( ExtRepOfObj( Zero(V) ) );
    fam!.originalAction:= FamilyObj( Zero(V) )!.left_operation;
    fam!.zeroCoeff:= 0*qpar;
    
    fam!.rels:= veclist;
    fam!.leadingElmNos:=leading_elms;
    
    W:= LeftAlgebraModuleByGenerators( U, action, wvecs ); 
    SetGeneratorsOfLeftModule( W, GeneratorsOfAlgebraModule( W ) );
      
    # We produce a basis directly of weight vectors:

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
    delB!.heads:= List( wvecs, x -> x![1][1][1] );
    delB!.baseChange:= List( [1..Length(wvecs)], x -> [[ x, qpar^0 ]] );
    B!.delegateBasis:= delB;
    SetBasis( W, B );
    SetDimension( W, Length( wvecs ) );

    # Set the attributes `WeightsAndVectors', and 
    # `HighestWeightsAndVectors'.
    wvecs:= [ ];
    weights:= [ ];
    for k in Basis(W) do
        w:= k![1]![1][1][3];
        pos:= Position( weights, w );
        if pos = fail then
            Add( weights, w );
            Add( wvecs, [ k ] );
        else
            Add( wvecs[pos], k );
        fi;
    od;
    
    SetWeightsAndVectors( W, [ weights, wvecs ] );
    SetHighestWeightsAndVectors( W, [ [ Basis(W)[1]![1]![1][1][3] ], 
            [ [ Basis(W)[1] ] ] ] );
    
    
    return W;    
    
end );


#############################################################################
##
#M  CanonicalMapping( <U> )
##
##
InstallMethod( CanonicalMapping,
        "for a non-generic quea", true,
        [ IsQuantumUEA ], 0,
        function( U )
    
    local   map, GenU;
    
    map:= function( fam, qpar, u )
        
        local   eu,  k;
        
        eu:= ShallowCopy( ExtRepOfObj( u ) );
        for k in [2,4..Length(eu)] do
            eu[k]:= Value( NumeratorOfRationalFunction(eu[k]), qpar )/
                    Value( DenominatorOfRationalFunction(eu[k]), qpar );
        od;
        return ObjByExtRep( fam, eu );
    end;
    
    GenU:= QuantizedUEA( RootSystem( U ) );
    
    return MappingByFunction( GenU, U, function( u ) 
        return map( ElementsFamily( FamilyObj(U) ), QuantumParameter(U), u );
    end );
end );

QGPrivateFunctions.weylwordNF:= function( R, path )
        
    local   w,  rho,  wt;
        
    # the WeylWord in lex shortest form...
    w:= WeylWord( path );
    rho:= List( [1..Length( CartanMatrix(R))], x -> 1 );
    wt:= ApplyWeylElement( WeylGroup(R), rho, w );
    return ConjugateDominantWeightWithWord( WeylGroup(R), wt )[2];
end;

#############################################################################
##
#M  HWModuleByGenerator( <W>, <w>, <hw> )
##
##
InstallMethod( HWModuleByGenerator, 
    "for a module, an element, a highest weight", true,
    [ IsAlgebraModule, IsObject, IsList ], 0,

    function( W, v, hw )
    
    local   U,  R,  graph,  pts,  dim,  strings,  wts,  p,  p1,  st,  
            j,  k,  Bil,  g,  bas,  i,  s1,  i1,  n1,  pos,  w,  V,  
            B,  VV,  BVV,  posR,  sim,  acts,  F,  qa,  act,  E,  word;
    
    U:= LeftActingAlgebra( W );
    R:= RootSystem( U );
    graph:= CrystalGraph( R, hw );
    pts:= graph.points;
    dim:= Length( graph.points );

    # We get the strings:
    strings:= [ ];
    wts:= [ ];
    for p in pts do
        
        Add( wts, EndWeight(p) ); 
        p1:= p;
        st:= [];

        word:= QGPrivateFunctions.weylwordNF( R, p1 );
        while word <> [] do
            j:= 0;
            k:= word[1];
            while  WeylWord( p1 ) <> [] and word[1] = k do
                p1:= Ealpha( p1, k );
                word:= QGPrivateFunctions.weylwordNF( R, p1 );                
                j:= j+1;
            od;
            if j > 0 then
                Add( st, k );
                Add( st, j );
            fi;
        od;
        Add( strings, st );        
    od;  

    Bil:= BilinearFormMat( R );
    g:= GeneratorsOfAlgebra( U );

    bas:= [ v ];
    for i in [2..Length(strings)] do
        s1:= ShallowCopy( strings[i] );
        i1:= s1[1];
        n1:= s1[2];
        if n1 > 1 then
           s1[2]:= n1-1;
        else
           Unbind( s1[1] ); Unbind( s1[2] );
           s1:= Filtered( s1, x -> IsBound(x) );
        fi;
        pos:= Position( strings, s1 );
        w:= bas[pos];
        w:= g[ Position( PositiveRootsInConvexOrder(R), 
                    SimpleSystemNF(R)[i1] )]^w;
        w:= w/GaussNumber( n1, _q^( Bil[i1][i1]/2 ) );
        Add( bas, w );
    od;

    V:= SubAlgebraModule( W, bas, "basis" );
    B:= Basis( V, bas );

    VV:= FullSparseRowSpace( QuantumField, Dimension(V) );
    BVV:= Basis( VV );
    posR:= PositiveRootsInConvexOrder( R );
    sim:= SimpleSystemNF( R );

    acts:= [ ];
    for i in [1..Length(sim)] do
        F:= g[ Position( posR, sim[i] ) ];
        Add( acts, List( B, x -> LinearCombination( 
                Coefficients( B, F^x ), BVV  ) ) );
    od;

    for i in [1..Length(sim)] do
        qa:= _q^( Bil[i][i]/2 );
        act:= [ ];
        for j in [1..Length(wts)] do
            Add( act, qa^wts[j][i]*BVV[j] );
        od;
        Add( acts, act );
    od;

    for i in [1..Length(sim)] do
        qa:= _q^( Bil[i][i]/2 );
        act:= [ ];
        for j in [1..Length(wts)] do
            Add( act, qa^-wts[j][i]*BVV[j] );
        od;
        Add( acts, act );
    od;

    for i in [1..Length(sim)] do
        E:= g[ Length(posR)+2*Length(sim)+Position( posR, sim[i] ) ];
        Add( acts, List( B, x -> LinearCombination( 
                Coefficients( B, E^x ), BVV  ) ) );
    od;

    return DIYModule( U, VV, acts ); 

end );

############################################################################
##
#M   InducedQEAModule( <U>, <V> )
##
InstallMethod( InducedQEAModule,
    "for a non-generic qea, and a module", true,
    [ IsQuantumUEA, IsAlgebraModule ], 0,
    
    function( U, V )
    
    local   action,  W,  fam,  M,  wv,  i,  lst,  j,  cf,  map;
    
    action:= function( x, v )

        local   basV,  basW,  Vwv,  Wwv,  famU1,  qpar,  cv,  ex,  im,  
                i,  vi,  j,  m,  cc,  k;
        
        basV:= FamilyObj( v )!.basisV;
        basW:= FamilyObj( v )!.basisW;
        Vwv:= BasisVectors( basV );
        Wwv:= BasisVectors( basW );
        
        famU1:= FamilyObj( v )!.famU1;
        qpar:= FamilyObj( v )!.qPar;
        
        cv:= Coefficients( basW, v );
        ex:= ExtRepOfObj( x );
        im:= 0*v;
        for i in [1..Length(cv)] do
            if not IsZero( cv[i] ) then
                # calculate the image x^vi, map it back, add it to im.
                vi:= Vwv[ i ];
                for j in [1,3..Length(ex)-1] do
                    m:= ObjByExtRep( famU1, [ ex[j], _q^0 ] );
                    # map m^vi back to the module W:
                    cc:= Coefficients( basV, m^vi );
                    for k in [1..Length(cc)] do
                        im:= im+Wwv[ k ]*Value( cc[k], qpar )*
                             ex[j+1]*cv[i];
                    od;
                od;
            fi;
        od;
        return im;
    end;

    if IsGenericQUEA(U) then 
        Error("<U> must be non-generic");
    fi;
    
    W:= FullSparseRowSpace( LeftActingDomain( U ), Dimension(V) );
    fam:= ElementsFamily( FamilyObj( W ) );
    fam!.basisV:= Basis(V);
    fam!.basisW:= Basis(W);
    fam!.qPar:= QuantumParameter( U );
    fam!.famU1:= ElementsFamily( FamilyObj( LeftActingAlgebra( V ) ) );
    
    M:= LeftAlgebraModule( U, action, W );
    
    SetGenericModule( M, V );

    map:= function( famW, famM, v )

         local cf, w;

         cf:= List( Coefficients( famW!.basisV, v ), x -> Value( x, famW!.qPar ) );
         w:= LinearCombination( famW!.basisW, cf );
         return Objectify( famM!.packedType, [w] );
    end;
     
    SetCanonicalMapping( M, MappingByFunction( V, M, function( v ) 
        return map( FamilyObj( ExtRepOfObj( Zero(M) ) ), FamilyObj( Zero(M) ), v );
    end ) );

    return M;
    
end );

#############################################################################
##
#M  WeightsAndVectors( <W> )
##
##
InstallMethod( WeightsAndVectors,
    "for a non-generic module", true,
    [ IsAlgebraModule ], 0,
    function( W )

    local V, wv, wv1, qpar, i, j, lst, cf;

    if not HasGenericModule( W ) then
        TryNextMethod();
    fi;

    V:= GenericModule( W );
    wv:= WeightsAndVectors( V )[2];
    wv1:= [ ];
    qpar:= QuantumParameter( LeftActingAlgebra( W ) );
    for i in [1..Length(wv)] do
         lst:= [ ];
         for j in wv[i] do
             cf:=List(  Coefficients( Basis(V), j ), x -> Value( x, qpar ) );
             Add( lst, LinearCombination( Basis(W), cf ) );
         od;
         wv1[i]:= lst;
     od;
     return [ WeightsAndVectors( V )[1], wv1 ];

end );

QGPrivateFunctions.BasisOfModule:= function( U, hw )

    local R, graph, dim, edges, bas, one, i, k, seq, pos, mon, posn;

    R:= RootSystem( U );
    graph:= CrystalGraph( R, hw );
    dim:= Length(graph.points);
    edges:= graph.edges;
    bas:= [ ];
    one:= One( U );

    posn:= [ ];
    # posn[i] will be the first position where in edges there is an
    # edge with endpoint i:
    for i in [1..Length(edges)] do
        k:= edges[i][1][2];
        if not IsBound( posn[k] ) then posn[k]:= i; fi;
    od;  

    for i in [1..dim] do
        seq:= [ ];
        k:= i;
        while k <> 1 do
            pos:= posn[k];
            Add( seq, edges[pos][2] );
            k:= edges[pos][1][1];
        od;
        seq:= Reversed( seq );
        mon:= one;
        
        for k in seq do
            mon:= Falpha( mon, k );
        od;
 
        Add( bas, mon );
    od;
    return [ bas, List( graph.points, EndWeight ) ];
    
end;

#############################################################################
##
#M   IrreducibleQuotient( <W> )
##
InstallMethod( IrreducibleQuotient,
    "for a module over a non-generic qea", true,
    [ IsAlgebraModule ], 0,
    
    function( W )
    
    local   V,  hwv,  U,  qpar,  R,  rootBas,  offset,  vecs,  inds,  
            mns,  wts,  fam,  v0,  bv0,  k,  ee,  ff,  rt,  i,  d,  j,  
            mat,  vij,  cfs,  M,  dim,  imgs,  preims,  pos,  im,  cf,  
            action;

    if IsWeightRepElement( ExtRepOfObj(Zero(W)) ) then
        TryNextMethod();
    fi;

    if not HasGenericModule( W ) then
        Error("<W> must be an induced module from a module over a generic quantized enveloping algebra.");
    fi;

    V:= GenericModule( W );
    hwv:= HighestWeightsAndVectors( V );
    if Length( hwv[1] )<> 1 or Length( hwv[2] ) <> 1 then
        Error("<W> is not a highest weight module");
    fi;
    
    U:= LeftActingAlgebra( W );
    qpar:= QuantumParameter( U );
    R:= RootSystem( U );
    rootBas:= Basis( VectorSpace( Rationals, SimpleRootsAsWeights(R) ),
                     SimpleRootsAsWeights( R ) );
    offset:= Length( PositiveRoots(R) )+Length( CartanMatrix(R) );
    vecs:= [ ];
    inds:= [ ];

    #mns:= QGPrivateFunctions.BasisOfModule( U, hwv[1][1] );
    mns:= WeightsAndVectors( W );
    wts:= mns[1];
    mns:= mns[2];

    # We compute the elements that are zero in the quotient.
    # These are vectors v such that e_i^v=0, for all e_i monomials in the
    # E's of the same weight as v.

    fam:= ElementsFamily( FamilyObj( U ) );
    v0:= Image( CanonicalMapping(W), hwv[2][1][1] );
    bv0:= Basis( VectorSpace( LeftActingDomain(W), [v0] ), [v0] );
    
    for k in [1..Length(wts)] do
        
         ee:= [ ];
         ff:= mns[k];
            
         rt:= Coefficients( rootBas, hwv[1][1] - wts[k] );
         ee:= QGPrivateFunctions.GetMonomials( U, rt );
         for i in [1..Length(ee)] do
              d:= ShallowCopy( ExtRepOfObj( ee[i] )[1] );
              for j in [1,3..Length(d)-1] do
                   d[j]:= d[j]+offset;
              od;
              ee[i]:= ObjByExtRep( fam, [ d, qpar^0 ] );
         od;
            
         mat:= List( [1..Length(ff)], x -> 
                        List( [1..Length(ee)], y -> 0*qpar ) );
         for i in [1..Length(ee)] do
             for j in [1..Length(ff)] do
                 vij:= ee[i]^ff[j];
                 mat[j][i]:= Coefficients( bv0, vij )[1];
             od;
         od;
         cfs:= List( NullspaceMatDestructive( mat ), x ->
                      Coefficients( Basis(W), LinearCombination(ff,x) ) );
         TriangulizeMat( cfs );
         Append( vecs, cfs );
         Append( inds, List( cfs, x -> PositionProperty( x, y -> y <> 0 ) ) );

    od;

    M:= FullSparseRowSpace( LeftActingDomain(W), Dimension(W)-Length(vecs) );
    dim:= Dimension( W );
    k:= Dimension( M );
    imgs:= [ ];
    preims:= [ ];
    for i in [dim, dim-1..1] do
         pos:= Position( inds, i );
         if pos <> fail then
             im:= Zero( M );
             cf:= vecs[pos];
             j:= PositionProperty( cf, x -> x<> 0 ) + 1;
             while j <= Length( cf ) do
                   if cf[j] <> 0*cf[j] then
                       im:= im - cf[j]*imgs[dim-j+1];
                   fi;
                   j:= j+1;
             od;
             Add( imgs, im );
         else
             Add( imgs, Basis(M)[k] );
             Add( preims, Basis(W)[i] );
             k:= k-1;
         fi;
    od;
    
    imgs:= Reversed( imgs );
    preims:= Reversed( preims );
    fam:= ElementsFamily( FamilyObj( M ) );
    fam!.images:= imgs;
    fam!.preimages:= preims;
    fam!.basisM:= Basis(M);
    fam!.basisW:= Basis(W);

    action:= function( x, m )

        local fam,  cf,  v;
        
        fam:= FamilyObj( m );
        cf:= Coefficients( fam!.basisM, m );
        v:= x^( cf*fam!.preimages );
        cf:= Coefficients( fam!.basisW, v );
        return cf*fam!.images;

    end;
            
    return LeftAlgebraModule( U, action, M );
    
end );


InstallMethod( HWModuleByTensorProduct, 
    "for a quantum uea, and a weight", true,
    [ IsQuantumUEA and IsGenericQUEA, IsList ], 0,
    function( U, hw )

      local left_quantum_action_generic, order, G_order, bvv,
            fund, wt, M, i, j, W, R, rank, Wg, graph, paths, strings, wts,
            p, p1, st, word, k, Bil, g, bas, s1, i1, n1, pos, w, Gb, Gwts, 
            pairs, vecs, Gwt, v, ev, cc, val, ccc, pol, V, BV, posR, sim, 
            VV, BVV, acts, qa, act, fam, cryst_module, fund_mod; 


      left_quantum_action_generic:= function( U, str, pp, tn )
    
            # Left action on a tensor product, but only for F_a, E_a, where a is 
            # a simple root. Then the action is easy...
            # When everyting is defined over Q(q). 
            # `pp' is the positiion of the relevant simple root; 
            # if str = "F" then we act with F_pp, otherwise with E_pp.
            # tn is an element of the tensor product of modules.
    
            local   deg, R,  noPosR,  rank,  B,  res,  ex,  etn,  i,  
                    vec,  rule,  u,  v,  tv,  rr,  Ka,  x;
    
            if tn = 0*tn then 
               return tn;
            fi;
    
            deg:= Length( tn![1][1] );

            R:= RootSystem( U );
            noPosR:= Length( PositiveRoots(R) );
            rank:= Length( CartanMatrix(R) );
            B:= BilinearFormMatNF( R );

            if str = "F" then
                x:= GeneratorsOfAlgebra( U )[ Position( PositiveRootsInConvexOrder(R), 
                                SimpleSystem(R)[pp] ) ];
                Ka:= GeneratorsOfAlgebra( U )[ noPosR+2*pp-1];
                rule:= [ ];
                for i in [1..deg] do
                    rr:= List( [1..i-1], x -> Ka );
                    Add( rr, x );
                    Append( rr, List( [i+1..deg], x -> One(U) ) );
                    Add( rule, rr ); Add( rule, _q^0 );
                od;

            else
                x:= GeneratorsOfAlgebra( U )[ Position( PositiveRootsInConvexOrder(R), 
                              SimpleSystem(R)[pp] ) + 2*rank + noPosR ];
                Ka:= GeneratorsOfAlgebra( U )[ noPosR+2*pp ];
                rule:= [ ];
                for i in [1..deg] do
                     rr:= List( [1..i-1], x -> One( U ) );
                     Add( rr, x );
                     Append( rr, List( [i+1..deg], x -> Ka ) );
                     Add( rule, rr ); Add( rule, _q^0 );
                od;
            fi;

            res:= [ ];  # result
            ex:= ExtRepOfObj( x );
            etn:= ExtRepOfObj( tn );
    
            vec:= List( etn, ShallowCopy );
        
            # we apply rule to all tensors in vec, and collect
            # everything in tv
            tv:= [ ]; 
            for u in [1,3..Length(vec)-1] do
                for v in [1,3..Length(rule)-1] do
                    Add( tv, List( [1..Length(vec[u])], x -> rule[v][x]^vec[u][x]) );
                    Add( tv, vec[u+1]*rule[v+1] );
                od;
            od;
                
            # normalization...
            tv:= ObjByExtRep( FamilyObj(tn), tv );
            tv![2]:= false;
            return ConvertToNormalFormMonomialElement(tv);

      end;

      order:= function( p1, p2 )

           local wd1, wd2, s1, s2, i;
 
           wd1:= QGPrivateFunctions.weylwordNF( R, p1[1] );
           wd2:= QGPrivateFunctions.weylwordNF( R, p2[1] );
           if wd1 = wd2 then
               # see which of the strings is bigger
               s1:= p1[2]; s2:= p2[2];
               for i in [2,4..Length(s1)] do
                   if s1[i] <> s2[i] then
                      return s1[i] > s2[i];
                   fi;
               od;
           else

               if Length( wd1 ) <> Length( wd2 ) then 
                    return Length( wd1 ) < Length( wd2 );
               fi;

               # see whether wd1 <_lex wd2....
               i:= 1;
               while i <= Length( wd1 ) do
                   if wd1[i] <> wd2[i] then return wd1[i] < wd2[i]; fi;
                   i:= i+1;
               od;

           fi;

      end;

      cryst_module:= function( V )
    
         local   U,  R,  sim,  posR,  rank,  s,  g,  C,  W,  acts,  k,  x,  pos,  f, B;

         # This function takes the module V, and makes an isomorphic module,
         # where the standard basis is the crystal basis. In the sequel we only
         # compute actions of generators, so we do not need to compute the 
         # actions of, e.g., F_{\beta} where \beta is a non-simple root.
         # So the module returned looks like one created by DIYModule, but the
         # difference is that the `actionlist' is incomplete.
    
         U:= LeftActingAlgebra(V);
         R:= RootSystem(U);
         sim:= SimpleSystemNF(R);
         posR:= PositiveRootsInConvexOrder( R );
         rank:= Length( sim );
         s:= Length( posR );
         g:= GeneratorsOfAlgebra( U );
         C:= CrystalBasis(V);
    
         W:= FullSparseRowSpace( QuantumField, Dimension(V) );
         acts:= [ ];

         for k in [1..rank] do
            pos:= Position( posR, sim[k] );
            x:= g[ pos ];
            acts[ pos ]:= List( C, v -> LinearCombination( Coefficients( C, x^v ),
                                    Basis(W) ) );
         od;
    
         for k in [1..rank] do
            x:= g[ s+2*k-1 ];
            Add( acts, List( C, v -> LinearCombination( Coefficients( C, x^v ),
                                    Basis(W) ) ) );
         od;
         for k in [1..rank] do
            x:= g[ s+2*k ];
            Add( acts, List( C, v -> LinearCombination( Coefficients( C, x^v ),
                                    Basis(W) ) ) );
         od;
    
         for k in [1..rank] do
            pos:= Position( posR, sim[k] );
            x:= g[ s+2*rank+ pos ];
            acts[ s+2*rank+pos ]:= List( C, v -> LinearCombination( 
                                                   Coefficients( C, x^v ), Basis(W) ) );
         od;
    
         B:= BilinearFormMatNF( R );
         f:= function( x, u ) return 
               QGPrivateFunctions.DIYAction( W, s, rank, B, posR, acts, x, u ); end;
         return LeftAlgebraModule( U, f, W );

      end;


      G_order:= function( a, b )

           local i,m,n;

           for i in [1..Length( a[2] )] do
               m:= Position( bvv[i], a[2][i] );
               n:= Position( bvv[i], b[2][i] );
               if m<>n then return m<n; fi;
           od;
      end;  

      R:= RootSystem( U );
      rank:= Length( CartanMatrix( R ) );
      Wg:= WeylGroup( R );
      Bil:= BilinearFormMat( R );
      g:= GeneratorsOfAlgebra( U );
      posR:= PositiveRootsInConvexOrder( R );
      sim:= SimpleSystemNF( R );

      if HasFundamentalModules( U ) then
          fund_mod:= ShallowCopy( FundamentalModules( U ) );
      else
          fund_mod:= [ ];
      fi;
      fund:= [ ];
      for i in [1..Length(hw)] do
          if hw[i] > 0 then
             wt:= 0*hw; wt[i]:= 1;
             if IsBound( fund_mod[i] ) then
                 M:= fund_mod[i];
             else
                 M:= HighestWeightModule( U, wt );
                 fund_mod[i]:= M;
             fi;
             M:= cryst_module( M );
             for j in [1..hw[i]] do Add( fund, M ); od;
          fi;
      od;
      U!.FundamentalModules:= Immutable( fund_mod );

      W:= TensorProduct( fund );

      fam:= FamilyObj( Zero(W) );
      bvv:= List( fam!.constituentBases, x -> BasisVectors( x ) );


      # Now we compute the crystal graph, and the basis of the tensor product
      # corresponding to the `stringmonomials'.

      graph:= CrystalGraph( R, hw );
      paths:= graph.points;

      # We get the strings:
      strings:= [ ];
      wts:= [ ];
      for p in paths do

           if not EndWeight( p ) in wts then Add( wts, EndWeight(p) ); fi;
           p1:= p;
           st:= [];

           word:= QGPrivateFunctions.weylwordNF( R, p1 );
           while word <> [] do
               j:= 0;
               k:= word[1];
               while  WeylWord( p1 ) <> [] and word[1] = k do
                  p1:= Ealpha( p1, k );
                  word:= QGPrivateFunctions.weylwordNF( R, p1 );     
                  j:= j+1;
               od;
               if j > 0 then
                   Add( st, k );
                   Add( st, j );
                fi;
           od;
           Add( strings, st );        
      od;  

      bas:= [ Basis(W)[1] ];
      for i in [2..Length(strings)] do
           s1:= ShallowCopy( strings[i] );
           i1:= s1[1];
           n1:= s1[2];
           if n1 > 1 then
              s1[2]:= n1-1;
           else
              Unbind( s1[1] ); Unbind( s1[2] );
              s1:= Filtered( s1, x -> IsBound(x) );
           fi;
           pos:= Position( strings, s1 );
           w:= bas[pos];
           w:= left_quantum_action_generic( U, "F", i1, w );
           w:= w/GaussNumber( n1, _q^( Bil[i1][i1]/2 ) );
           Add( bas, w );
      od;

      # Now bas is a basis of the submodule of W generated by Basis(W)[1].
      # By the triangular algorithm we get the canonical basis of this 
      # submodule.

      Gb:= [ ];
      Gwts:= [ ];

      for wt in wts do
          # get all pairs, path, string that have this weight.
          pairs:= [ ];
          vecs:= [ ];
          for i in [1..Length(paths)] do
              if EndWeight( paths[i] ) = wt then 
                  
                  Add( pairs, [ paths[i], strings[i] ] );
                  Add( vecs, bas[i] );
              fi;
          od;

          SortParallel( pairs, vecs, order );

          Gwt:= [ ];

          for i in [1..Length(vecs)] do
               v:= vecs[i];
               ev:= v![1];
               for j in [i-1,i-2..1] do
                   pos:= Position( ev, Gwt[j][2] );
                   if pos <> fail then
                      cc:= CoefficientsOfUnivariateLaurentPolynomial( ev[pos+1] );
                
                      # if this has non-positive powers of q, then we repair this
                      # situation by adding a bar-invariant multiple of the 
                      # appropriate canonical element.

                      if cc[2] <= 0 then
                         val:= cc[2];
                         k:= 1;
                         ccc:= List( [1..-2*val+1], x -> 0 );
                         while k <= -val+1 and k <= Length(cc[1]) do
                             ccc[k]:= cc[1][k];
                             ccc[-2*val+2-k]:= cc[1][k];
                             k:= k+1;
                         od;

                         pol:= LaurentPolynomialByCoefficients( 
                                       FamilyObj(1), ccc, val,
                                       QGPrivateFunctions.indetNo );
                         v:= v-pol*Gwt[j][1];
                         ev:= v![1];
                      fi;
                   fi;
               od;

               pos:= Position( ev, _q^0 );
               Add( Gwt, [ v, ev[pos-1] ] );
               Sort( Gwt, G_order );
          od;
          
          Append( Gb, List( Gwt, x -> x[1] ) );
          Append( Gwts, List( Gwt, x -> wt ) );
     
      od;

      # Gb is the canonical basis; we compute the actions of the generators
      # with respect to this basis, and return the corresponding DIYModule.

      V:= VectorSpace( QuantumField, Gb );
      BV:= Basis( V, Gb );

      VV:= FullSparseRowSpace( QuantumField, Length( Gb ) );
      BVV:= Basis( VV );

      acts:= [ ];
      for i in [1..Length(sim)] do
        Add( acts, List( Gb, x -> LinearCombination( 
                Coefficients( BV, left_quantum_action_generic( U, "F", i, x ) 
                                              ), BVV ) ) );
      od;

      for i in [1..Length(sim)] do
          qa:= _q^( Bil[i][i]/2 );
          act:= [ ];
          for j in [1..Length(Gwts)] do
              Add( act, qa^Gwts[j][i]*BVV[j] );
          od;
          Add( acts, act );
      od;

      for i in [1..Length(sim)] do
          qa:= _q^( Bil[i][i]/2 );
          act:= [ ];
          for j in [1..Length(Gwts)] do
              Add( act, qa^-Gwts[j][i]*BVV[j] );
          od;
          Add( acts, act );
      od;

      for i in [1..Length(sim)] do
          Add( acts, List( Gb, x -> LinearCombination( 
                  Coefficients( BV, left_quantum_action_generic( U, "E", i, x ) 
                                                ), BVV ) ) );
      od;
 
      M:= DIYModule( U, VV, acts ); 
      SetCrystalBasis( M, Basis(M) );
      return M;

end );

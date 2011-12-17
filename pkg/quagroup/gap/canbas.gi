##########################################################################
##
#W  canbas.gd                  QuaGroup                     Willem de Graaf
##
##
##  Methods for canonical bases.
##

## just a private function, maybe make it "public" later
QGPrivateFunctions.GetMonomials:= function( U, rt )
    
    local   R,  posR,  nu,  i,  oldlev,  mlist,  deg,  newlev,  mon,  
            rts,  j,  rr,  pos,  mn1,  mons,  m,  emon,  k;
    
    R:= RootSystem( U );
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
    
    mons:= [ ];

    for m in mlist do
        emon:= [ ];
        for k in [1..Length(m)] do
            if m[k] <> 0*m[k] then
                Add( emon, k ); Add( emon, m[k] );
            fi;
        od;
        Add( mons, ObjByExtRep( ElementsFamily( FamilyObj( U ) ), 
                [ emon, _q^0 ] ) );
    od;
    return mons;
end;

QGPrivateFunctions.lexicOrd:= function( m1, m2 )
    
    # lex for monomials of the form [1,2,2,3,3,2]=x_1^2x_2^3x_3^2
    # x_1^2x_2^3 < x_1x_2^3 etc.
    
    local   len1,  len2,  min,  i;
    
    len1:= Length(m1); len2:= Length(m2);
    min:= Minimum( len1, len2 );
    
    for i in [1,3..min-1] do
        if m1[i] <> m2[i] then
            return m1[i] < m2[i];
        elif m1[i+1] <> m2[i+1] then
            return m1[i+1] > m2[i+1];
        fi;
    od;
    
    return len1 < len2;
end;


#############################################################################
##
#M  CanonicalBasis( <U> )
##
InstallMethod( CanonicalBasis, 
        "for a quantized uea",
        true, [ IsQuantumUEA ], 0,
        function( U )
    
    local   B;
    
#+  Is the canonical basis of the quantized universal enveloping algebra
#+  <U>. When this is construted nothing is computed. By using 
#+  `PBWElements', `MonomialElements', `Strings' information about elements
#+  of the canonical basis can be obtained. 
        
    B:= Objectify( NewType( FamilyObj( U ), IsCanonicalBasisOfQuantumUEA
                                       and  IsAttributeStoringRep ),
                rec() );
    B!.quantizedUEA:= U;
    return B;
end);

#############################################################################
##
#M   PrintObj( <B> )
##
InstallMethod( PrintObj,
        "for a canonical basis of a quantized uea",
        true, [ IsCanonicalBasisOfQuantumUEA ], 0,
        function( B )
    
    Print("<canonical basis of ",B!.quantizedUEA," >");
    
end );

#############################################################################
##
#F  GetCanonicalElements( <B>, <rt> )
##
##  This function does the work for `PBWElements', `MonomialElements',
##  `Strings'.
##
QGPrivateFunctions.GetCanonicalElements:= function( B, rt )
    
    local   lexord,  lex,  U,  R,  posR,  nu,  i,  oldlev,  mlist,  
            deg,  newlev,  mon,  rts,  j,  rr,  pos,  mn1,  mons,  m,  
            emon,  k,  w0,  strings,  b,  st,  a,  g,  ip,  p,  ees,  
            list,  slist,  len,  eg,  cc,  val,  ccc,  pol,  em,  
            list1,  mlist1,  slist1;

    
    lexord:= function( s1, s2 )
    
        # lex ordering for adapted strings:
        # [2,0,3,0,1] < [2,0,4,0,1] etc.
        
        local   k;
    
        for k in [1..Length(s1)] do
            if s1[k] <> s2[k] then
                return s1[k] < s2[k];
            fi;
        od;
        # they are equal...
        return false;
    end;
    
    U:= B!.quantizedUEA;
    
    if not IsGenericQUEA( U ) then
        Error( "Computing the canonical basis only works for generic quea" );
    fi;
    
    R:= RootSystem( U );
    posR:= PositiveRootsInConvexOrder( R );
    
    # Now we calculate the adapted strings of weight `rt'.
    # An adapted string is represented as a
    # list of the same length as w0, with on the i-th position, the 
    # exponent of the w0[i]-th path operator. 
    
    # First we calculate all monomials of weight `rt'. The algorithm
    # is as follows: the monomial of the highest degree consists of
    # F_a only, where a is a simple root. If m is a monomial of degree
    # d, then we construct monomials of degree d-1 as follows. We write
    # down all positive roots involved in the generators that constitute 
    # m. We see which pairs sum to a root, and we decrease the exponents
    # corresponding to such a pair, while increasing the exponent
    # corresponding to their sum (all by 1).

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
    
    mons:= [ ];

    for m in mlist do
        emon:= [ ];
        for k in [1..Length(m)] do
            if m[k] <> 0*m[k] then
                Add( emon, k ); Add( emon, m[k] );
            fi;
        od;
        Add( mons, ObjByExtRep( ElementsFamily( FamilyObj( U ) ), 
                [ emon, _q^0 ] ) );
    od;
    
    w0:= LongestWeylWord( R );
    strings:= [ ];
    
    # Now for each monomial we calculate thecorresponding string,
    # by acting with the Kashiwara operators.
    
    for m in mons do

        b:= m;
        st:= ShallowCopy( w0*0 );
        for i in [1..Length(w0)] do
            j:= 0;
            while b <> fail do
                a:= b;
                b:= Ealpha( b, w0[i] );
                j:= j+1;
            od;
            j:= j-1;
            b:= a;
            st[i]:= j;
        od;
        Add( strings, st );
    od;
    
    Sort( strings, function(x,y) return lexord(y,x); end );
    
    # `m' will be the list of monomials corresponding to the strings;
    # as linear combinations of PBW elements.
    
    m:= [ ];
    g:= GeneratorsOfAlgebra( U );
    rts:= PositiveRootsInConvexOrder( R );
    pos:= List( SimpleSystemNF( R ), x -> Position( rts, x ) );
    ip:= List( pos, x -> rts[x]*( BilinearFormMatNF(R)*rts[x] )/2 );
    for i in strings do
        p:= One( U );
        for j in [1..Length(i)] do
            if i[j] <> 0 then
                p:= p*g[ pos[w0[j]] ]^i[j]/GaussianFactorial( 
                            i[j], _q^ip[w0[j]] );
            fi;    
        od;
        Add( m, p );
      
    od;
    
    # Now we represent the strings differently. Namely as a list of 
    # index-exponent pairs of the form [ w0[i], e_i ]. `mons' will
    # be the list of monomials corresponding to the strings.
    
    ees:= List( strings, x -> Filtered( 
                  List( [1..Length(w0)],  y -> [ w0[y], x[y] ] ), 
                  z -> z[2] <> 0 ) );
    
    strings:= List( ees, x -> Flat(x) );  # the form in which they
                                          # will appear in the output.
    
    ees:= List( ees, x -> [Flat( List( x, y -> [pos[y[1]],y[2]] ) ), _q^0] );
    mons:= List( ees, x -> ObjByExtRep( FamilyObj(g[1]), x ) );
    
    # Now `list' will contain lists of length two; the first element
    # is a canonical element, in pbw form, the second element is the 
    # ext rep of its principal monomial,
    # `mlist' wil contain the same elements, now as linear combinations
    # of monomials in the generators,
    # `slist' contains the corresponding strings.
    
    list:= [ ];
    mlist:= [ ];
    slist:= [ ];
    len:= 0;
    for i in [1..Length( m )] do
        g:= m[i];
        mon:= mons[i];
        eg:= ExtRepOfObj( g );
        for j in [len,len-1..1] do
            pos:= Position( eg, list[j][2] );
            if pos <> fail then
                cc:= CoefficientsOfUnivariateLaurentPolynomial( eg[pos+1] );
                
                # if this has non-positive powers of q, then we repair this
                # situation by adding a bar-invariant multiple of the 
                # appropriate canonical element.
                if cc[2] <= 0 then
                    val:= cc[2];
                    k:= 1;
                    ccc:= [ ];
                    while k <= -val+1 and k <= Length(cc[1]) do
                        ccc[k]:= cc[1][k];
                        ccc[-2*val+2-k]:= cc[1][k];
                        k:= k+1;
                    od;
                   
                    pol:= LaurentPolynomialByCoefficients( 
                                  FamilyObj(1), ccc, val, 
                                  QGPrivateFunctions.indetNo );
                    g:= g-pol*list[j][1];
                    mon:= mon-pol*mlist[j];
                    eg:= ExtRepOfObj( g );
                fi;
            fi;
        od;
        for j in [2,4..Length(eg)] do
            if CoefficientsOfUnivariateLaurentPolynomial(eg[j])[2] = 0 then
                em:= eg[j-1]; 
                break;
            fi;
        od;
        
        # look for correct position
        # lexicographic ordering of principal monomials
        pos:= fail;
        j:= len;
        
        while pos = fail and j > 0 do
            if QGPrivateFunctions.lexicOrd( list[j][2], em ) then
                pos:= j+1;
            else
                j:= j-1;
            fi;
        od;
                
        if pos = fail then
            pos:= 1;
        fi;
        
        # Insert on the correst position:
        list1:= list{[1..pos-1]};
        Add( list1, [ g, em ] );
        Append( list1, list{[pos..len]} );
        mlist1:= mlist{[1..pos-1]};
        Add( mlist1, mon );
        Append( mlist1, mlist{[pos..len]} );
        slist1:= slist{[1..pos-1]};
        Add( slist1, strings[i] );
        Append( slist1, slist{[pos..len]} );
        
        list:= list1; mlist:= mlist1; slist:= slist1;
        len:= len+1;
    od;
    
    return [ List( list, x -> x[1] ), mlist, slist ];
    
end;

#############################################################################
##
#M   PBWElements( <B>, <rt> )
#M   MonomialElements( <B>, <rt> )
#M   Strings( <B>, <rt> )
##
InstallMethod( PBWElements, 
        "for canonical basis and a positive elt from the root lattice",
        true, [ IsCanonicalBasisOfQuantumUEA, IsList ],
        function( B, rt )
    
    local   isLowR,  pos,  U,  bar,  mons,  G,  i,  elm,  ex,  len,  
            cfs,  j,  cf,  ec,  val,  k,  ll;
    
    isLowR:= ValueOption( "lowrank" );
    if isLowR <> fail and isLowR then
        # we use a different method...
        
        if not IsBound( B!.pbwElms2 ) then
            B!.pbwElms2:= [ ];
        else
            pos:= PositionProperty( B!.pbwElms2, x -> x[1] = rt );
            if pos <> fail then
                return B!.pbwElms2[pos][2];
            fi;
        fi;
        
        U:= B!.quantizedUEA;    
        bar:= BarAutomorphism( U );
        mons:= QGPrivateFunctions.GetMonomials( U, rt );
        Sort( mons, function( a, b ) 
            return QGPrivateFunctions.lexicOrd( a![1][1], b![1][1] ); 
        end );
        
        G:= [ mons[1] ];
        for i in [2..Length(mons)] do
            
            elm:= Image( bar, mons[i] ) - mons[i];
            ex:= elm![1];
            len:= i-1;
            cfs:= [ ];
            for j in [len, len-1..1] do
                pos:= Position( ex, mons[j]![1][1] );
                if pos = fail then
                    Add( cfs, 0*_q );
                else
                    cf:= ex[pos+1];
                    Add( cfs, cf );
                    elm:= elm - cf*G[j];
                    ex:= elm![1];
                fi;
            od;
            
            for j in [1..Length(cfs)] do
                ec:= CoefficientsOfLaurentPolynomial( cfs[j] );
                val:= -ec[2];
                cf:= 0*_q;
                for k in [1..val] do
                    cf:= cf + ec[1][ val+1+k ]*_q^k;
                od;
                cfs[j]:= cf;
            od;
            cfs:= Reversed( cfs );
            
            Add( G, mons[i] + cfs*G );
            
        od;
        
        Add( B!.pbwElms2, [ rt, G ] );
                
        return G;
    fi;    
    
    if not IsBound( B!.pbwElms ) then
        B!.pbwElms:= [ ];
        B!.monomialElms:= [ ];
        B!.strings:= [ ];            
    fi;
        
    pos:= PositionProperty( B!.pbwElms, x -> x[1] = rt );
    if pos <> fail then
        return B!.pbwElms[pos][2];
    else
        ll:= QGPrivateFunctions.GetCanonicalElements( B, rt );
        Add( B!.pbwElms, [ rt, ll[1] ] );
        Add( B!.monomialElms, [ rt, ll[2] ] );
        Add( B!.strings, [ rt, ll[3] ] );
        return ll[1];
    fi;
        
 end);

InstallMethod( MonomialElements, 
        "for canonical basis and a positive elt from the root lattice",
        true, [ IsCanonicalBasisOfQuantumUEA, IsList ],
        function( B, rt )
    
    local   pos,  ll;
    
    if not IsBound( B!.pbwElms ) then
        B!.pbwElms:= [ ];
        B!.monomialElms:= [ ];
        B!.strings:= [ ];            
    fi;
    
    pos:= PositionProperty( B!.pbwElms, x -> x[1] = rt );
    if pos <> fail then
        return B!.monomialElms[pos][2];
    else
        ll:= QGPrivateFunctions.GetCanonicalElements( B, rt );
        Add( B!.pbwElms, [ rt, ll[1] ] );
        Add( B!.monomialElms, [ rt, ll[2] ] );
        Add( B!.strings, [ rt, ll[3] ] );
        return ll[2];
    fi;
    
end);


InstallMethod( Strings, 
        "for canonical basis and a positive elt from the root lattice",
        true, [ IsCanonicalBasisOfQuantumUEA, IsList ],
        function( B, rt )
    
    local   pos,  ll;
    
    if not IsBound( B!.pbwElms ) then
        B!.pbwElms:= [ ];
        B!.monomialElms:= [ ];
        B!.strings:= [ ];            
    fi;
    
    pos:= PositionProperty( B!.pbwElms, x -> x[1] = rt );
    if pos <> fail then
        return B!.strings[pos][2];
    else
        ll:= QGPrivateFunctions.GetCanonicalElements( B, rt );
        Add( B!.pbwElms, [ rt, ll[1] ] );
        Add( B!.monomialElms, [ rt, ll[2] ] );
        Add( B!.strings, [ rt, ll[3] ] );
        return ll[3];
    fi;
        
end);

QGPrivateFunctions.MoveExpVector:= function( m, B, moves )
    
    # Here `m' is the exponent vector of a PBW monomial relative to 
    # the reduced word w1,
    # `moves' is a list of elementary moves, moving w1 to the word w2;
    # `B' is the matrix of the bilinear form.
    # We have that `m' is equivalent to a monomial expression relative
    # to w2, modulo q. This function calculates that monomial.
    
    local   exp,  move,  l,  store,  a,  b,  c,  min,  d,  max,  p1,  
            p2,  p3,  p4,  e,  f,  B2,  moves2,  exp2;
    
    exp:= ShallowCopy( m );
    for move in moves do

        if Length( move ) = 4 then
            
            # just interchange the corresponding exponents.
            
            l:= move[1];
            store:= exp[l+1];
            exp[l+1]:= exp[l];
            exp[l]:= store;
            
        elif Length( move ) = 6 then
            
            # here (a,b,c) - > ( b+c-min, min, a+b-min ), where
            # a,b,c are the three exponents, and min = Min( a, c ).
            
            l:= move[1];
            a:= exp[l]; b:= exp[l+1]; c:= exp[l+2];
            min:= Minimum( a, c );
            exp[l]:= b+c-min;
            exp[l+1]:= min;
            exp[l+2]:= a+b-min;
            
        elif Length( move ) = 8 then
            
            # This case is rather complicated. Roughly it works as 
            # follows. Suppose that F_1^a F_2^b F_3^c F_4^d is the 
            # PBW-monomial in the qea of type B2. Then we calculate
            # exponents p1,p2,p3,p4 belonging to an adapted string
            # corresponding to the word where we move to. Finally
            # we calculate the exponents of the PBW-monomial corresponding
            # to this adapted string.
            
            l:= move[1];
            a:= exp[l]; b:= exp[l+1]; c:= exp[l+2]; d:= exp[l+3];
            min:= Minimum( b, d );
            max:= Maximum( b, d );
            
            if B[ move[2] ][ move[2] ] = 2 then
                
                # i.e., the move is s_a s_b s_a s_b -> s_b s_a s_b s_a,
                # where b is short.
                
                p1:= Maximum( b, max+2*c-2*a );
                p2:= Maximum( b+c, a+b );
                p3:= Minimum( 2*c+d, min+2*a );
                p4:= Minimum( a, c );
                
                if p3 <= p2+p4 then
                    exp[l]:= p1;
                    exp[l+1]:= p4;
                    exp[l+2]:= p3-2*p4;
                    exp[l+3]:= p2-p3+2*p4;
                else
                    exp[l]:= p1;
                    exp[l+1]:= p3-p2;
                    exp[l+2]:= 2*p2-p3;
                    exp[l+3]:= p4;
                fi;
                
                else
                
                # i.e., the move is s_a s_b s_a s_b -> s_b s_a s_b s_a,
                # where b is long.
                
                p1:= Maximum( b, max+c-a );
                p2:= Maximum( a, c ) + 2*b;
                p3:= Minimum( c+d, a+min );
                p4:= Minimum( a, c );

                if p2+p4 <= 2*p3 then
                    exp[l]:= p1;
                    exp[l+1]:=2*p3-p2;
                    exp[l+2]:= p2-p3;
                    exp[l+3]:= p4;
                else
                    exp[l]:= p1;
                    exp[l+1]:= p4;
                    exp[l+2]:= p3-p4;
                    exp[l+3]:= p2+2*p4-2*p3;
                fi;
                
            fi;
            
        elif Length( move ) = 12 then
            
            # We are in the G2 case. We map to the case D4, and back.
            
            l:= move[1];
            a:= exp[l]; b:= exp[l+1]; c:= exp[l+2]; d:= exp[l+3];
            e:= exp[l+4]; f:= exp[l+5];
            B2:= [ [ 2, -1, 0, 0 ], [ -1, 2, -1, -1 ], [ 0, -1, 2, 0 ], 
                   [ 0, -1, 0, 2 ] ];
            
            if B[ move[2] ][ move[2] ] = 6 then
                
                # i.e., the move is s_a s_b ... -> s_b s_a ..
                # where b is long.
                
                moves2:= [ [ 6, 3, 7, 1 ], [ 7, 4, 8, 1 ], 
                           [ 8, 2, 9, 1, 10, 2 ], [ 6, 4, 7, 3 ], 
                           [ 4, 2, 5, 4, 6, 2 ], [ 6, 3, 7, 2, 8, 3 ], 
                           [ 5, 3, 6, 4 ], [ 8, 1, 9, 3 ], 
                           [ 9, 2, 10, 3, 11, 2 ], [ 3, 2, 4, 3, 5, 2 ], 
                           [ 5, 4, 6, 2, 7, 4 ], [ 7, 1, 8, 4 ], 
                           [ 1, 1, 2, 2, 3, 1 ], [ 3, 3, 4, 1 ], 
                           [ 4, 4, 5, 1 ], [ 5, 2, 6, 1, 7, 2 ], 
                           [ 7, 4, 8, 2, 9, 4 ], [ 6, 4, 7, 1 ], 
                           [ 4, 2, 5, 4, 6, 2 ], [ 2, 3, 3, 2, 4, 3 ], 
                           [ 9, 3, 10, 4 ], [ 6, 1, 7, 2, 8, 1 ], 
                           [ 5, 1, 6, 4 ], [ 4, 1, 5, 3 ], 
                           [ 10, 2, 11, 4, 12, 2 ], [ 4, 3, 5, 1 ], 
                           [ 5, 4, 6, 1 ], [ 6, 2, 7, 1, 8, 2 ], 
                           [ 8, 3, 9, 2, 10, 3 ], [ 7, 3, 8, 1 ], 
                           [ 4, 4, 5, 3 ], [ 5, 2, 6, 3, 7, 2 ], 
                           [ 7, 1, 8, 2, 9, 1 ], [ 3, 4, 4, 2, 5, 4 ], 
                           [ 5, 3, 6, 4 ], [ 6, 1, 7, 4 ], [ 5, 1, 6, 3 ] ];

                exp2:= [ a, b,b,b, c, d,d,d, e, f,f,f ];
                exp2:= QGPrivateFunctions.MoveExpVector( exp2, B2, moves2 );
                exp[l]:= exp2[1]; exp[l+1]:= exp2[4];
                exp[l+2]:= exp2[5]; exp[l+3]:= exp2[8];
                exp[l+4]:= exp2[9]; exp[l+5]:= exp2[12];
                
            else
                
                # i.e., the move is s_a s_b ... -> s_b s_a ..
                # where b is short.
                
                moves2:= [ [ 5, 3, 6, 1 ], [ 6, 4, 7, 1 ], 
                           [ 7, 2, 8, 1, 9, 2 ], [ 5, 4, 6, 3 ], 
                           [ 3, 2, 4, 4, 5, 2 ], [ 5, 3, 6, 2, 7, 3 ], 
                           [ 4, 3, 5, 4 ], [ 7, 1, 8, 3 ], 
                           [ 8, 2, 9, 3, 10, 2 ], [ 6, 1, 7, 2, 8, 1 ], 
                           [ 5, 1, 6, 4 ], [ 4, 1, 5, 3 ], 
                           [ 10, 4, 11, 2, 12, 4 ], [ 9, 4, 10, 3 ], 
                           [ 4, 3, 5, 1 ], [ 5, 4, 6, 1 ], 
                           [ 6, 2, 7, 1, 8, 2 ], [ 2, 2, 3, 3, 4, 2 ], 
                           [ 4, 4, 5, 2, 6, 4 ], [ 6, 1, 7, 4 ], 
                           [ 7, 2, 8, 4, 9, 2 ], [ 5, 1, 6, 2, 7, 1 ], 
                           [ 4, 1, 5, 4 ], [ 3, 1, 4, 3 ], 
                           [ 9, 3, 10, 2, 11, 3 ], [ 7, 4, 8, 1 ], 
                           [ 8, 3, 9, 1 ], [ 5, 2, 6, 4, 7, 2 ], 
                           [ 1, 2, 2, 1, 3, 2 ], [ 3, 3, 4, 2, 5, 3 ], 
                           [ 5, 4, 6, 3 ], [ 6, 2, 7, 3, 8, 2 ], 
                           [ 4, 4, 5, 2, 6, 4 ], [ 8, 1, 9, 2, 10, 1 ], 
                           [ 6, 3, 7, 4 ], [ 7, 1, 8, 4 ], [ 6, 1, 7, 3 ] ];
                
                exp2:= [ a,a,a, b, c,c,c, d, e,e,e, f ];
                exp2:= QGPrivateFunctions.MoveExpVector( exp2, B2, moves2 );
                exp[l]:= exp2[1]; exp[l+1]:= exp2[4];
                exp[l+2]:= exp2[5]; exp[l+3]:= exp2[8];
                exp[l+4]:= exp2[9]; exp[l+5]:= exp2[12];
            fi;
            
        fi;
    od;

    return exp;
    
end;
   
            
#############################################################################
##
#M   Falpha( <u>, <i> )
##
InstallMethod( Falpha, 
        "for an element of the negative part of a quea, and an int", true,
        [ IsQEAElement, IsInt ], 0,
    function( u, k )
    
    local   R,  w0,  v,  exp,  eu;
    
    R:= FamilyObj( u )!.rootSystem;
    
    w0:= LongestWeylWord( R );
    v:= LongWords( R )[k];
    
    # construct the exponent vector.
    exp:= [1..Length(w0)]*0;
    eu:= ExtRepOfObj( u )[1];
    for k in [1,3..Length(eu)-1] do
        
        if eu[k] > Length( w0 ) then
            Error( "<u> must be an element of the negative part of <U>" );
        fi;
        
        exp[ eu[k] ]:= eu[k+1];
    od;
    
    # Move it to an exponent vector relative to a reduced
    # expression of w0, starting with `k'.

    exp:= QGPrivateFunctions.MoveExpVector( exp, BilinearFormMatNF( R ), v[2] );
    
    # Increase first exponent by 1:
    exp[1]:= exp[1]+1;
    # Move back:
    exp:= QGPrivateFunctions.MoveExpVector( exp, BilinearFormMatNF( R ), v[3] );
    
    # Produce the PBW-monomial:
    eu:= [ ];
    for k in [1..Length(exp)] do
        if exp[k] <> 0 then
            Add( eu, k );
            Add( eu, exp[k] );
        fi;
    od;
    
    return ObjByExtRep( FamilyObj(u), [ eu, _q^0 ] );
end );


#############################################################################
##
#M   Ealpha( <u>, <i> )
##
InstallMethod( Ealpha, 
        "for an element of the negative part of a quea, and an int", true,
        [ IsQEAElement, IsInt ], 0,
    function( u, k )
    
    local   R,  w0,  v,  exp,  eu;
    
    R:= FamilyObj( u )!.rootSystem;
    
    w0:= LongestWeylWord( R );
    v:= LongWords( R )[k];
    
    # construct the exponent vector.
    exp:= [1..Length(w0)]*0;
    eu:= ExtRepOfObj( u )[1];
    for k in [1,3..Length(eu)-1] do
        
        if eu[k] > Length( w0 ) then
            Error( "<u> must be an element of the negative part of <U>" );
        fi;
        
        exp[ eu[k] ]:= eu[k+1];
    od;
    
    # Move it to an exponent vector relative to a reduced
    # expression of w0, starting with `k'.

    exp:= QGPrivateFunctions.MoveExpVector( exp, BilinearFormMatNF( R ), v[2] );
    
    # Decrease first exponent by 1:
    
    if exp[1] = 0 then 
        return fail;
    fi;
    
    exp[1]:= exp[1]-1;
    # Move back:
    exp:= QGPrivateFunctions.MoveExpVector( exp, BilinearFormMatNF( R ), v[3] );
    
    # Produce the PBW-monomial:
    eu:= [ ];
    for k in [1..Length(exp)] do
        if exp[k] <> 0 then
            Add( eu, k );
            Add( eu, exp[k] );
        fi;
    od;
    
    return ObjByExtRep( FamilyObj(u), [ eu, _q^0 ] );
end );


QGPrivateFunctions.Decompose:= function( V, i )
    
    # Decompose V under the sl_2 corresponding to the i-th simple root.
    # Returns a list of two lists [ vv, www ], where vv is a list of
    # two lists; namely bases of the direct summands of V (the k_th
    # element of such a list is $F^{(k)}\cdot v_0$, where $v_0$ is the first
    # element. Secondly `www' is a list of lists of weights, giving
    # the weight of each element of `vv'.

    local   R,  vv,  wt,  gg,  pos,  n,  rk,  f_i,  e_i,  wts,  vecs,  
            t,  b,  eqs,  v,  sol,  lst,  www,  qp,  wlist,  v1,  w1;
   
    R:= RootSystem( LeftActingAlgebra( V ) );
    vv:= WeightsAndVectors( V );
    wt:= SimpleRootsAsWeights( R )[i];   
    gg:= GeneratorsOfAlgebra( LeftActingAlgebra( V ) );
    pos:= Position( FamilyObj( gg[1] )!.convexRoots, SimpleSystemNF(R)[i] );
    n:= Length( PositiveRoots( R ) );
    rk:= Length( SimpleSystemNF( R ) );
    f_i:= gg[pos];
    e_i:= gg[ n+ 2*rk + pos ];
    
    # we first look for vectors w st E_i^w = 0...
    # we group them according to their weight
    # wts are the weights, vecs contains the corr vectors
    
    wts:= [ ]; vecs:= [ ];
    
    for t in [1..Length(vv[1])] do
        
        if vv[1][t][i] >= 0 then
            
            pos:= Position( vv[1], vv[1][t] + wt );
            
            if pos = fail then
                # all vectors v satisfy e_i^v = 0 
                Add( wts, vv[1][t] );
                Add( vecs, vv[2][t] );
            else
                
                # We solve equations.
                
                b:= Basis( VectorSpace( QuantumField, vv[2][pos] ), 
                           vv[2][pos] );
                eqs:= [ ];
                for v in vv[2][t] do
                    Add( eqs, Coefficients( b, e_i^v ) );
                od;
                
                sol:= NullspaceMat( eqs );
                if sol <> [] then
                    Add( wts, vv[1][t] );
                    lst:= [];
                    for v in sol do
                        Add( lst, v*vv[2][t] );
                    od;
                    Add( vecs, lst );
                fi;
            fi;
        fi;
    od;         
    
    # Now every vector in `vecs' generates a direct summand (as highest
    # weight vector).
    
    vv:= [];  www:= [ ];
    qp:= _q^( BilinearFormMatNF( R )[i][i]/2 );
    for t in [1..Length(vecs)] do
        for v in vecs[t] do
            lst:= [ ];
            wlist:= [ ];
            v1:= v;
            w1:= wts[t]; 
            n:= 0;
            while v1 <> 0*v1 do
                Add( lst, v1 );
                Add( wlist, w1 );         
                n:= n+1;
                v1:= f_i^v1/GaussNumber( n, qp );
                w1:= w1 - wt; 
            od;
            Add( vv, lst );
            Add( www, wlist );
        od;
    od;
    
    return [Basis( V, Flat(vv) ), vv,www];
    
end;


#############################################################################
##
#M   Falpha( <V>, <v>, <k> )
##
InstallOtherMethod( Falpha, 
        "for a module over a quea, an element of it, and an int", true,
        [ IsAlgebraModule, IsAlgebraModuleElement, IsInt ], 0,
        
    function( V, v, k )
    
    local   dd,  cf,  res,  i,  j,  dim,  r;
    
    # apply the k-th Kashiwara operator to the vector v;
    
    if not IsBound( V!.decompositions ) then
        
        V!.decompositions:= [ ];
        
    fi;

    if not IsBound( V!.decompositions[k] ) then
        V!.decompositions[k]:= QGPrivateFunctions.Decompose( 
                                                    V, k );
    fi;
    
    dd:= V!.decompositions[k];
    
    cf:= Coefficients( dd[1], v );
    
    # we construct the vector with the same coefficients as v, but
    # with vectors of weight "one bigger":
    
    res:= Zero( V );
    for i in [1..Length(cf)] do
        if cf[i] <> 0*cf[i] then
            # look for the component of the i-th basis vector:
            j:= 1;
            dim:= Length( dd[2][j] );
            while dim < i do
                j:= j+1;
                dim:= dim+Length( dd[2][j] );
            od;
            # r will be the position of the i-th basis vector in the j-th
            # component.
            r:= i - Sum( [1..j-1], ii -> Length( dd[2][ii] ) );
            if r < Length(dd[2][j]) then
                # i.e., the vector is not the last one in this component.
                res:= res + cf[i]*dd[2][j][r+1];
            fi;
        fi;
    od;
    return res;
    
end );


#############################################################################
##
#M   Ealpha( <V>, <v>, <k> )
##
InstallOtherMethod( Ealpha, 
        "for a module over a quea, an element of it, and an int", true,
        [ IsAlgebraModule, IsAlgebraModuleElement, IsInt ], 0,
        
    function( V, v, k )
    
    local   dd,  cf,  res,  i,  j,  dim,  r;
    
    # apply the k-th Kashiwara operator to the vector v;
    
    if not IsBound( V!.decompositions ) then
        
        V!.decompositions:= [ ];
        
    fi;
    
    if not IsBound( V!.decompositions[k] ) then
        V!.decompositions[k]:= QGPrivateFunctions.Decompose( 
                                       V, k );
    fi;
    
    dd:= V!.decompositions[k];
    
    cf:= Coefficients( dd[1], v );
    
    # we construct the vector with the same coefficients as v, but
    # with vectors of weight "one smaller":
    
    res:= Zero( V );
    for i in [1..Length(cf)] do
        if cf[i] <> 0*cf[i] then
            # look for the component of the i-th basis vector:
            j:= 1;
            dim:= Length( dd[2][j] );
            while dim < i do
                j:= j+1;
                dim:= dim+Length( dd[2][j] );
            od;
            # r will be the position of the i-th basis vector in the j-th
            # component.
            r:= i - Sum( [1..j-1], ii -> Length( dd[2][ii] ) );
            if r > 1 then
                # i.e., the vector is not the first one in this component.
                res:= res + cf[i]*dd[2][j][r-1];
            fi;
        fi;
    od;
    return res;
    
end );


##############################################################################
##
#M  CrystalBasis( <V> )
##
##
InstallMethod( CrystalBasis,
        "for a f.d module over a quea", true,
        [IsAlgebraModule], 0,
        function( V )
    
    local   lexord,  lex,  U,  R,  w0,  lenw0,  rts,  pos,  www,  
            cbas,  w,  hw,  cg,  paths,  strings,  p,  b,  st,  i,  j,  
            a,  hvec,  paths1,  strings1,  celms,  len,  mons,  ww,  
            vv,  s,  u,  k,  mn,  cf,  c,  val,  ccc,  pol,  pp,  
            celms1;
    
    lexord:= function( s1, s2 )
    
        # lex ordering for adapted strings:
        # [2,0,3,0,1] < [2,0,4,0,1] etc.
        
        local   k;
    
        for k in [1..Length(s1)] do
            if s1[k] <> s2[k] then
                return s1[k] < s2[k];
            fi;
        od;
        # they are equal...
        return false;
    end;
    
    lex:= function( m1, m2 )
    
        # lex for monomials of the form [1,2,2,3,3,2]=x_1^2x_2^3x_3^2
        # x_1^2x_2^3 < x_1x_2^3 etc.
        
        local   len1,  len2,  min,  i;
    
        len1:= Length(m1); len2:= Length(m2);
        min:= Minimum( len1, len2 );
        
        for i in [1,3..min-1] do
            if m1[i] <> m2[i] then
                return m1[i] < m2[i];
            elif m1[i+1] <> m2[i+1] then
                return m1[i+1] > m2[i+1];
            fi;
        od;
        
        return len1 < len2;
    end;
    
    
    U:= LeftActingAlgebra( V );
    R:= RootSystem( U );
    w0:= LongestWeylWord( R );
    lenw0:= Length( w0 );
    
    rts:= PositiveRootsInConvexOrder( R );
    pos:= List( SimpleSystemNF( R ), x -> Position( rts, x ) );
    
    www:= HighestWeightsAndVectors( V );
    
    # `cbas' will be a list of canonical basis elements spanning
    # L(\lambda) over Z[q]. The algorithm is a module version of 
    # the algorithm for calculating canonical basis elements in the
    # negative part of a quantized uea.
   
    cbas:= [ ];
    
    for w in [1..Length(www[1])] do
        
        hw:= www[1][w];
        cg:= CrystalGraph( R, hw );
        paths:= cg.points;
    
        # For every path we compute its adapted string.
    
        strings:= [ ];
    
        for p in paths do
            b:= p;
            st:= ShallowCopy( w0*0 );
            for i in [1..lenw0] do
                j:= 0;
                while b <> fail do
                    a:= b;
                    b:= Ealpha( b, w0[i] );
                    j:= j+1;
                od;
                j:= j-1;
                b:= a;
                st[i]:= j; 
            od;
            Add( strings, st );
            
        od;

        for hvec in www[2][w] do
            
            paths1:= ShallowCopy( paths );
            strings1:= ShallowCopy( strings );
            while paths1 <> [ ] do
        
                celms:= [ ];
                len:= 0;
        
                # `celms' will be a list of lists of length two;
                # let l be such a list, then l[1] is an element of the crystal
                # basis, and l[2] is the index of its principal vector, i.e., 
                # index as element of `vv' (to be constructed).
                # `len' is the length of `celms'.
        
                # We take all paths of the same weight as the first path 
                # together, and erase them from the list.
        
                p:= paths1[1];
                st:= [ strings1[1] ];
                Unbind( paths1[1] );
                Unbind( strings1[1] );
                for i in [2..Length(paths1)] do
                    if EndWeight( paths1[i] ) = EndWeight( p ) then
                        Add( st, strings1[i] );
                        Unbind( paths1[i] );
                        Unbind( strings1[i] );
                    fi;
                od;
        
                paths1:= Filtered( paths1, x -> IsBound(x) );
                strings1:= Filtered( strings1, x -> IsBound(x) );
        
                # Sort according to lexicographical order.
        
                Sort( st, function(x,y) return lexord(y,x); end );
        
                # `mons' will contain the PBW-monomials corresponding to the
                # strings in `st';
                # `vv' is the list of m^v0, where m is from `mons';
                # the elements from `vv' span the lattice L(\lambda) over Z[q];
                # `ww' is the list `m^v0', where `m' is the monomial in 
                # the generators corresponding to a string.
        
                mons:= [ ]; ww:=[ ]; vv:= [ ];
                for s in st do
                    u:= One( U );
                    for i in [lenw0,lenw0-1..1] do
                        for k in [1..s[i]] do
                            u:= Falpha( u, w0[i] );
                        od;
                    od;
                    Add( mons, u );
                    
                    Add( vv, u^hvec );
                    
                    mn:= [ ];
                    for i in [1..lenw0] do
                        if s[i] <> 0 then
                            Add( mn, pos[ w0[i] ] );
                            Add( mn, s[i] );
                        fi;
                    od;
                    mn:= ObjByExtRep( FamilyObj(u), [ mn, _q^0 ] );
                    Add( ww, mn^hvec );
                od;
                
                b:= Basis( VectorSpace( QuantumField, vv ), vv );
                
                for i in [1..Length(ww)] do
                    
                    # We write ww[i] as a linear combination of elements 
                    # from `vv'. If the coefficients are all elements from 
                    # qZ[q], then we are happy: then the element is 
                    # bar-invariant, and it lies in L(\lambda). If not, we 
                    # use the previous canonical elements to repair the 
                    # situation.
                    
                    w:= ww[i];
                    cf:= Coefficients( b, w );
                    
                    for j in [len,len-1..1] do
                        c:= CoefficientsOfUnivariateLaurentPolynomial( 
                                    cf[ celms[j][2] ] );
                        
                    # if this has non-positive powers of q, then we repair this
                    # situation by adding a bar-invariant multiple of the 
                    # appropriate canonical element.
                        
                        if c[2] <= 0 then
                            val:= c[2];
                            k:= 1;
                            ccc:= [ ];
                            while k <= -val+1 and k <= Length(c[1]) do
                                ccc[k]:= c[1][k];
                                ccc[-2*val+2-k]:= c[1][k];
                                k:= k+1;
                            od;
                            
                            pol:= LaurentPolynomialByCoefficients( 
                                          FamilyObj(1), ccc, val,
                                          QGPrivateFunctions.indetNo );
                            w:= w-pol*celms[j][1];
                            cf:= Coefficients( b, w );
                        fi;
                    od;
                    
                    # look for correct position
                    # lexicographic ordering of principal monomials
                    pp:= fail;
                    j:= len;
                    
                    while pp = fail and j > 0 do
                        if lex( mons[ celms[j][2] ]![1][1], 
                                mons[i]![1][1] ) then
                            pp:= j+1;
                        else
                            j:= j-1;
                        fi;
                    od;
                    
                    if pp = fail then
                        pp:= 1;
                    fi;
                    
                    # Insert on the correct position:
                    celms1:= celms{[1..pp-1]};
                    Add( celms1, [ w, i ] );
                    Append( celms1, celms{[pp..len]} );
                    celms:= celms1;
                    len:= len+1;
                od;
                
                Append( cbas, List( celms, x -> x[1] ) );
            od; 
        od;
    od;
    
    return BasisNC( V, cbas );
    
end );

##############################################################################
##
#M  PrintObj( <c> )
##
##
InstallMethod( PrintObj,
        "for a crystal vector", true,
        [IsCrystalVector], 0,
        function( c )
    
    Print("<",c!.vector,">");
end);

InstallMethod( \=,
        "for two crystal vectors",
        IsIdenticalObj, [ IsCrystalVector, IsCrystalVector ], 0,
        function( c1, c2 )
    
    return c1!.vector = c2!.vector;
end );


##############################################################################
##
#M  CrystalVectors( <V> )
##
##
InstallMethod( CrystalVectors,
        "for a f.d module over a quea", true,
        [IsAlgebraModule], 0,
        function( V )
    
    local   U,  R,  w0,  lenw0,  rts,  pos,  ctype,  www,  vecs,  a,  
            hw,  cg,  paths,  mons,  p,  b,  st,  i,  j,  u,  k,  
            hvec,  r,  w;
    
    U:= LeftActingAlgebra( V );
    R:= RootSystem( U );
    w0:= LongestWeylWord( R );
    lenw0:= Length( w0 );
    
    rts:= PositiveRootsInConvexOrder( R );
    pos:= List( SimpleSystemNF( R ), x -> Position( rts, x ) );
    
    ctype:=  NewType( NewFamily( "CrystalEltsFam", IsCrystalVector ),
                     IsCrystalVector and 
                     IsComponentObjectRep and 
                     IsAttributeStoringRep );
    
    www:= HighestWeightsAndVectors( V );
    
    vecs:= [ ];
    
    for w in [1..Length(www[1])] do
        
        hw:= www[1][w];
        cg:= CrystalGraph( R, hw );
        paths:= cg.points;
        mons:= [ ];
        # For every path we compute its adapted string.
        # For every adapted string we calculate the corresponding
        # PBW-monomial.
        for p in paths do
            b:= p;
            st:= ShallowCopy( w0*0 );
            for i in [1..lenw0] do
                j:= 0;
                while b <> fail do
                    a:= b;
                    b:= Ealpha( b, w0[i] );
                    j:= j+1;
                od;
                j:= j-1;
                b:= a;
                st[i]:= j; 
            od;
        
            u:= One( U );
            for i in [lenw0,lenw0-1..1] do
                for k in [1..st[i]] do
                    u:= Falpha( u, w0[i] );
                od;
            od;
            Add( mons, u );
        od;
        
        for hvec in [1..Length(www[2][w])] do
    
            # We apply all monomials to the hw vector;
            # the index and hwt components are there to distinguish 
            # vectors with the same monomial, coming from different
            # hw vectors.
    
            for u in mons do
                r:= rec( vector:= u^www[2][w][hvec], module:= V, 
                         index:= hvec, hwt:= www[1][w] );
                ObjectifyWithAttributes( r, ctype, PBWMonomial, u );        
                Add( vecs, r );
            od;        
        od;
    od;
        
    return vecs;
end );


#############################################################################
##
#M   Falpha( <c>, <i> )
##
InstallMethod( Falpha, 
        "for a crystal vector, and an int", true,
        [ IsCrystalVector, IsInt ], 0,
        function( v, k )
    
    local   m,  pos;
    
    m:= Falpha( PBWMonomial( v ), k );
    pos:= PositionProperty( CrystalVectors( v!.module ), 
                  x -> PBWMonomial(x) = m and x!.index = v!.index and
                  x!.hwt = v!.hwt );
    if pos = fail then 
        return fail;
    else
        return CrystalVectors( v!.module )[pos];
    fi;
end);

#############################################################################
##
#M   Ealpha( <c>, <i> )
##
InstallMethod( Ealpha, 
        "for a crystal vector, and an int", true,
        [ IsCrystalVector, IsInt ], 0,
        function( v, k )
       
    local   m,  pos;
    
    m:= Ealpha( PBWMonomial( v ), k );
    
    if m = fail then return fail; fi;
    
    pos:= PositionProperty( CrystalVectors( v!.module ), 
                  x -> PBWMonomial(x) = m and x!.index = v!.index and
                  x!.hwt = v!.hwt );
    if pos = fail then 
        return fail;
    else
        return CrystalVectors( v!.module )[pos];
    fi;
end);


QGPrivateFunctions.crystal_graph:= function( V )
    
    local   rank,  points,  edges,  i,  pt,  j,  c;
    
    if IsBound( FamilyObj(V)!.crystalGraph ) then
        return FamilyObj(V)!.crystalGraph;
    fi;
    
    rank:= Length( CartanMatrix( RootSystem( LeftActingAlgebra(V) ) ) );
    points:= CrystalVectors( V );
    edges:= [ ];
    for i in [1..Length(points)] do
        
        pt:= points[i];
        for j in [1..rank] do
            c:= Falpha( pt, j );
            if c <> fail then
                Add( edges, [ [ i, Position( points, c ) ], j ] );
            fi;
        od;
    od;
    FamilyObj(V)!.crystalGraph:= rec( points:= points, edges:= edges );
    return FamilyObj(V)!.crystalGraph;
end;

            
#############################################################################
##
#M   PrincipalMonomial( <p> )
##
InstallMethod( PrincipalMonomial, 
        "for a an element of the canonical basis", true,
        [ IsQEAElement ], 0,
        function( p )
    
    local   ep,  pos;
    
    ep:= ExtRepOfObj( p );
    pos:= PositionProperty( ep, x -> not IsList(x) and IsOne(x) );
    return ObjByExtRep( FamilyObj(p), [ ep[pos-1], ep[pos] ] );
end );


#############################################################################
##
#M   StringMonomial( <m> )
##
InstallMethod( StringMonomial, 
        "for a monomial in the minus part of a quea", true,
        [ IsQEAElement ], 0,
        function( m )
    
    local   R,  w0,  string,  k,  i,  n,  m1;
    
    R:= FamilyObj(m)!.rootSystem;
    w0:= LongestWeylWord( R );
    string:= [ ];
    for k in [1..Length(w0)] do
        if IsOne( m ) then break; fi;
        i:= w0[k];
        n:= 0;
        m1:= Ealpha( m, i );
        while m1 <> fail do
            n:= n+1;
            m:= m1;
            m1:= Ealpha( m, i );
        od;
        if n > 0 then
            Add( string, i ); Add( string, n );
        fi;
    od;
    return string;
    
end );


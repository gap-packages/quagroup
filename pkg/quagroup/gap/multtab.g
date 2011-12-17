############################################################################
##
#W  multtab.g                  QuaGroup                      Willem de Graaf
##
##
##  This file contains the basic code for computing the multiplication table 
##  of (PBW-type basis of) a quantized enveloping algebra.
##
##  This file roughly consists of three parts:
## 
##       * code for moving a w-expression into a u-expression,
##       * code for getting comm rels between two E's and between two F's,
##       * code for getting comm rels between an F and an E
##
##  Throughout we use two assumptions on the root system:
##
##       1) all roots are written as linear combinations of the simple roots
##          (i.e., all simple roots are unit vectors),
##       2) the squared root lengths are 2,4,6.
##


##############################################################################
##
##  Part one
##
##  Let w be a reduced word in the Weyl group and write w=s1s2..st.
##  Set Ek = T1..T{k-1}(E{k}) for k=1..t. Then any polynomial expression
##  in the Ek is called a w-expression. It is said to be in normal form 
##  if all monomials are of the form E{i1}...E{ir} with i1<i2<...<ir.
##  Let u be a reduced word in the Weyl group representing the same element
##  of the Weyl group as w. Let p be a w-expression in normal form. Then
##  p is equal to a u-expression in normal form. This first part contains 
##  code for finding this u-expression, given p, w, u. We reduce to the rank
##  2 case, where u is constructed from w by one elementary move. 
##  Furthermore, we assume that there is no component of type G2. 
##  The rewriting in the rank 2 cases is handled by the functions
##  `A2_rewrite', `B2_rewrite_1', `B2_rewrite_2'. The rewriting of an
##  expression "relative" to only one elementary move is handled by
##  `EltMove'. Finally everything is put together in `MoveIt'.
##


QGPrivateFunctions.A2_rewrite:= function( expr, qa )
    
    # Let a and b be two roots spanning a root system of type A2, set
    # X1 = Ea, X2 = Ta(Eb), X3 = Eb, Y1 = Eb, Y2 = Tb(Ea), Y3=Ea. 
    # This functions rewrites an expression in the Xi to an expression in 
    # the Yi. Here expr is of the form [ [i1, e1, ...], cf, [... etc ]... ], 
    # where the indices ik are 1,2,3 (indicating whether it is X1,X2,X3). 
    
    local   todo,  i,  mns,  j,  k,  b,  mns1,  mns2,  l,  m,  res,  
            cf,  found,  mon,  s,  ex,  pos,  st,  start;
    
    # `todo' will contain the `expr' with the Yi substituted for the
    # Xi. We use the following substitutions:
    #
    #  X1 = Y3, X3 = Y1,
    #  X2 = (qa-qa^-1)Y1Y3-qaY2
    #
    # Also we "stretch" the monomials, i.e., [1,3,2,2] will be represented
    # as [ 1, 1, 1, 2, 2 ]. 
    

    todo:= [ ];
    for i in [1,3..Length(expr)-1] do
        mns:= [ [], expr[i+1]];
        for j in [1,3..Length(expr[i])-1] do
            if expr[i][j] = 1 then
                
                for k in [ 1,3..Length(mns)-1] do
                    Append( mns[k], List( [1..expr[i][j+1]], x -> 3 ) );
                od;
                
            elif expr[i][j] = 2 then
                b:= expr[i][j+1];
                mns1:= [ [1,3], qa-qa^-1, [2], -qa ];
                for k in [1..b-1] do
                    mns2:= [ ];
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [ 1,3] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(qa-qa^-1) );
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [2] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(-qa) );
                    od;
                    mns1:= mns2;
                od;
                
                mns2:= [ ];
                for k in [1,3..Length(mns)-1] do
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns[k] );
                        Append( m, mns1[l] );
                        Add( mns2, m ); Add( mns2, mns[k+1]*mns1[l+1] );
                    od;
                od;
                mns:= mns2;

            elif expr[i][j] = 3 then
                
                for k in [ 1,3..Length(mns)-1] do
                    Append( mns[k], List( [1..expr[i][j+1]], x -> 1 ) );
                od;

            fi;
        od;
        Append( todo, mns );
    od;
    
    # Now we "straighten" the elements of `todo'. We use the following 
    # relations:
    #
    #  Y2Y1 = qa^(-1)Y1Y2
    #  Y3Y1 = qaY1Y3 - qaY2
    #  Y3Y2 = qa^(-1)Y2Y3
    #
    # `res' will contain the result (in normal form).
    

    res:= [ ];
    while todo <> [] do

        m:= todo[1];
        cf:= todo[2];
            
        found:= false;
        for i in [1..Length(m)-1] do
            if m[i] > m[i+1] then
                found:= true;
                break;
            fi;
        od;
        if not found then
            
            # The monomial `m' is in normal form; we add it to `res'.
            # First we transform it in to varno, exp form (i.e., [1,1,1,2,2]
            # will become [1,3,2,2]). 
            
            mon:= [ ];
            s:= 1;
            while s <= Length( m ) do
                ex:= 1;
                while s < Length(m) and m[s+1] = m[s] do
                    s:= s+1;
                    ex:= ex+1;
                od;
                Add( mon, m[s] );
                Add( mon, ex );
                s:= s+1;
            od;

            pos:= Position( res, mon );
            if pos <> fail then
                res[pos+1]:= res[pos+1]+cf;
                if res[pos+1] = 0*cf then
                    Unbind( res[pos] ); Unbind( res[pos+1] );
                    res:= Filtered( res, x -> IsBound(x) );
                fi;
            else    
                Add( res, mon );
                Add( res, cf );
            fi;

            Unbind( todo[1] );
            Unbind( todo[2] );
            todo:= Filtered( todo, x -> IsBound(x) );
        else
            
            # we apply a commutation relation.
            
            st:= m[i];
            m[i]:= m[i+1]; m[i+1]:= st;
            todo[1]:= m; 
            
            # note: now the order in m has changed so we test on this 
            # changed order.
            
            if [ m[i+1], m[i] ] = [ 2, 1 ] then
                
                todo[2]:= todo[2]*qa^-1;
                
            elif [ m[i+1], m[i] ] = [ 3, 2 ] then
                
                todo[2]:= todo[2]*qa^-1;
                
            else
                todo[2]:= todo[2]*qa;
                start:= m{[1..i-1]};
                Add( start, 2 );
                Append( start, m{[i+2..Length(m)]} );
                Add( todo, start ); Add( todo, cf*(-qa) );
            fi;
            
            
        fi;
    od;
    
    return res;        
    
end;


QGPrivateFunctions.B2_rewrite_1:= function( expr )
    

    # Let a,b be two roots spanning a root system of type B2, where b is a
    # long root. Set X1 = Ea, X2 = Ta(Eb), X3 = TaTb(Ea), X4 = TaTbTa(Eb)=Eb, 
    # and Y1 = Eb, Y2 = Tb(Ea), Y3 = TbTa(Eb), Y4 = TbTaTb(Ea). 
    # Here `expr' is an expression on the Xi, which we transform into an
    # expression in the Yi (in normal form).
    
    local   todo,  i,  mns,  j,  k,  b,  mns1,  mns2,  l,  m,  res,  
            cf,  found,  mon,  s,  ex,  pos,  st,  start;
        
    if expr = [] then return []; fi;
    
    # First we substitute expressions with Yi's for Xi's. We use the following 
    # substitutions:
    #
    #   X1 = Y4, X4 = Y1,
    #   X2 = q^2Y3 - (q^3-q)Y2Y4+(q^3-2q+q^-1)Y1Y4^2
    #   X3 = -q^2Y2 + (q^2-q^-2)Y1Y4
    #
    # `todo' will contain the result, in streched form 
    # (e.g., [1,1,1,2,2] instead of [1,3,2,2]).

    todo:= [ ];
    for i in [1,3..Length(expr)-1] do
        mns:= [[],expr[i+1]];
        for j in [1,3..Length(expr[i])-1] do
            if expr[i][j] = 1 then
                
                for k in [1,3..Length(mns)-1] do
                    Append( mns[k], List( [1..expr[i][j+1]], x -> 4 ) );
                od;
                
            elif expr[i][j] = 2 then
                b:= expr[i][j+1];
                mns1:= [ [3], _q^2, [2,4], -(_q^3-_q), [1,4,4], _q^3-2*_q+_q^-1 ];
                for k in [1..b-1] do
                    mns2:= [ ];
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [3] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(_q^2) );
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [2,4] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(-(_q^3-_q)) );
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [1,4,4] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(_q^3-2*_q+_q^-1) );
                    od;
                    mns1:= mns2;
                od;
                
                mns2:= [ ];
                for k in [1,3..Length(mns)-1] do
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns[k] );
                        Append( m, mns1[l] );
                        Add( mns2, m ); Add( mns2, mns[k+1]*mns1[l+1] );
                    od;
                od;
                mns:= mns2;
                
            elif expr[i][j] = 3 then
                
                b:= expr[i][j+1];
                mns1:= [ [2], -_q^2, [1,4], _q^2-_q^-2 ];
                for k in [1..b-1] do
                    mns2:= [ ];
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [2] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(-_q^2) );
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [1,4] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(_q^2-_q^-2) );
                    od;
                    mns1:= mns2;
                od;
                
                mns2:= [ ];
                for k in [1,3..Length(mns)-1] do
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns[k] );
                        Append( m, mns1[l] );
                        Add( mns2, m ); Add( mns2, mns[k+1]*mns1[l+1] );
                    od;
                od;
                mns:= mns2;
                
            elif expr[i][j] = 4 then
                
                for k in [1,3..Length(mns)-1] do
                    Append( mns[k], List( [1..expr[i][j+1]], x -> 1 ) );
                od;

            fi;
        od;
        Append( todo, mns );
    od;
    
    # Now we "straighten" the elements of `todo' using the following 
    # commutation relations:
    #
    #  Y2Y1 = q^(-2)Y1Y2
    #  Y3Y1 = Y1Y3 - (q^2-1)/(q+q^-1)Y2^2
    #  Y4Y1 = q^2Y1Y4 -q^2Y2
    #  Y3Y2 = q^(-2)Y2Y3 
    #  Y4Y2 = Y2Y4 - (q+q^-1)Y3
    #  Y4Y3 = q^(-2)Y3Y4

    res:= [ ];
    while todo <> [] do

        m:= todo[1];
        cf:= todo[2];
            
        found:= false;
        for i in [1..Length(m)-1] do
            if m[i] > m[i+1] then
                found:= true;
                break;
            fi;
        od;
        if not found then
            
            # The monomial `m' is in normal form; we add it to `res'.
            # First we transform it in to varno, exp form (i.e., [1,1,1,2,2]
            # will become [1,3,2,2]). 
            
            mon:= [ ];
            s:= 1;
            while s <= Length( m ) do
                ex:= 1;
                while s < Length(m) and m[s+1] = m[s] do
                    s:= s+1;
                    ex:= ex+1;
                od;
                Add( mon, m[s] );
                Add( mon, ex );
                s:= s+1;
            od;

            pos:= Position( res, mon );
            if pos <> fail then
                res[pos+1]:= res[pos+1]+cf;
                if res[pos+1] = 0*cf then
                    Unbind( res[pos] ); Unbind( res[pos+1] );
                    res:= Filtered( res, x -> IsBound(x) );
                fi;
            else    
                Add( res, mon );
                Add( res, cf );
            fi;

            Unbind( todo[1] );
            Unbind( todo[2] );
            todo:= Filtered( todo, x -> IsBound(x) );
        else
            
            # We apply a commutation relation.
            
            st:= m[i];
            m[i]:= m[i+1]; m[i+1]:= st;
            todo[1]:= m; 
            
            # Note: now the order in m has changed so we test on this 
            # changed order.
            
            if [ m[i+1], m[i] ] = [ 2, 1 ] then
                
                todo[2]:= todo[2]*_q^-2;
                
            elif [ m[i+1], m[i] ] = [ 3, 1 ] then
                
                start:= m{[1..i-1]};
                Append( start, [2,2] );
                Append( start, m{[i+2..Length(m)]} );
                Add( todo, start ); Add( todo, cf*(-(_q^2-1)/(_q+_q^-1)) );
                
            elif [ m[i+1], m[i] ] = [ 4, 1 ] then
                
                todo[2]:= todo[2]*_q^2;
                start:= m{[1..i-1]};
                Add( start, 2 );
                Append( start, m{[i+2..Length(m)]} );
                Add( todo, start ); Add( todo, cf*(-_q^2) );
                
            elif [ m[i+1], m[i] ] = [ 3, 2 ] then
                
                todo[2]:= todo[2]*_q^-2;
                
            elif [ m[i+1], m[i] ] = [ 4, 2 ] then
                
                start:= m{[1..i-1]};
                Add( start, 3 );
                Append( start, m{[i+2..Length(m)]} );
                Add( todo, start ); Add( todo, cf*(-(_q+_q^-1)) );
                
            else
                
                todo[2]:= todo[2]*_q^-2;
                
            fi;
            
        fi;
    od;
    
    return res;        
    
end;


QGPrivateFunctions.B2_rewrite_2:= function( expr )
    
    # Let a,b be two roots spanning a root system of type B2, where b is a
    # long root. Set X1 = Ea, X2 = Ta(Eb), X3 = TaTb(Ea), X4 = TaTbTa(Eb)=Eb, 
    # and Y1 = Eb, Y2 = Tb(Ea), Y3 = TbTa(Eb), Y4 = TbTaTb(Ea). 
    # Here `expr' is an expression on the Yi, which we transform into an
    # expression in the Xi (in normal form).
    
    local   todo,  i,  mns,  j,  k,  b,  mns1,  mns2,  l,  m,  res,  
            cf,  found,  mon,  s,  ex,  pos,  st,  start;    
        
    if expr = [] then return []; fi;
    
    # First we substitute expressions with Xi's for Yi's. We use the following 
    # substitutions:
    #
    #   Y1 = X4, Y4 = X1,
    #   Y2 = -q^2X3 + (q^2-q^-2)X1X4
    #   Y3 = q^2X2 - (q^3-q)X1X3 + (q^3-2q+q^-1)X1^2X4
    #
    # `todo' will contain the result, in streched form 
    # (e.g., [1,1,1,2,2] instead of [1,3,2,2]).

    todo:= [ ];
    for i in [1,3..Length(expr)-1] do
        mns:= [[],expr[i+1]];
        for j in [1,3..Length(expr[i])-1] do
            if expr[i][j] = 1 then
                
                for k in [1,3..Length(mns)-1] do
                    Append( mns[k], List( [1..expr[i][j+1]], x -> 4 ) );
                od;
                
            elif expr[i][j] = 3 then
                b:= expr[i][j+1];
                mns1:= [ [2], _q^2, [1,3], -(_q^3-_q), [1,1,4], _q^3-2*_q+_q^-1 ];
                for k in [1..b-1] do
                    mns2:= [ ];
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [2] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(_q^2) );
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [1,3] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(-(_q^3-_q)) );
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [1,1,4] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(_q^3-2*_q+_q^-1) );
                    od;
                    mns1:= mns2;
                od;
                
                mns2:= [ ];
                for k in [1,3..Length(mns)-1] do
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns[k] );
                        Append( m, mns1[l] );
                        Add( mns2, m ); Add( mns2, mns[k+1]*mns1[l+1] );
                    od;
                od;
                mns:= mns2;
                
            elif expr[i][j] = 2 then
                
                b:= expr[i][j+1];
                mns1:= [ [3], -_q^2, [1,4], _q^2-_q^-2 ];
                for k in [1..b-1] do
                    mns2:= [ ];
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [3] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(-_q^2) );
                        m:= ShallowCopy( mns1[l] );
                        Append( m, [1,4] );
                        Add( mns2, m ); Add( mns2, mns1[l+1]*(_q^2-_q^-2) );
                    od;
                    mns1:= mns2;
                od;
                
                mns2:= [ ];
                for k in [1,3..Length(mns)-1] do
                    for l in [1,3..Length(mns1)-1] do
                        m:= ShallowCopy( mns[k] );
                        Append( m, mns1[l] );
                        Add( mns2, m ); Add( mns2, mns[k+1]*mns1[l+1] );
                    od;
                od;
                mns:= mns2;
                
            elif expr[i][j] = 4 then
                
                for k in [1,3..Length(mns)-1] do
                    Append( mns[k], List( [1..expr[i][j+1]], x -> 1 ) );
                od;

            fi;
        od;
        Append( todo, mns );
    od;

    # Now we "straighten" the elements of `todo'. We use the following 
    # commutation relations:
    #
    #   X2X1 = q^(-2)X1X2
    #   X3X1 = X1X3 - (q+q^-1)X2
    #   X4X1 = q^2X1X4 - q^2X3
    #   X3X2 = q^(-2)X2X3
    #   X4X2 = X2X4 - (q^2-1)/(q+q^-1)X3^2
    #   X4X3 = q^(-2)X3X4
    
    res:= [ ];
    while todo <> [] do

        m:= todo[1];
        cf:= todo[2];
            
        found:= false;
        for i in [1..Length(m)-1] do
            if m[i] > m[i+1] then
                found:= true;
                break;
            fi;
        od;
        if not found then
            
            # The monomial `m' is in normal form; we add it to `res'.
            # First we transform it in to varno, exp form (i.e., [1,1,1,2,2]
            # will become [1,3,2,2]).
            
            mon:= [ ];
            s:= 1;
            while s <= Length( m ) do
                ex:= 1;
                while s < Length(m) and m[s+1] = m[s] do
                    s:= s+1;
                    ex:= ex+1;
                od;
                Add( mon, m[s] );
                Add( mon, ex );
                s:= s+1;
            od;

            pos:= Position( res, mon );
            if pos <> fail then
                res[pos+1]:= res[pos+1]+cf;
                if res[pos+1] = 0*cf then
                    Unbind( res[pos] ); Unbind( res[pos+1] );
                    res:= Filtered( res, x -> IsBound(x) );
                fi;
            else    
                Add( res, mon );
                Add( res, cf );
            fi;

            Unbind( todo[1] );
            Unbind( todo[2] );
            todo:= Filtered( todo, x -> IsBound(x) );
        else
            
            st:= m[i];
            m[i]:= m[i+1]; m[i+1]:= st;
            todo[1]:= m; 
            # note: now the order in m has changed so we test on this 
            # changed order..
            
            if [ m[i+1], m[i] ] = [ 2, 1 ] then
                
                todo[2]:= todo[2]*_q^-2;
                
            elif [ m[i+1], m[i] ] = [ 3, 1 ] then
                
                start:= m{[1..i-1]};
                Add( start, 2 );
                Append( start, m{[i+2..Length(m)]} );
                Add( todo, start ); Add( todo, cf*(-(_q+_q^-1)) );
                
            elif [ m[i+1], m[i] ] = [ 4, 1 ] then
                
                todo[2]:= todo[2]*_q^2;
                start:= m{[1..i-1]};
                Add( start, 3 );
                Append( start, m{[i+2..Length(m)]} );
                Add( todo, start ); Add( todo, cf*(-_q^2) );
                
            elif [ m[i+1], m[i] ] = [ 3, 2 ] then
                
                todo[2]:= todo[2]*_q^-2;
                
            elif [ m[i+1], m[i] ] = [ 4, 2 ] then
                
                start:= m{[1..i-1]};
                Append( start, [3,3] );
                Append( start, m{[i+2..Length(m)]} );
                Add( todo, start ); Add( todo, cf*(-(_q^2-1)/(_q+_q^-1)) );
                
            else
                
                todo[2]:= todo[2]*_q^-2;
                
            fi;
            
        fi;
    od;
    
    return res;        
    
end;

QGPrivateFunctions.EltMove:= function( w1, w2, move, expr, Bil )

    # Here w1, w2 are two Weyl words, move is an elementary move 
    # moving w1 into w2. `move' is a list of the form 
    # [ p1, im1, p2, im2, ...] which means that after the move, 
    # on position p1, there will be im1 etc.
    # So moves can be of lengths 4, 6, 8, 12. The last case only occurs 
    # if there is a componenet of type G2, which is excluded here (for these 
    # components commutation relations are found directly). 
    # `expr' is a w1-expression.
    # the output will be a w2-expression, which is equal to `expr'.
    # Bil is the matrix of the bilinear form.

    # An example in the case of a A1+A1 (should also clarify the rest).
    # Suppose that w1 = x(s_a)(s_b)y, and w2 = x(s_b)(s_a)y, where
    # s_a, s_b commute. The move maps their product to (s_b)(s_a), so the 
    # move reads [ s+1, b', s+2, a' ] (where a', b' denote the index in 
    # the list of simple roots).  This means that
    # the sub-monomial T_{x}(E_a)^m T_{xs_a}(E_b)^n is mapped to
    # T_{x}(E_b)^n T_{xs_b}(E_a)^m. Now the index of T_{x}(E_a) is
    # s+1, i.e., the `k' below. So we interchange the exponents of the
    # elements with indices k, k+1.
    

    local   k,  res,  i,  mon,  j,  store,  a2,  b2,  set,  up,  qa,  
            k1,  k2,  start,  tail,  mn,  mon1,  l,  pos;
    
    k:= move[1]-1;
    if Length( move ) = 4 then
        
        # Here we are in the case of A1+A1; the two elements with indices 
        # k and k+1 respectively commute. We interchange their exponents.
        
        res:= [ ];
        for i in [1,3..Length(expr)-1] do
            mon:= ShallowCopy( expr[i] );
            for j in [1,3..Length(mon)-1] do
                
                if mon[j] = k+1 then
                    
                    # See whether the next element has index k+2.
                    
                    if j+2 < Length( mon ) and mon[j+2] = k+2 then
                        # interchange the exponents
                        store:= mon[j+1];
                        mon[j+1]:= mon[j+3];
                        mon[j+3]:= store;
                        break;
                    else
                        mon[j]:= k+2;
                        break;
                    fi;
                elif mon[j]=k+2 then
                    mon[j]:= k+1;
                    break;
                fi;
            od;
            Add( res, mon );
            Add( res, expr[i+1] );
        od;
        return res;
        
    elif Length( move ) >= 6 then
        
        # a2, b2 are booleans signalling whether we are in the A2, or B2 case.
        # `set' will be the set of indices that need to be treated.
        # `up' is the biggest element of this set. 
        
        a2:= false; b2:= false; 
        if Length( move ) = 6 then
            # case (alpha,beta)=-1
            a2:= true;
            set:= [k+1,k+2,k+3];
            up:= k+3;
            qa:= _q^( Bil[move[2]][move[2]]/2 );
        else   
            # case B2
            
            if Bil[move[2]][move[2]] = 4 then
                
                # i.e., b2 is true if we replace the sequence 
                # starting with the short root, by the sequence 
                # starting with the long one. 
                # if both a2 and b2 are false, then we are in the other case.
                b2:= true;
                
            fi;
            
            set:= [ k+1,k+2,k+3,k+4 ];
            up:= k+4;
        fi;
        
        res:= [ ];
        for i in [1,3..Length(expr)-1] do
            
            # `k1' will be the index of the first element in expr[i] belonging
            # to `set'; `k2'-1 will be the index of the last such element.
            
            k1:= 0; k2:= Length(expr[i])+1;
            for j in [1,3..Length(expr[i])-1] do
                if expr[i][j] in set and k1 = 0 then k1:= j; fi;
                if expr[i][j] > up then k2:= j; break; fi;
            od;

            if k1 = 0 then #i.e., nothing to do
                Add( res, expr[i] ); Add( res, expr[i+1] );
            else
  
                start:= expr[i]{[1..k1-1]};
                tail:= expr[i]{[k2..Length(expr[i])]};
                mn:= [ ];
                Add( mn, expr[i]{[k1..k2-1]} );
                
                # So now `mn' contains the part of the monomial that needs 
                # treatment.
                # We decrease the indices such that they will fall in the range
                # [1..3] (A2), or [1..4] (B2).
                
                for j in [1,3..Length(mn[1])-1] do
                    mn[1][j]:= mn[1][j] - k;
                od;
                Add( mn, expr[i+1] );
                
                # Now we feed `mn' to the rewrite routines (so later on we need
                # to increase the indices again).
                                
                if a2 then

                    mn:= QGPrivateFunctions.A2_rewrite( mn, qa );

                elif b2 then
                    
                    mn:= QGPrivateFunctions.B2_rewrite_1( mn );
                    
                else
                    
                    mn:= QGPrivateFunctions.B2_rewrite_2( mn );
                    
                fi;
                
                # We add start and tail again and increase the indices. 
                # Then we add the result to `res'.
                
                for j in [1,3..Length(mn)-1] do
                    mon:= ShallowCopy( start );
                    mon1:= mn[j];
                    for l in [1,3..Length(mon1)-1] do
                        mon1[l]:= mon1[l]+k;
                    od;
                    Append( mon, mon1 );
                    Append( mon, tail );
                    
                    pos:= Position( res, mon );
                    if pos <> fail then
                        res[pos+1]:= res[pos+1]+mn[j+1];
                        if res[pos+1] = 0*res[pos+1] then
                            Unbind( res[pos] ); Unbind( res[pos+1] );
                            res:= Filtered( res, x -> IsBound(x) );
                        fi;
                    else    
                        Add( res, mon );
                        Add( res, mn[j+1] );
                    fi;
                od;
            fi;
            
        od;
        return res;
        
    fi;

end;

QGPrivateFunctions.MoveIt:= function( R, w1, w2, expr )
    
    # Here `R' is the root system we are working in. `w1', `w2' are two
    # words in the Weyl group representing the same element.
    # `expr' is a w1-expression. We move it to a w2-expression,
    # by a sequence of elementary moves.

    local   moves,  u1,  move,  u2,  i;
    
    moves:= GetBraidRelations( WeylGroup(R), w1, w2 );
    u1:= ShallowCopy( w1 );
    for move in moves do 
        
        # apply move to u1
        
        u2:= ShallowCopy( u1 );
        for i in [1,3..Length(move)-1] do
            u2[move[i]]:= move[i+1];
        od;
        
        # Execute the move.
        
        expr:= QGPrivateFunctions.EltMove( u1, u2, move, expr, 
                       BilinearFormMatNF(R) );
    od;
    return expr;
end;


###############################################################################
##
##   Part two
##
##   In this part we compute commutation relations of the elements E_k, 
##   where E_k = T_{i1}...T_{i_{k-1}}( E_{k} ), where 
##   w0 = s_{i_1}...s_{i_t} is the longest element in the Weyl group,
##   and E_1...E_l are generators of the positive part of the quantum group,
##   where l is the rank of the root system. We use the fact that the T_i 
##   satisfy the braid relations together with the known commutation
##   relations for the rank two cases, to devise a recursive procedure 
##   (`com_rel') that calculates the commutation relations for the general 
##   case.
##   The function `E_tab' puts alll such relations into a table. The function
##   `F_tab' uses the table of the E-elements to create a table of the 
##   F-elements.
##
##   `GlTab' is a global variable; basically it is a big list containing all
##   computed commutation relations (so also many, many that we do not need).

QGPrivateFunctions.GlTab:= [ ];

QGPrivateFunctions.com_rel:= function( R, w, wp, j, m )

    # Here R (as usual) is the root system. This function computes
    # by a recursive procedure the skew-commutator of T_{w.wp}(E_j) 
    # and T_w(E_m)
    
    local   simple,  bas,  B,  collect,  Append_and_del,  wd1,  wd2,  
            i,  rel,  k,  C,  u,  qa,  v,  len,  sigma,  omega,  rt1,  
            rt2,  ip,  omp,  pi,  U,  V,  x,  va,  mon,  mon1,  cf,  
            s,  t,  cf1,  ome2,  case1;
    
    simple:= SimpleRootsAsWeights( R );
    bas:= Basis( VectorSpace( Rationals, simple ), simple );
    B:= BilinearFormMatNF( R );

    # We need a subfunction for collecting expressions; this subfunction gets 
    # the commutation relations it needs from recursive calls to `com_rel'.
    
    collect:= function( expr, j, x, q1, q2 )
        
        # Here `x' is a word of the form  v = [ i1, i2, i3 .. ik ]
        # It is a reduced word in the Weyl group. 
        # `expr' is an x-expression.
        # q1, q2 are elements of QuantumField.
        # We collect q1*expr*T_x(E_j)-q2*T_x(E_j)*expr. 
        # The output will in general be an xs_j-expression.
        
        local   k,  todo,  i,  m,  s,  res,  cf,  found,  mon,  ex,  
                pos,  u1,  u2,  lastind,  rel,  r1,  r2,  st,  start,  
                tail,  t, newexpr, v;        

        
        if expr = [] then return []; fi;

        k:= Length(x)+1;

        # `newexpr' will be q1*expr*T_x(E_j)-q2*T_x(E_j)*expr.
        
        newexpr:= [ ];
        for i in [1,3..Length(expr)-1] do
            m:= ShallowCopy(expr[i]);
            Append( m, [k,1] );
            Add( newexpr, m );
            Add( newexpr, expr[i+1]*q1 );

            m:= [k,1];
            Append( m, expr[i] );
            Add( newexpr, m );
            Add( newexpr, -expr[i+1]*q2 );
        od;

        v:= ShallowCopy( x );
        Add( v, j );

        k:= Length(v);

        # We "stretch" the monomials in `newexpr' (e.g., [1,3,2,2] is 
        # represented as [1,1,1,2,2]). We put the result in `todo'.
        
        todo:= [ ];
        for i in [1,3..Length(newexpr)-1] do
            m:= [ ];
            for s in [1,3..Length(newexpr[i])-1] do
                Append( m, List( [1..newexpr[i][s+1]], x -> newexpr[i][s] ) );
            od;
            
            todo[i]:= m;
            todo[i+1]:= newexpr[i+1];
        od;

        res:= [ ];
        while todo <> [] do

            m:= todo[1];
            cf:= todo[2];

            # We try to find the first position in `m' where the 
            # elements are not in the right order.
            
            found:= false;
            for i in [1..Length(m)-1] do
                if m[i] > m[i+1] then
                    found:= true;
                    break;
                fi;
            od;
            if not found then

                # We transform the monomial back to non-stretched form,
                # and add the result to `res'.
                
                mon:= [ ];
                s:= 1;
                while s <= Length( m ) do
                    ex:= 1;
                    while s < Length(m) and m[s+1] = m[s] do
                        s:= s+1;
                        ex:= ex+1;
                    od;
                    Add( mon, m[s] );
                    Add( mon, ex );
                    s:= s+1;
                od;
                
                pos:= Position( res, mon );
                if pos <> fail then
                    res[pos+1]:= res[pos+1]+cf;
                    if res[pos+1] = 0*cf then
                        Unbind( res[pos] ); Unbind( res[pos+1] );
                        res:= Filtered( res, x -> IsBound(x) );
                    fi;
                else    
                    Add( res, mon );
                    Add( res, cf );
                fi;
                
                Unbind( todo[1] );
                Unbind( todo[2] );
                todo:= Filtered( todo, x -> IsBound(x) );
            else

                # We apply a commutation relation found by a call to `com_rel'.
                # The commutation relation is [ T_{u1u2}(E_r), T_{u1}(E_s) ],
                # with u1, u2 as below, and r = v[m[i]], 
                # s = v[m[i+1]]. (Recall that the index of an element
                # T_{w}(E_i) is lenw+1). 
 
                u1:= v{[1..m[i+1]-1]};
                u2:= v{[m[i+1]..m[i]-1]};
                
                rel:= QGPrivateFunctions.com_rel( R, u1, u2, v[m[i]], 
                                    v[m[i+1]] );

                # The commutation relation is 
                # T_{u1u2}(E_r)T_{u1}(E_s) = q^{-(u2(a_r),a_s)}T_{u_1}(E_s)
                #      T_{u1u2}(E_r) + \sigma.
                # Where a_r, a_s are the r-th, and s-th simple roots. 
                # We calculate the exponent of q in this formula.
                
                r1:= ApplyWeylElement( WeylGroup(R), simple[ v[m[i]] ], u2 );
                r1:= Coefficients( bas, r1 );
                r2:= SimpleSystemNF(R)[ v[m[i+1]] ];
                todo[2]:= todo[2]*_q^( -r1*(B*r2) );

                # Now we change the order of the elements in the principal 
                # monomial, and we add the \sigma (see previous comment).

                st:= m[i];
                m[i]:= m[i+1]; m[i+1]:= st;
                todo[1]:= m; 
                start:= m{[1..i-1]};
                tail:= m{[i+2..Length(m)]};
                for s in [1,3..Length(rel)-1] do
                    mon:= ShallowCopy( start );
                    for t in [1,3..Length(rel[s])-1] do
                        Append( mon, List( [1..rel[s][t+1]], x -> rel[s][t]));
                    od;
                    Append( mon, tail );
                    Add( todo, mon ); Add( todo, cf*rel[s+1] ); 
                od;
            fi;
        od;

        return res;        
                
    end;
    
    
    Append_and_del:= function( expr1, expr2 )
        
        # append expr2 to expr1, deleting monomials if cancellations occur...
        
        local   k,  pos;        
        
        for k in [1,3..Length(expr2)-1] do
            pos:= Position( expr1, expr2[k] );
            if pos <> fail then
                expr1[pos+1]:= expr1[pos+1]+expr2[k+1];
                if expr1[pos+1] = 0*expr1[pos+1] then
                    Unbind( expr1[pos] ); Unbind( expr1[pos+1] );
                    expr1:= Filtered( expr1, x -> IsBound(x) );
                fi;
            else    
                Add( expr1, expr2[k] );
                Add( expr1, expr2[k+1] );
            fi;
        od;
        return expr1;
    end;    
    
    # First we check whether the relation is already there
    
    wd1:= ShallowCopy(w); 
    Append( wd1, wp );
    Add( wd1, j );
    wd2:= ShallowCopy( w );
    Add( wd2, m );
    
    for i in [1..Length(QGPrivateFunctions.GlTab)] do
        if QGPrivateFunctions.GlTab[i][1] = wd1 and 
           QGPrivateFunctions.GlTab[i][2] = wd2 then
            return List( QGPrivateFunctions.GlTab[i][3], ShallowCopy );
        fi;
    od;
    
    if w <> [] then
        rel:= List( QGPrivateFunctions.com_rel( R, [],  wp, j, m ), 
                    ShallowCopy );
        for i in [1,3..Length(rel)-1] do
            for k in [1,3..Length(rel[i])-1] do
                rel[i][k]:= rel[i][k]+Length(w);
            od;
        od;
        Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
        return rel;
    fi;
   
    C:= CartanMatrix(R);
    
    # case Len(wp)=1 is straightforward...
    
    if Length(wp) = 1 then
   
        # they commute
        Add( QGPrivateFunctions.GlTab, [ wd1, wd2, [] ] );
        return [];

    fi;
    
    
    i:= wp[Length(wp)];
    u:= wp{[1..Length(wp)-1]};
    
    if C[i][j] = 0 then
        
        rel:= QGPrivateFunctions.com_rel( R, [], u, j, m );
        Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
        return rel;
        
    elif C[i][j] = -1 and C[j][i] = -1 then
        
        qa:= _q^( B[j][j]/2 );
        v:= ShallowCopy( u );
        Add( v, j );
        len:= LengthOfWeylWord( WeylGroup(R), v );
        
        if len > Length(u) then
            
            
            sigma := List( QGPrivateFunctions.com_rel( R, [], u, j, m ), 
                           ShallowCopy );
            omega := List( QGPrivateFunctions.com_rel( R, [], u, i, m ), 
                           ShallowCopy );
            
            rt1:= ApplyWeylElement( WeylGroup(R), simple[j], u );
            rt2:= ApplyWeylElement( WeylGroup(R), simple[i], u );
            rt2:= Coefficients( bas, rt2 );
            rt2[m]:= rt2[m]+1;
            ip:= Coefficients( bas, rt1 )*(B*rt2); 
                                    
            rel:= collect( omega, j, u, -_q^(-ip), -_q^0 );
            
            for k in [2,4..Length(rel)] do
                rel[k]:= rel[k]*(-qa^-1);
            od;

            rt1:= ApplyWeylElement( WeylGroup(R), simple[ i ], u );
            ip:= SimpleSystemNF(R)[m]*( B*Coefficients( bas, rt1 ) );

            rel:= Append_and_del( rel, 
                           collect( sigma, i, u, -_q^(-B[j][j]/2-ip), -_q^0 ) );

            Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
            return rel;

        else
            
            v:= ExchangeElement( WeylGroup(R), u, j );
            if (not IsBound( v[1] ) ) or v[1] <> u[1] then
                
                # the rel is -qa*T_u( E_i )
                
                rel:= [ [ Length(u)+1, 1 ], -qa ];
                
            else
                rel:= QGPrivateFunctions.com_rel( R, [], v, i, m );
                Add( v, j );
                rel:= QGPrivateFunctions.MoveIt( R, v, u, rel );
            fi;
            
            
            Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
            return rel;
        fi;
        
    elif C[i][j] = -1 and C[j][i] = -2 then
        
        v:= ShallowCopy( u );
        Add( v, j );
        len:= LengthOfWeylWord( WeylGroup(R), v );
        
        if len > Length(u) then
            
            sigma := List( QGPrivateFunctions.com_rel( R, [], u, j, m ), 
                           ShallowCopy );
            omega := List( QGPrivateFunctions.com_rel( R, [], u, i, m ), 
                           ShallowCopy ); 
            
            rt1:= ApplyWeylElement( WeylGroup(R), simple[j], u );
            rt2:= ApplyWeylElement( WeylGroup(R), simple[i], u );
            rt2:= Coefficients( bas, rt2 );
            rt2[m]:= rt2[m]+1;
            ip:= Coefficients( bas, rt1 )*(B*rt2); 
                                    
            omp:= collect( omega, j, u, -_q^(-ip), -_q^0 );
            
            pi:= List( omp, ShallowCopy );
            
            for k in [2,4..Length(pi)] do
                pi[k]:= pi[k]*(-_q^-2);
            od;

            rt1:= ApplyWeylElement( WeylGroup(R), simple[ i ], u );
            ip:= SimpleSystemNF(R)[m]*( B*Coefficients( bas, rt1 ) );

            pi:= Append_and_del( pi, 
                           collect( sigma, i, u, -_q^(-2-ip), -_q^0 ) );
            
            U:= collect( pi, i, u, -_q^(-ip), -_q^0 );
            V:= collect( omp, i, u, -_q^(-4-ip), -_q^0 );
            omp:= collect( omega, i, u, -_q^(-2-ip), -_q^0 );
            
            rt1:= ApplyWeylElement( WeylGroup(R), simple[j], u );
            ip:= SimpleSystemNF(R)[m]*( B*Coefficients( bas, rt1 ) );
            omp:= collect( omp, j, u, -_q^(4-ip), -_q^0 );
            
            # the result is (U-V+_q^-2*omp)/(_q+_q^-1)
            
            rel:= omp;
            for k in [2,4..Length(rel)] do
                rel[k]:= rel[k]*_q^-2;
            od;
            rel:= Append_and_del( rel, U );
            for k in [2,4..Length(V)] do
                V[k]:= -V[k];
            od;
            rel:= Append_and_del( rel, V );
            
            # divide by _q+_q^-1.
            
            for k in [2,4..Length(rel)] do
                rel[k]:= rel[k]/(_q+_q^-1);
            od;

            Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
            return rel;
            
        else   # i.e. len < Length(u)
            
            v:= ExchangeElement( WeylGroup(R), u, j );
            if (not IsBound( v[1] ) ) or v[1] <> u[1] then
                
                # the rel is -(q^2-1)/(q+q^-1)*T_u( E_i )^2
                
                rel:= [ [ Length(u)+1, 2 ], -(_q^2-1)/(_q+_q^-1) ];
                Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
                return rel;
                
            else
                
                x:= ShallowCopy( v ); 
                Add( x, i );
                if LengthOfWeylWord( WeylGroup(R), x ) > Length( v ) then
                    
                    omega:= List( QGPrivateFunctions.com_rel( R, [], u, 
                                    i, m ), ShallowCopy );
                    va:= ShallowCopy( v );
                    Add( va, j );
                    omega:= QGPrivateFunctions.MoveIt( R, u, va, omega );
                    
                    # now we perform the `diffcult algorithm' on omega, i.e., 
                    # we straighten 
                    #     T_v( E_i )*omega-q^(v*i,m)*omega*T_v( E_i ), 
                    # and we do it "by hand".
                    # we collect all results in pi
                    pi:= [ ];
                    
                    rt1:= ApplyWeylElement( WeylGroup(R), simple[i], v );
                    ip:= SimpleSystemNF(R)[m]*( B*Coefficients( bas, rt1 ) );
                    
                    for k in [1,3..Length(omega)-1] do
                        
                        mon:= omega[k];
                        if mon[Length(mon)-1] <> Length( va ) then
                            # the monomial does not contain the 
                            # `evil' element i.e., T_v( E_j ); 
                            # we can do the usual thing.
                            
                            omp:= collect( [ mon, -omega[k+1] ], i, v, 
                                           -_q^(-ip), -_q^0 );
                                           
                            pi:= Append_and_del( pi,
                               QGPrivateFunctions.MoveIt( R, va, u, omp ));
                            
                            
                        else
                            # it does contain the evil element; we are very
                            # distressed; we have to do it all by hand...

                            mon1:= mon{[1..Length(mon)-2]};
                            # i.e., this is the part without the evil elt.
                            cf:= -omega[k+1];
                            
                            s:= mon[Length(mon)];
                            # i.e., the power with which the evil
                            # element occurs

                            omp:= collect( [ mon1, cf ], i, v, 
                                          -_q^(-ip+s*B[i][j]), -_q^0 );
                            
                            cf:= cf*_q^(-ip+s*B[i][j]); # for later use...
                                     
                            for t in [1,3..Length(omp)-1] do
                                Append( omp[t], [ Length(va), s ] );
                            od;

                            omp:= QGPrivateFunctions.MoveIt( R, va, u, omp );
                            pi:= Append_and_del( pi, omp );             

                            cf1:= _q^(2*s);
                            for t in [1..s-1] do
                                cf1:= cf1 + _q^(2*s-4*t);
                            od;
                            if s > 1 then
                                Append( mon1, [ Length(va), s-1 ] );
                            fi;
                            
                            ome2:= [ mon1, -cf*cf1 ];
                            ome2:= QGPrivateFunctions.MoveIt( R, va, u, ome2 );
                            for t in [1,3..Length(ome2)-1] do
                                Append( ome2[t], [ Length(u)+1, 1 ] );
                            od;
                            
                            pi:= Append_and_del( pi, ome2 );
                        fi;    
                    od;

                    sigma:= List( QGPrivateFunctions.com_rel( R, [], v, 
                                    i, m ), ShallowCopy );
                    sigma:= QGPrivateFunctions.MoveIt( R, va, u, sigma );

                    rt1:= ApplyWeylElement( WeylGroup( R ), simple[i], u );
                    ip:= SimpleSystemNF(R)[m]*( B*Coefficients(bas,rt1) );
                    rel:= Append_and_del( pi, collect( sigma, i, u, 
                                  -_q^(-ip), -_q^0 ) );
                    
                    # divide by q+q^-1.
            
                    for k in [2,4..Length(rel)] do
                        rel[k]:= rel[k]/(_q+_q^-1);
                    od;

                    Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
                    return rel;                    
                            
                else
                    
                    x:= ExchangeElement( WeylGroup(R), v, i );
                    if (not IsBound( x[1] ) ) or x[1] <> v[1] then
                        
                        # the rel is -q^2*T_u( E_i )
                        
                        rel:= [ [ Length(u)+1, 1 ], -_q^2 ];
                        
                    else
                        rel:= QGPrivateFunctions.com_rel( R, [], x, j, m );
                        Add( x, i ); Add( x, j );
                        rel:= QGPrivateFunctions.MoveIt( R, x, u, rel );
                    fi;
                    
                    
                    Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
                    return rel;
                fi;                    
            fi;
        fi;
    elif C[i][j] = -2 and C[j][i] = -1 then
        
        v:= ShallowCopy( u );
        Add( v, j );
        len:= LengthOfWeylWord( WeylGroup(R), v );

        if len > Length(u) then
            
            sigma := List( QGPrivateFunctions.com_rel( R, [], u, j, m ),
                           ShallowCopy );
            omega := List( QGPrivateFunctions.com_rel( R, [], u, i, m ), 
                           ShallowCopy ); 
            
            rt1:= ApplyWeylElement( WeylGroup(R), simple[j], u );
            ip:= Coefficients( bas, rt1 )*( B*SimpleSystemNF(R)[m] ); 
                                    
            rel:= collect( omega, j, u, -_q^(2-ip), -_q^0 );

            for k in [2,4..Length(rel)] do
                rel[k]:= rel[k]*(-_q^-2);
            od;

            rt1:= ApplyWeylElement( WeylGroup(R), simple[ i ], u );
            ip:= SimpleSystemNF(R)[m]*( B*Coefficients( bas, rt1 ) );

            rel:= Append_and_del( rel, 
                           collect( sigma, i, u, -_q^(-2-ip), -_q^0 ) );

            Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
            return rel;        
            
        else  # i.e. len < Length(u)

            v:= ExchangeElement( WeylGroup(R), u, j );

            if (not IsBound( v[1] ) ) or v[1] <> u[1] then
                
                # the rel is -(q+q^-1)*T_u( E_i )
                
                rel:= [ [ Length(u)+1, 1 ], -(_q+_q^-1) ];
                Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
                return rel;
                
            else
                
                x:= ShallowCopy( v ); 
                Add( x, i );

                if LengthOfWeylWord( WeylGroup(R), x ) > Length( v ) then

                    sigma:= List( QGPrivateFunctions.com_rel( R, [], v, 
                                    i, m ), ShallowCopy );
                    omega:= List( QGPrivateFunctions.com_rel( R, [], v, 
                                    j, m ), ShallowCopy );
                    
                    rt1:= ApplyWeylElement( WeylGroup(R), simple[i], v );
                    ip:= SimpleSystemNF(R)[m]*( B*Coefficients( bas, rt1 ) );
            
                    rel:= collect( omega, i, v, -_q^(2-ip), -_q^0 );
            
                    for k in [2,4..Length(rel)] do
                        rel[k]:= -rel[k]*_q^(-2);
                    od;
                    
                    rt1:= ApplyWeylElement( WeylGroup(R), simple[j], v );
                    ip:= SimpleSystemNF(R)[m]*( B*Coefficients( bas, rt1 ) );
            
                    rel:= Append_and_del( rel, 
                                  collect( sigma, j, v, -_q^(-2-ip), -_q^0 ));
                    # finally we move `rel' to a u-expression:
                    va:= ShallowCopy( v );
                    Add( va, j );    

                    rel:= QGPrivateFunctions.MoveIt( R, va, u, rel );

                    Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
                    return rel;        
                    
                else
                    
                    x:= ExchangeElement( WeylGroup(R), v, i );

                    if (not IsBound( x[1] ) ) or x[1] <> v[1] then
                        
                        # the rel is -q^2T_v( E_j )
                        
                        rel:= [ [ Length(v)+1, 1 ], -_q^2 ];
                        va:= ShallowCopy( v );
                        Add( va, j );             
                        rel:= QGPrivateFunctions.MoveIt( R, va, u, rel );
                        
                    else

                        rel:= QGPrivateFunctions.com_rel( R, [], x, j, m );
                        Add( x, i ); Add( x, j );
                        rel:= QGPrivateFunctions.MoveIt( R, x, u, rel );
                    fi;
                    
                    
                    Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
                    return rel;
                fi;       
            fi;
        fi;
        
        
    elif C[j][i] = -3 or C[i][j] = -3 then    

        # Here we are in a G2-case; we fill in the commutators directly. 
        # Let the commutator be written as [ T_uT_{\beta_r}(E_a), E_b ].
        # Then the commutator is zero if the root b does not belong to the 
        # component of type G2 spanned by \beta_r, a (i.e., if b is not 
        # beta_r, or a). 
        # In other cases we use T_uT_{\beta_r}(E_a) = T_xT_{\beta_r}(E_a), 
        # where
        # x is obtained from u by deleting all elements that are not equal to
        # beta_r, a. Then we can fill in the commutation relation, and 
        # finally have
        # to change the result to a us_{\beta_r}-expression again.

        if not m in [ i, j ] then

            Add( QGPrivateFunctions.GlTab, [ wd1, wd2, [] ] );
            return [];
        else
            
            # Let a,b be two simple roots of a root system of type G2,
            # such that <a,b*>=-1, <b,a*>=-3. Then we say that we are in 
            # `case1'
            # if the longest word in the Weyl group that we use is
            # s_a s_b s_a s_b s_a s_b. We are in case2 if s_b s_a... is used.
            # First we determine in which case we are.

            x:= Filtered( u, ind -> ind in [ i, j ] );
            Add( x, i );

            case1:= false; 
            if C[j][i] = -3 then
               if x[1] = i then case1:= true; fi;
            else
               if x[1] = j then case1:= true; fi;
            fi;

            if case1 then
       
               len:= Length( x );
               if len = 1 then
                  
                  Add( QGPrivateFunctions.GlTab, [ wd1, wd2, [] ] );
                  return [];

               elif len = 2 then
                  
                  rel:= [ [ 2, 1 ], -(_q+_q^-1+_q^-3) ];

               elif len = 3 then 
  
                  rel:= [ [ 3, 2 ], 1-_q^2 ];

               elif len = 4 then

                  rel:= [ [ 3, 1 ], -1-_q^2 ];

               else # i.e., len =5

                  rel:= [ [ 5, 1 ], -_q^3 ];
     
               fi;

            else # we are in case 2...

               len:= Length( x );
               if len = 1 then
                  
                  Add( QGPrivateFunctions.GlTab, [ wd1, wd2, [] ] );
                  return [];

               elif len = 2 then
                  
                  rel:= [ [ 2, 3 ], -(1-2*_q^2+_q^4)/(1+_q^2+_q^4) ];

               elif len = 3 then 
  
                  rel:= [ [ 2, 2 ], 1-_q^2 ];

               elif len = 4 then

                  rel:= [ [ 2, 1, 4, 1 ], _q^2-_q^4, [ 3, 1 ], _q^4+_q^2-1 ]; 

               else # i.e., len =5

                  rel:= [ [ 2, 1 ], -_q^3 ];
     
               fi;
            fi;

            # Now we need to correct the indices...
            # We have that rel is an expression relative to an isolated 
            # component of type G2. We now have to change `rel' into an
            # expression relative to `wp'. We write `wp = xv'. Then
            # `rel' is an x-expression, and hence an xv-expression.
            # We use MoveIt to move it into a wp-expression. Note that
            # the move works, because it never executes a move in 
            # the component of type G2.

            Append( x, Filtered( u, ind -> not ind in [ i, j ] ) ); 
         
            rel:= QGPrivateFunctions.MoveIt( R, x, wp, rel );
            Add( QGPrivateFunctions.GlTab, [ wd1, wd2, rel ] );
            return rel;

        fi;
        
    fi;
    
end;


QGPrivateFunctions.E_Tab:= function( R )
    
    local   w0, comm,  i,  j,  posR,  bas,  rts1, rts2;
        
    w0:= LongestWeylWord(R);
    QGPrivateFunctions.GlTab:= [ ];
    comm:= [ ];

    for i in [0..Length(w0)-1] do
        for j in [i+1..Length(w0)-1] do

            Add( comm, [ [j+1,i+1], 
                    QGPrivateFunctions.com_rel( R, w0{[1..i]}, w0{[i+1..j]}, 
                            w0[j+1], w0[i+1] ) ] );
        od;
    od;
    
    QGPrivateFunctions.GlTab:= [ ];
    
    posR:= PositiveRootsAsWeights( R );
    rts1:= List( [0..Length(w0)-1], i -> ApplyWeylElement( WeylGroup(R), 
                   SimpleRootsAsWeights(R)[w0[i+1]], w0{[1..i]} ) ); 
    rts2:= List( rts1, i -> PositiveRootsNF(R)[ Position( posR, i ) ] ); 
    
    MakeImmutable(comm);
    return [ rts2, comm ];
end;

QGPrivateFunctions.F_tab:= function( R, Etab, rts )

    # The function returns the commutation table of the F-elements. The input
    # is formed by a root system, and the second and first elements of the 
    # output
    # of `E_Tab'. For computing a commutation relation of F-elements we use the
    # automorphism f of U_q(g) given by f(F_{\alpha})=E_{\alpha}, 
    # f(K_{\alpha}) = K_{\alpha}^-1, f(E_{\alpha}) = F_{\alpha}. Then we have
    # the following formula:
    #
    #   f(T_w(E_{\alpha})) = 
    #    ( \prod_{\gamma\in\Delta} (-q_{\gamma})^{-m_{\gamma}})*
    #                                      T_w(F_{\alpha})
    #
    # where w(\alpha) - \alpha = \sum_{\gamma\in\Delta} m_{\gamma}\gamma.
    # Using this it is straightforward to calculate the commutation table of 
    # the F-elements.

    local   w0,  cfs,  i,  a,  c,  j,  ftab,  sigma,  cf,  k;
    
    w0:= LongestWeylWord( R );
    cfs:= [ ];
    for i in [1..Length(w0)] do

        # Set u = w0{[1..i-1]}, then rts[i] is the image of the simple
        # root a with index w0[i] under u. We compute the coefficient 
        # `c' such that f(T_u(E_a)) = c*T_u(F_a). 
 
        a:= rts[i] - SimpleSystemNF(R)[w0[ i ]];
        c:= _q^0;

        for j in [1..Length(a)] do
            c:= c*( (-_q^(BilinearFormMatNF(R)[j][j]/2 ))^(-a[j]) );
        od;
        Add( cfs, c );
    od;

    ftab:= [ ];
    for i in [1..Length(Etab)] do
        
        sigma:= List( Etab[i][2], ShallowCopy );
        
        cf:= 1/(cfs[Etab[i][1][1]]*cfs[Etab[i][1][2]]);
        
        # we calculate cf*f(sigma)
        for j in [1,3..Length(sigma)-1] do
            c:= _q^0;
            for k in [1,3..Length(sigma[j])-1] do
                c:= c*( cfs[sigma[j][k]]^sigma[j][k+1] );
            od;
            sigma[j+1]:= sigma[j+1]*c*cf;
        od;
        Add( ftab, [ Etab[i][1], sigma ] );
    od;
    MakeImmutable( ftab );
    return ftab;
end;



#############################################################################
##
##  Part three
##
##  The computation of the commutation relations between the E-elements and
##  the F-elements.    
##
        
QGPrivateFunctions.FE_table:= function( R, Etab, Ftab, rts )
    
    # here the rts are the positive roots, the Etab is the E-mult tab,
    # indexed by the roots in rts. Ftab is the F-mult tab.
    # We use the following indexing of the elements: If i <= s, then 
    # i is the index of an F, if s+1 <= i <= s+rank, then i is the index
    # of a K, if i >= s+rank+1, then i is the index of an E; where 
    # s is the number of positive roots.
    
    local   collect,  posR,  s,  bas,  cfs,  B,  rank,  sim,  FEtab,  
            i,  j,  qa,  cf,  k,  k1,  k2,  pair,  rel,  pos,  mon,  
            l,  expr,  cc,  p1,  p2;
    
    collect:= function( expr, Ecollect, Fcollect )
        
        # collect expr, using known relations and those in Etab.
        # If `Ecollect' is false then we do not collect E's and
        # similarly for Fcollect.
        
        local   todo,  res,  m,  cf,  k,  found,  pos,  k1,  k2,  rel,  
                start,  tail,  mn,  i,  m1,  j, comm_rule, r;
        
        
        comm_rule:= function( rel, j, i, m, n, r )
        
        # commutation rule for x_j^mx_i^n, where x_jx_i=q^rx_jx_i+rel
        
        local   rule,  l,  k,  cf,  u,  mn, start, tail;        
        
        rule:= [ [ i, n, j, m], _q^(n*m*r) ];
        for l in [0..n-1] do
            for k in [0..m-1] do
                cf:= _q^((l*m+k)*r);
                start:= [ ];
                if l <> 0 then
                    Add( start, i ); Add( start, l );
                fi;
                if m-1-k <> 0 then
                    Add( start, j ); Add( start, m-1-k );
                fi;
                tail:= [];
                if k <> 0 then
                    Add( tail, j ); Add( tail, k );
                fi;
                if n-1-l <> 0 then
                    Add( tail, i ); Add( tail, n-1-l );
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


        todo:= expr;
        res:= [ ];
        while todo <> [] do

            m:= todo[1];
            cf:= todo[2];

            k:= 1; found:= false;
            while k < Length(m)-2 do
                if m[k] > m[k+2] then
                    if Ecollect or m[k+2] <= s+rank then
                        # i.e., if it is 2 E's and Ecollect is false then we
                        # do not end up here, and so the search will continue.
                        # This means that for those cases we do nothing.
                        
                        if Fcollect or m[k] > s then
                            # again, if it is two F's and Fcollect is false, 
                            # then we do not end up here; so we  
                            # do nothing in that case either.

                            found:= true;
                            break;
                        fi;
                        
                    fi;
                elif m[k] = m[k+2] then

                    # add the exponents...

                    m[k+1]:= m[k+1]+m[k+3];
                    Unbind( m[k+2] ); Unbind( m[k+3] );
                    if m[k+1] = 0*m[k+1] then
                        Unbind( m[k] ); Unbind( m[k+1] );
                        k:= k-2;

                    fi;

                    m:= Filtered( m, x -> IsBound(x) );
                fi;
                k:= k+2;
            od;
            
            if not found then

                # Add the monomial to `res'.
      
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
                
                k1:= m[k]; k2:= m[k+2];

                # we know k1 > k2...
                
                if k1 > s+rank then
                    
                    # i.e., k1 is an E
                    
                    if k2 > s+rank then
                        
                        # i.e., k2 is also an E, commutation from Etab
                        
                        pos:= PositionProperty( Etab, x -> 
                                  x[1] = [ k1-s-rank, k2-s-rank] );
                        r:= rts[k1-s-rank]*( B*rts[k2-s-rank]);
                        rel:= comm_rule( Etab[pos][2], m[k]-s-rank, 
                                      m[k+2]-s-rank, 
                                      m[k+1], m[k+3], -r );
                        start:= m{[1..k-1]};
                        tail:= m{[k+4..Length(m)]};

                        # We apply the commutation rule; the first monomial 
                        # we get will go to the first position of `todo'.
                        
                        for i in [1,3..Length(rel)-1] do
                            mn:= ShallowCopy( start );
                            m1:= ShallowCopy( rel[i] );
                            for j in [1,3..Length(m1)-1] do
                                m1[j]:= m1[j]+s+rank;
                            od;
                            Append( mn, m1 ); Append( mn, tail );
                            if i = 1 then
                                todo[1]:= mn;
                                todo[2]:= cf*rel[i+1];
                            else
                                Add( todo, mn ); Add( todo, cf*rel[i+1] );
                            fi;

                        od;
                        
                    elif k2 > s then
                        
                        # i.e., k2 is a K, commutation easy
                        
                        mn:= m{[1..k-1]};
                        Add( mn, m[k+2] ); Add( mn, m[k+3] );
                        Add( mn, m[k] ); Add( mn, m[k+1] );
                        Append( mn,m{[k+4..Length(m)]} );
                        todo[1]:= mn;
                        todo[2]:= cf*_q^( -m[k+1]*rts[k1-s-rank]*( 
                                          B*( m[k+3]*sim[k2-s] ) ) );
                    else
                        # k2 is an F, commutation from FEtab

                        pos:= PositionProperty( FEtab, x -> x[1] = [k1,k2] );
                        rel:= comm_rule( FEtab[pos][2], m[k], m[k+2], 
                                      m[k+1], m[k+3], 0 );
                        start:= m{[1..k-1]};
                        tail:= m{[k+4..Length(m)]};
                        
                        for i in [1,3..Length(rel)-1] do
                            mn:= ShallowCopy( start );
                            Append( mn, rel[i] ); Append( mn, tail );
                            if i = 1 then
                                todo[1]:= mn; 
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
                    else
                        
                        # i.e., k2 is an F, commutation easy 
                        
                        mn:= m{[1..k-1]};
                        Add( mn, m[k+2] ); Add( mn, m[k+3] );
                        Add( mn, m[k] ); Add( mn, m[k+1] );
                        Append( mn,m{[k+4..Length(m)]} );
                        todo[1]:= mn;
                        todo[2]:= cf*_q^( -m[k+1]*sim[k1-s]*( 
                                          B*( m[k+3]*rts[k2] ) ) );
                    fi;
                else
                    # i.e., k1, k2 are both F's. 
                    # commutation from Ftab
                    
                    pos:= PositionProperty( Ftab, x -> x[1] = [ k1, k2] );
                    r:= rts[k1]*( B*rts[k2]);
                    rel:= comm_rule( Ftab[pos][2], m[k], m[k+2], 
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
        
    
    posR:= ShallowCopy( PositiveRootsNF( R ) );
    s:= Length(posR);
    bas:= Basis( VectorSpace( Rationals, SimpleSystemNF( R ) ), 
                 SimpleSystemNF( R ) );
    cfs:= List( List( posR, x -> Coefficients( bas, x ) ), Sum );
    SortParallel( cfs, posR );    

    # in posR the roots are now sorted according to level; we loop through
    # this list.
    
    B:= BilinearFormMatNF(R);
    rank:= Length( B );
    sim:= SimpleSystemNF( R );
    
    FEtab:= [ ];
    
    for i in [1..rank] do
        for j in [1..s] do

            # We calculate the commutation rule of E_j with F_i. If 
            # j <= rank, then this relation is one of the defining relations 
            # of the qea. Otherwise
            # we use the relations in the multiplication table to write E_j
            # as a polynomial in E_k, where all E_k belong to roots of lower 
            # level.
            # Here E_j corresponds to the j-th element of posR, and 
            # F_i corresponds to the i-th element of sim...

            if posR[j] in sim then
                # we know the commrel...
                
                if posR[j] <> sim[i] then
                    # they commute...
                    Add( FEtab, [ [ s+rank+Position(rts,posR[j]), 
                            Position( rts, sim[i] ) ], [] ] );
                else

                    qa:=  _q^( B[i][i]/2 );
                    cf:= 1/(qa-qa^-1);
                    Add( FEtab, [ [ s+rank+Position(rts,posR[j]), 
                            Position( rts, sim[i] ) ], 
                            [ [s+i,1], cf, [ s+i, -1 ], -cf ] ] );
                fi;
            else
                
                # we calculate the com rel of E_j with F_i

                # We write E_j as a polynomial in the E_k of lower level. 

                for k in [1..rank] do

                    # First we find a simple root r such that posR[j]-r 
                    # is also a root

                    k1:= Position( rts, posR[j] - sim[k] );
                    if k1 <> fail then
                        k2:= Position( rts, sim[k] );

                        if k1 > k2 then
                           pair:= [ k1, k2 ];
                        else
                           pair:= [ k2, k1 ];
                        fi;

                        rel:= ShallowCopy( Etab[ PositionProperty( Etab, x -> 
                                        x[1] = pair ) ][2] );

                        # we establish whether E_j is in there
                        pos:= Position( rel, [ Position( rts, posR[j] ), 1 ] );
                        if pos <> fail then break; fi;
                    fi;
                od;

                # We throw away the E_j in `rel'.
                cf:= rel[ pos+1];
                Unbind( rel[pos] ); Unbind( rel[pos+1] );
                rel:= Filtered( rel, x -> IsBound(x) );

                # Get the indexing and the coefficients right:
                for k in [1,3..Length(rel)-1] do
                    mon:= ShallowCopy( rel[k] );
                    for l in [1,3..Length(mon)-1] do
                        mon[l]:= mon[l] + s+rank;
                    od;
                    rel[k]:= mon;
                    rel[k+1]:= -(1/cf)*rel[k+1];
                od;
                
                # Now we add the AB-q^*BA bit:
                    
                Add( rel, [ pair[1]+s+rank, 1, pair[2]+s+rank, 1 ] );
                Add( rel, 1/cf );
                
                qa:=  _q^( -rts[k1]*( B*rts[k2] ) );
                Add( rel, [ pair[2]+s+rank, 1, pair[1]+s+rank, 1 ] );
                Add( rel, -qa/cf );
        
                # now `rel' is the `definition' of E_j (in terms of pbw
                # elts of lower level). We commute. `expr' will be 
                # the commutator rel*F_i-F_i*rel.  

                expr:= [ ];
                pos:= Position( rts, sim[i] ); # this is the index of F_i
                for k in [1,3..Length(rel)-1] do
                    mon:= ShallowCopy( rel[k] );
                    Append( mon, [ pos, 1 ] );
                    Add( expr, mon ); Add( expr, rel[k+1] );
                    mon:= [ pos, 1 ];
                    Append( mon, rel[k] );
                    Add( expr, mon ); Add( expr, -rel[k+1] );
                od;

                # First we collect everything to terms of the form FKE,
                # where, maybe, the F-part and the E-part are uncollected.
                # We do this because a collection of two E-s my result 
                # in an E of higher level. This in turn may lead to a 
                # commutation relation for an F and an E being needed which 
                # is not there (yet).

                cc:= collect( expr, false, false );
                # this comes back without the F's; only in the 
                # E-part there may be some collection needed....

                cc:= collect( cc, true, true );

                Add( FEtab, [ [ s+rank+Position( rts, posR[j] ), pos ], 
                                                         cc ] );
            fi;
        od;
    od;
    
    # now we know all comm rels of E_j , F_i for 1<=i<=rank;
    # now we do the rest. (Basically same loop with E,F interchanged).

    for i in [1..s] do
        
        if not posR[i] in sim then
        
            # We write F_i as a polynomial in F_k of lower rank.
            # Now F_i corresponds to posR[i]...
            
            for k in [1..rank] do
                # We find a simple root r such that posR[i]-r is also a root.
                
                k1:= Position( rts, posR[i] - sim[k] );
                if k1 <> fail then
                    k2:= Position( rts, sim[k] );
                    
                    if k1 > k2 then
                        pair:= [ k1, k2 ];
                    else
                        pair:= [ k2, k1 ];
                    fi;
                    
                    rel:= ShallowCopy( Ftab[ PositionProperty( Ftab, x -> 
                                  x[1] = pair ) ][2] );
                    
                    # We establish whether F_i is in there.
                    pos:= Position( rel, [ Position( rts, posR[i] ), 1 ] );
                    if pos <> fail then break; fi;
                fi;
            od;
            
            cf:= rel[ pos+1];
            Unbind( rel[pos] ); Unbind( rel[pos+1] );
            rel:= Filtered( rel, x -> IsBound(x) );
            
            for k in [2,4..Length(rel)] do
                rel[k]:= -(1/cf)*rel[k];
            od;
            
            p1:= pair[1]; p2:= pair[2];
            
            Add( rel, [ pair[1], 1, pair[2], 1 ] );
            Add( rel, 1/cf );
            
            qa:=  _q^( -rts[k1]*( B*rts[k2] ) );
            Add( rel, [ pair[2], 1, pair[1], 1 ] );
            Add( rel, -qa/cf );
            
            # now `rel' is the `definition' of F_i (in terms of pbw
            # elts of lower level). We commute with all E_j.
            
            for j in [1..s] do
                
                expr:= [ ];
                pos:= Position( rts, posR[j] )+s+rank; # this is the index of E_j.
                for k in [1,3..Length(rel)-1] do
                    mon:= ShallowCopy( rel[k] );
                    Append( mon, [ pos, 1 ] );
                    Add( expr, mon ); Add( expr, -rel[k+1] );
                    mon:= [ pos, 1 ];
                    Append( mon, rel[k] );
                    Add( expr, mon ); Add( expr, rel[k+1] );
                od;
                
                # As above, we first collect without collecting F's or E's.
                # (Because this may result in an F, or an E of higher level.)

                cc:= collect( expr, false, false );

                cc:= collect( cc, true, true );

                Add( FEtab, [ [ pos, Position( rts, posR[i] ) ], 
                        cc ] );
                
            od;
        fi;
        
    od;
    
    return FEtab;
end;

# QuaGroup, chapter 3
#
# DO NOT EDIT THIS FILE - EDIT EXAMPLES IN THE SOURCE INSTEAD!
#
# This file has been generated by AutoDoc. It contains examples extracted from
# the package documentation. Each example is preceded by a comment which gives
# the name of a GAPDoc XML file and a line range from which the example were
# taken. Note that the XML file in turn may have been generated by AutoDoc
# from some other input.
#
gap> START_TEST("quagroup02.tst");

# doc/quagroup.xml:525-528
gap> QuantumField;
QuantumField

# doc/quagroup.xml:541-546
gap> _q;
q
gap> _q in QuantumField;
true

# doc/quagroup.xml:561-564
gap> GaussNumber( 4, _q );
q^3+q+q^-1+q^-3

# doc/quagroup.xml:573-578
gap> GaussianFactorial( 3, _q );
q^3+2*q+2*q^-1+q^-3
gap> GaussianFactorial( 3, _q^2 );
q^6+2*q^2+2*q^-2+q^-6

# doc/quagroup.xml:588-591
gap> GaussianBinomial( 5, 2, _q^2 );
q^12+q^8+2*q^4+2+2*q^-4+q^-8+q^-12

# doc/quagroup.xml:638-660
gap> R:=RootSystem( [ "B", 2, "F", 4, "E", 6 ] );
<root system of type B2 F4 E6>
gap> R:= RootSystem( "A", 2 );
<root system of type A2>
gap> PositiveRoots( R );
[ [ 1, 0 ], [ 0, 1 ], [ 1, 1 ] ]
gap> BilinearFormMat( R );
[ [ 2, -1 ], [ -1, 2 ] ]
gap> W:= WeylGroup( R );
Group([ [ [ -1, 1 ], [ 0, 1 ] ], [ [ 1, 0 ], [ 1, -1 ] ] ])
gap> ConjugateDominantWeight( W, [-3,2] );
[ 2, 1 ]
gap> o:= WeylOrbitIterator( W, [-3,2] );
<iterator>
gap> # Using the iterator we can loop over the orbit:
gap> NextIterator( o );
[ 2, 1 ]
gap> NextIterator( o );
[ -1, -2 ]
gap> PositiveRootsAsWeights( R );
[ [ 2, -1 ], [ -1, 2 ], [ 1, 1 ] ]

# doc/quagroup.xml:686-692
gap> R:= RootSystem( SimpleLieAlgebra( "B", 2, Rationals ) );;
gap> PositiveRootsNF( R );
[ [ 1, 0 ], [ 0, 1 ], [ 1, 1 ], [ 1, 2 ] ]
gap> # We note that in this case PositiveRoots( R ) will give the
gap> # positive roots in a different format.

# doc/quagroup.xml:720-724
gap> R:= RootSystem( "G", 2 );;
gap> PositiveRootsInConvexOrder( R );
[ [ 1, 0 ], [ 3, 1 ], [ 2, 1 ], [ 3, 2 ], [ 1, 1 ], [ 0, 1 ] ]

# doc/quagroup.xml:733-737
gap> R:= RootSystem( "A", 2 );;
gap> SimpleRootsAsWeights( R );
[ [ 2, -1 ], [ -1, 2 ] ]

# doc/quagroup.xml:763-767
gap> W:= WeylGroup( RootSystem( "G", 2 ) ) ;;
gap> ApplyWeylElement( W, [ -3, 7 ], [ 1, 1, 2, 1, 2 ] );
[ 15, -11 ]

# doc/quagroup.xml:777-782
gap> W:= WeylGroup( RootSystem( "F", 4 ) ) ;
<matrix group with 4 generators>
gap> LengthOfWeylWord( W, [ 1, 3, 2, 4, 2 ] );
3

# doc/quagroup.xml:807-811
gap> R:= RootSystem( "G", 2 );;
gap> LongestWeylWord( R );
[ 1, 2, 1, 2, 1, 2 ]

# doc/quagroup.xml:823-835
gap> R:= RootSystem( "F", 4 );;
gap> it:= ReducedWordIterator( WeylGroup(R), LongestWeylWord(R) );
<iterator>
gap> NextIterator( it );
[ 1, 2, 1, 3, 2, 1, 3, 2, 3, 4, 3, 2, 1, 3, 2, 3, 4, 3, 2, 1, 3, 2, 3, 4 ]
gap> k:= 1;;
gap> while not IsDoneIterator( it ) do
> k:= k+1; w:= NextIterator( it );
> od;
gap> k;
2144892

# doc/quagroup.xml:853-858
gap> R:= RootSystem( "G", 2 );;
gap> wd:= LongestWeylWord( R );;
gap> ExchangeElement( WeylGroup(R), wd, 1 );
[ 2, 1, 2, 1, 2 ]

# doc/quagroup.xml:881-888
gap> R:= RootSystem( "A", 3 );;
gap> wd1:= LongestWeylWord( R );
[ 1, 2, 1, 3, 2, 1 ]
gap> wd2:= [ 1, 3, 2, 1, 3, 2 ];;
gap> GetBraidRelations( WeylGroup(R), wd1, wd2 );
[ [ 3, 3, 4, 1 ], [ 4, 2, 5, 1, 6, 2 ], [ 2, 3, 3, 2, 4, 3 ], [ 4, 1, 5, 3 ] ]

# doc/quagroup.xml:903-911
gap> R:= RootSystem( "A", 3 );;
gap> LongWords( R )[3];
[ [ 3, 1, 2, 1, 3, 2 ], 
  [ [ 3, 3, 4, 1 ], [ 4, 2, 5, 1, 6, 2 ], [ 2, 3, 3, 2, 4, 3 ], 
      [ 4, 1, 5, 3 ], [ 1, 3, 2, 1 ] ], 
  [ [ 4, 3, 5, 1 ], [ 1, 1, 2, 3 ], [ 2, 2, 3, 3, 4, 2 ], 
      [ 4, 1, 5, 2, 6, 1 ], [ 3, 1, 4, 3 ] ] ]

# doc/quagroup.xml:958-986
gap> # We construct the generic quantized enveloping algebra corresponding
gap> # to the root system of type A2+G2:
gap> R:= RootSystem( [ "A", 2, "G", 2 ] );;
gap> U:= QuantizedUEA( R );
QuantumUEA( <root system of type A2 G2>, Qpar = q )
gap> RootSystem( U );
<root system of type A2 G2>
gap> g:= GeneratorsOfAlgebra( U );
[ F1, F2, F3, F4, F5, F6, F7, F8, F9, K1, (-q+q^-1)*[ K1 ; 1 ]+K1, K2, 
  (-q+q^-1)*[ K2 ; 1 ]+K2, K3, (-q+q^-1)*[ K3 ; 1 ]+K3, K4, 
  (-q^3+q^-3)*[ K4 ; 1 ]+K4, E1, E2, E3, E4, E5, E6, E7, E8, E9 ]
gap> # These elements generate a PBW-type basis of U; the nine elements Fi,
gap> # and the nine elements Ei correspond to the roots listed in convex order:
gap> PositiveRootsInConvexOrder( R );
[ [ 1, 0, 0, 0 ], [ 1, 1, 0, 0 ], [ 0, 1, 0, 0 ], [ 0, 0, 1, 0 ], 
  [ 0, 0, 3, 1 ], [ 0, 0, 2, 1 ], [ 0, 0, 3, 2 ], [ 0, 0, 1, 1 ], 
  [ 0, 0, 0, 1 ] ]
gap> # So, for example, F5 is an element of weight -[ 0, 0, 3, 1 ].
gap> # We can also multiply elements; the result is written on the PBW-basis:
gap> g[17]*g[4];
(-1+q^-6)*F4*[ K4 ; 1 ]+(q^-3)*F4*K4
gap> # Now we construct a non-generic quantized enveloping algebra:
gap> R:= RootSystem( "A", 2 );;
gap> U:= QuantizedUEA( R, CF(3), E(3) );;
gap> g:= GeneratorsOfAlgebra( U );
[ F1, F2, F3, K1, (-E(3)+E(3)^2)*[ K1 ; 1 ]+K1, K2, 
  (-E(3)+E(3)^2)*[ K2 ; 1 ]+K2, E1, E2, E3 ]

# doc/quagroup.xml:1028-1037
gap> U:= QuantizedUEA( RootSystem("A",2) );;
gap> fam:= ElementsFamily( FamilyObj( U ) );;
gap> list:= [ [ 2, 3, [ 4, 0 ], 8, 6, 11 ], _q^2,    # monomial and coefficient
> [ 1, 7, 3, 5, [ 5, 1 ], 3, 8, 9 ], _q^-1 + _q^2 ]; # monomial and coefficient
[ [ 2, 3, [ 4, 0 ], 8, 6, 11 ], q^2, [ 1, 7, 3, 5, [ 5, 1 ], 3, 8, 9 ], 
  q^2+q^-1 ]
gap> ObjByExtRep( fam, list );
(q^2)*F2^(3)*[ K1 ; 8 ]*E1^(11)+(q^2+q^-1)*F1^(7)*F3^(5)*K2[ K2 ; 3 ]*E3^(9)

# doc/quagroup.xml:1046-1053
gap> U:= QuantizedUEA( RootSystem("A",2) );;
gap> g:= GeneratorsOfAlgebra(U);
[ F1, F2, F3, K1, (-q+q^-1)*[ K1 ; 1 ]+K1, K2, (-q+q^-1)*[ K2 ; 1 ]+K2, E1, 
  E2, E3 ]
gap> ExtRepOfObj( g[5] );
[ [ [ 4, 0 ], 1 ], -q+q^-1, [ [ 4, 1 ], 0 ], 1 ]

# doc/quagroup.xml:1062-1067
gap> R:= RootSystem("A",2);;
gap> U0:= QuantizedUEA( R, CF(3), E(3) );;
gap> QuantumParameter( U0 );
E(3)

# doc/quagroup.xml:1079-1093
gap> R:= RootSystem("A", 3 );;
gap> U:= QuantizedUEA( R, CF(5), E(5) );;
gap> f:= CanonicalMapping( U );
MappingByFunction( QuantumUEA( <root system of type A
3>, Qpar = q ), QuantumUEA( <root system of type A3>, Qpar = 
E(5) ), function( u ) ... end )
gap> U0:= Source( f );
QuantumUEA( <root system of type A3>, Qpar = q )
gap> g:= GeneratorsOfAlgebra( U0 );;
gap> u:= g[18]*g[9]*g[6];
(q^2)*F6*K2*E6+(q)*K2*[ K3 ; 1 ]
gap> Image( f, u );
(E(5)^2)*F6*K2*E6+(E(5))*K2*[ K3 ; 1 ]

# doc/quagroup.xml:1103-1106
gap> U:= QuantizedUEA( RootSystem("A",3) );;
gap> WriteQEAToFile( U, "A3" );

# doc/quagroup.xml:1116-1121
gap> U:= QuantizedUEA( RootSystem("A",3) );;
gap> WriteQEAToFile( U, "A3" );
gap> U0:= ReadQEAFromFile( "A3" );
QuantumUEA( <root system of type A3>, Qpar = q )

# doc/quagroup.xml:1152-1179
gap> R:= RootSystem( "G", 2 );;
gap> SetLongestWeylWord( R, [1,2,1,2,1,2] );
gap> UR:= QuantizedUEA( R );;
gap> S:= RootSystem( "G", 2 );;
gap> SetLongestWeylWord( S, [2,1,2,1,2,1] );
gap> US:= QuantizedUEA( S );;
gap> gS:= GeneratorsOfAlgebra( US );
[ F1, F2, F3, F4, F5, F6, K1, (-q+q^-1)*[ K1 ; 1 ]+K1, K2, 
  (-q^3+q^-3)*[ K2 ; 1 ]+K2, E1, E2, E3, E4, E5, E6 ]
gap> SimpleSystem( R );
[ [ 1, 0 ], [ 0, 1 ] ]
gap> PositiveRootsInConvexOrder( S );
[ [ 0, 1 ], [ 1, 1 ], [ 3, 2 ], [ 2, 1 ], [ 3, 1 ], [ 1, 0 ] ]
gap> # We see that the simple roots of R occur on positions 6 and 1
gap> # in the list PositiveRootsInConvexOrder( S ); This means that we
gap> # get the following list of images of the homomorphism:
gap> imgs:= [ gS[6], gS[1],      # the images of the F_{\alpha}
> gS[7], gS[9],                  # the images of the K_{\alpha}
> gS[8], gS[10],                 # the images of the K_{\alpha}^{-1}
> gS[16], gS[11] ];              # the images of the E_{\alpha}
[ F6, F1, K1, K2, (-q+q^-1)*[ K1 ; 1 ]+K1, (-q^3+q^-3)*[ K2 ; 1 ]+K2, E6, E1 ]
gap> h:= QEAHomomorphism( UR, US, imgs );
<homomorphism: QuantumUEA( <root system of type G
2>, Qpar = q ) -> QuantumUEA( <root system of type G2>, Qpar = q )>
gap> Image( h, GeneratorsOfAlgebra( UR )[3] );
(q^10-q^6-q^4+1)*F1*F6^(2)+(q^6-q^2)*F2*F6+(q^4)*F4

# doc/quagroup.xml:1215-1249
gap> # First we construct the quantized enveloping algebra:
gap> R:= RootSystem( "A", 3 );;
gap> U0:= QuantizedUEA( R );
QuantumUEA( <root system of type A3>, Qpar = q )
gap> g:= GeneratorsOfAlgebra( U0 );
[ F1, F2, F3, F4, F5, F6, K1, (-q+q^-1)*[ K1 ; 1 ]+K1, K2, 
  (-q+q^-1)*[ K2 ; 1 ]+K2, K3, (-q+q^-1)*[ K3 ; 1 ]+K3, E1, E2, E3, E4, E5, 
  E6 ]
gap> # Now, for instance, we map F_{\alpha} to E_{\alpha}, where \alpha
gap> # is a simple root. In order to find where those F_{\alpha}, E_{\alpha}
gap> # are in the list of generators, we look at the list of positive roots
gap> # in convex order:
gap> PositiveRootsInConvexOrder( R );
[ [ 1, 0, 0 ], [ 1, 1, 0 ], [ 0, 1, 0 ], [ 1, 1, 1 ], [ 0, 1, 1 ], 
  [ 0, 0, 1 ] ]
gap> # So the simple roots occur on positions 1, 3, 6. This means that we
gap> # have the following list of images:
gap> imgs:= [ g[13], g[15], g[18], g[8], g[10], g[12], g[7], g[9], g[11], 
> g[1], g[3], g[6] ];
[ E1, E3, E6, (-q+q^-1)*[ K1 ; 1 ]+K1, (-q+q^-1)*[ K2 ; 1 ]+K2, 
  (-q+q^-1)*[ K3 ; 1 ]+K3, K1, K2, K3, F1, F3, F6 ]
gap> f:= QEAAutomorphism( U0, imgs );
<automorphism of QuantumUEA( <root system of type A3>, Qpar = q )>
gap> Image( f, g[2] );
(-q)*E2
gap> # f induces an automorphism of any non-generic quantized enveloping
gap> # algebra with the same root system R:
gap> U1:= QuantizedUEA( R, CF(5), E(5) );
QuantumUEA( <root system of type A3>, Qpar = E(5) )
gap> h:= QEAAutomorphism( U1, f );
<automorphism of QuantumUEA( <root system of type A3>, Qpar = E(5) )>
gap> Image( h, GeneratorsOfAlgebra(U1)[7] );
(-E(5)+E(5)^4)*[ K1 ; 1 ]+K1

# doc/quagroup.xml:1267-1273
gap> R:= RootSystem( "A", 3 );;
gap> U:= QuantizedUEA( R, CF(5), E(5) );
QuantumUEA( <root system of type A3>, Qpar = E(5) )
gap> f:= AutomorphismOmega( U );
<automorphism of QuantumUEA( <root system of type A3>, Qpar = E(5) )>

# doc/quagroup.xml:1281-1287
gap> R:= RootSystem( "A", 3 );;
gap> U:= QuantizedUEA( R, CF(5), E(5) );
QuantumUEA( <root system of type A3>, Qpar = E(5) )
gap> t:= AntiAutomorphismTau( U );
<anti-automorphism of QuantumUEA( <root system of type A3>, Qpar = E(5) )>

# doc/quagroup.xml:1297-1303
gap> U:= QuantizedUEA( RootSystem(["A",2,"B",2]) );;
gap> bar:= BarAutomorphism( U );
<automorphism of QuantumUEA( <root system of type A2 B2>, Qpar = q )>
gap> Image( bar, GeneratorsOfAlgebra( U )[5] );
(q^2-q^-2)*F4*F7+F5

# doc/quagroup.xml:1312-1320
gap> U:= QuantizedUEA( RootSystem( "B", 3 ) );;
gap> f:=AutomorphismTalpha( U, 1 );
<automorphism of QuantumUEA( <root system of type B3>, Qpar = q )>
gap> a:= GeneratorsOfAlgebra( U )[3];
F3
gap>  Image( f, a );
F2

# doc/quagroup.xml:1334-1345
gap> R:= RootSystem( "A", 3 );;
gap> U:= QuantizedUEA( R );;
gap> f:= DiagramAutomorphism( U, (1,3) );
<automorphism of QuantumUEA( <root system of type A3>, Qpar = q )>
gap> g:= GeneratorsOfAlgebra( U );
[ F1, F2, F3, F4, F5, F6, K1, (-q+q^-1)*[ K1 ; 1 ]+K1, K2, 
  (-q+q^-1)*[ K2 ; 1 ]+K2, K3, (-q+q^-1)*[ K3 ; 1 ]+K3, E1, E2, E3, E4, E5, 
  E6 ]
gap> Image( f, g[1] );
F6

# doc/quagroup.xml:1358-1375
gap> U:= QuantizedUEA( RootSystem( "B", 3 ) );;
gap> f:=AutomorphismTalpha( U, 1 );
<automorphism of QuantumUEA( <root system of type B3>, Qpar = q )>
gap> h:= AutomorphismOmega( U );
<automorphism of QuantumUEA( <root system of type B3>, Qpar = q )>
gap> f*h;
<automorphism of QuantumUEA( <root system of type B3>, Qpar = q )>
gap> t:= AntiAutomorphismTau( U );;
gap> T:= AutomorphismTalpha( U, 2 );;
gap> Tinv:= t*T*t;
<automorphism of QuantumUEA( <root system of type B3>, Qpar = q )>
gap> # (The last call may take a little while.)
gap> x:= Image( T, GeneratorsOfAlgebra( U )[1] );
(-q^4+1)*F1*F3+(-q^2)*F2
gap> Image( Tinv, x );
F1

# doc/quagroup.xml:1398-1409
gap> U:= QuantizedUEA( RootSystem( [ "B", 2 ] ) );;
gap> T:= TensorPower( U, 3 );
<algebra over QuantumField, with 36 generators>
gap> g:= GeneratorsOfAlgebra( T );;
gap> x:= g[1];
1*(1<x>1<x>F1)
gap> y:= g[30];
1*(E2<x>1<x>1)
gap> x*y;
1*(E2<x>1<x>F1)

# doc/quagroup.xml:1423-1427
gap> U:= QuantizedUEA( RootSystem("A",2), CF(5), E(5) );;
gap> t:= AntiAutomorphismTau( U );;
gap> UseTwistedHopfStructure( U, t, t );

# doc/quagroup.xml:1439-1446
gap> U:= QuantizedUEA( RootSystem("A",2), CF(5), E(5) );;
gap> D:= ComultiplicationMap( U, 3 );
<Comultiplication of QuantumUEA( <root system of type A2>, Qpar = 
E(5) ), degree 3>
gap> Image( D, GeneratorsOfAlgebra(U)[4] );
1*(K1<x>K1<x>K1)

# doc/quagroup.xml:1456-1460
gap> U:= QuantizedUEA( RootSystem("A",2), CF(5), E(5) );;
gap> a:= AntipodeMap( U );
<anti-automorphism of QuantumUEA( <root system of type A2>, Qpar = E(5) )>

# doc/quagroup.xml:1470-1478
gap> U:= QuantizedUEA( RootSystem("A",2), CF(5), E(5) );;
gap> co:= CounitMap( U );
function( u ) ... end
gap> x:= GeneratorsOfAlgebra( U )[4];
K1
gap> co( x );
1

# doc/quagroup.xml:1511-1526
gap> U:= QuantizedUEA( RootSystem( [ "A", 2, "G", 2 ] ) );;
gap> V:= HighestWeightModule( U, [ 0, 1, 0, 2 ] );
<231-dimensional left-module over QuantumUEA( <root system of type A2 G
2>, Qpar = q )>
gap> Basis( V )[1];
1*v0
gap> Basis(V)[23]+(_q^2+_q^-2)*Basis(V)[137];
F3*F5*v0+(q^2+q^-2)*F8^(6)*v0
gap> # We compute the action of an element on a vector:
gap> gg:= GeneratorsOfAlgebra( U );;
gap> x:= gg[21]*gg[5];
F5*E4+(-q^-1)*F6*K3
gap> x^Basis(V)[1];
(-q^-1)*F6*v0

# doc/quagroup.xml:1537-1546
gap> R:= RootSystem( "A", 2 );;
gap> U:= QuantizedUEA( R, CF(3), E(3) );;
gap> V:= HighestWeightModule( U, [1,1] );
<8-dimensional left-module over QuantumUEA( <root system of type A2>, Qpar = 
E(3) )>
gap> IrreducibleQuotient( V );
<7-dimensional left-module over QuantumUEA( <root system of type A2>, Qpar = 
E(3) )>

# doc/quagroup.xml:1561-1567
gap> U:= QuantizedUEA( RootSystem("G",2) );;
gap> V:= HWModuleByTensorProduct( U, [2,1] );
<189-dimensional left-module over QuantumUEA( <root system of type G
2>, Qpar = q )>
gap> # (This is a case where this algorithm is a lot faster.)

# doc/quagroup.xml:1594-1606
gap> U:= QuantizedUEA( RootSystem("A",1) );
QuantumUEA( <root system of type A1>, Qpar = q )
gap> V:= QuantumField^2;
( QuantumField^2 )
gap> v:= BasisVectors( Basis(V) );
[ [ 1, 0 ], [ 0, 1 ] ]
gap> acts:= [ [ v[2], 0*v[1] ], [ _q*v[1], _q^-1*v[2] ], 
> [ _q^-1*v[1], _q*v[2] ], [ 0*v[1], v[1] ] ];;
gap> M:= DIYModule( U, V, acts );
<2-dimensional left-module over QuantumUEA( <root system of type A
1>, Qpar = q )>

# doc/quagroup.xml:1621-1628
gap> U:= QuantizedUEA( RootSystem( [ "A", 2 ] ) );;
gap> V1:= HighestWeightModule( U, [ 1, 0 ] );;
gap> V2:= HighestWeightModule( U, [ 0, 1 ] );;
gap> TensorProductOfAlgebraModules( V1, V2 );
<9-dimensional left-module over QuantumUEA( <root system of type A
2>, Qpar = q )>

# doc/quagroup.xml:1640-1650
gap> U:= QuantizedUEA( RootSystem("B",2) );;
gap> W1:= HighestWeightModule( U, [1,0] );;
gap> W2:= HighestWeightModule( U, [0,1] );;
gap> T:= TensorProductOfAlgebraModules( W1, W2 );
<20-dimensional left-module over QuantumUEA( <root system of type B
2>, Qpar = q )>
gap> HWModuleByGenerator( T, Basis(T)[1], [1,1] );
<16-dimensional left-module over QuantumUEA( <root system of type B
2>, Qpar = q )>

# doc/quagroup.xml:1662-1672
gap> R:= RootSystem("B",2);;
gap> U:= QuantizedUEA( R );;
gap> U0:= QuantizedUEA( R, CF(3), E(3) );;
gap> V:= HighestWeightModule( U, [1,1] );;
gap> W:= InducedQEAModule( U0, V );
<16-dimensional left-module over QuantumUEA( <root system of type B2>, Qpar = 
E(3) )>
gap> # This module is isomorphic to the one obtained by
gap> # HighestWeightModule( U0, [1,1] );

# doc/quagroup.xml:1691-1705
gap> R:= RootSystem("B",2);;
gap> U:= QuantizedUEA( R );;
gap> U0:= QuantizedUEA( R, CF(3), E(3) );;
gap> V:= HighestWeightModule( U, [1,1] );;
gap> W:= InducedQEAModule( U0, V );;
gap> f:= CanonicalMapping( W );
MappingByFunction( <
16-dimensional left-module over QuantumUEA( <root system of type B
2>, Qpar = q )>, <
16-dimensional left-module over QuantumUEA( <root system of type B2>, Qpar = 
E(3) )>, function( v ) ... end )
gap> Image( f, _q^2*Basis(V)[3] );
(E(3)^2)*e.3

# doc/quagroup.xml:1717-1722
gap> U:= QuantizedUEA( RootSystem("A",2) );;
gap> A2Module( U, [4,7] );
<260-dimensional left-module over QuantumUEA( <root system of type A
2>, Qpar = q )>

# doc/quagroup.xml:1734-1739
gap> U:= QuantizedUEA( RootSystem("A",5) );;
gap> MinusculeModule( U, [0,0,1,0,0] );
<20-dimensional left-module over QuantumUEA( <root system of type A
5>, Qpar = q )>

# doc/quagroup.xml:1761-1783
gap> U:= QuantizedUEA( RootSystem("A",2) );;
gap> V:= HighestWeightModule( U, [1,1] );;
gap> M:= DualAlgebraModule( V );
<8-dimensional left-module over QuantumUEA( <root system of type A
2>, Qpar = q )>
gap> u:= GeneratorsOfAlgebra( U )[2];
F2
gap> vv:= BasisVectors( Basis( M ) );
[ (1)*F@1*v0, (1)*F@F1*v0, (1)*F@F3*v0, (1)*F@F1*F3*v0, (1)*F@F2*v0, 
  (1)*F@F1*F2*v0, (1)*F@F2*F3*v0, (1)*F@F2^(2)*v0 ]
gap> u^vv[3];
<zero function>
gap> # (The zero of the dual space is printed as <zero function>).
gap> u^vv[4];
(-q^5+q^3)*F@1*v0
gap> # We get the function corresponding to a vector in M by using ExtRepOfObj:
gap> f:= ExtRepOfObj( vv[1] );
(1)*F@1*v0
gap> # We can calculate images of this function:
gap> List( Basis(V), v -> Image( f, v ) );
[ 1, 0, 0, 0, 0, 0, 0, 0 ]

# doc/quagroup.xml:1792-1796
gap> U:= QuantizedUEA( RootSystem("A",2) );;
gap> V:= TrivialAlgebraModule( U );
<left-module over QuantumUEA( <root system of type A2>, Qpar = q )>

# doc/quagroup.xml:1815-1823
gap> U:= QuantizedUEA( RootSystem( "A", 2 ) );;
gap> V:= HighestWeightModule( U, [ 1, 1 ] );;
gap> WeightsAndVectors( V );
[ [ [ 1, 1 ], [ -1, 2 ], [ 2, -1 ], [ 0, 0 ], [ -2, 1 ], [ 1, -2 ], 
      [ -1, -1 ] ], 
  [ [ 1*v0 ], [ F1*v0 ], [ F3*v0 ], [ F1*F3*v0, F2*v0 ], [ F1*F2*v0 ], 
      [ F2*F3*v0 ], [ F2^(2)*v0 ] ] ]

# doc/quagroup.xml:1835-1840
gap> U:= QuantizedUEA( RootSystem( [ "A", 2 ] ) );;
gap> V:= HighestWeightModule( U, [ 1, 1 ] );;
gap> HighestWeightsAndVectors( V );
[ [ [ 1, 1 ] ], [ [ 1*v0 ] ] ]

# doc/quagroup.xml:1857-1862
gap> U:= QuantizedUEA( RootSystem("A",1) );;
gap> V:= HighestWeightModule( U, [1] );;
gap> RMatrix( V );
[ [ 1, 0, 0, 0 ], [ 0, q, -q^2+1, 0 ], [ 0, 0, q, 0 ], [ 0, 0, 0, 1 ] ]

# doc/quagroup.xml:1878-1888
gap> U:= QuantizedUEA( RootSystem("B",2) );;
gap> V:= HighestWeightModule( U, [1,0] );;
gap> W:= HighestWeightModule( U, [0,1] );;
gap> h:= IsomorphismOfTensorModules( V, W );;
gap> VW:= Source( h );
<20-dimensional left-module over QuantumUEA( <root system of type B
2>, Qpar = q )>
gap> Image( h, Basis(VW)[13] );
q*(1*v0<x>F3*v0)+-q^2+1*(F4*v0<x>F2*v0)+-q^3+q^-1*(F3*v0<x>1*v0)

# doc/quagroup.xml:1915-1922
gap> U:= QuantizedUEA( RootSystem("A",3) );;
gap> V:= HighestWeightModule( U, [1,1,1] );;
gap> WriteModuleToFile( V, "A3mod" );
gap> W:= ReadModuleFromFile( "A3mod" );
<64-dimensional left-module over QuantumUEA( <root system of type A
3>, Qpar = q )>

# doc/quagroup.xml:1940-1944
gap> R:= RootSystem( "G", 2 );;
gap> DominantLSPath( R, [1,3] );
<LS path of shape [ 1, 3 ] ending in [ 1, 3 ] >

# doc/quagroup.xml:1955-1962
gap> R:= RootSystem( "G", 2 );;
gap> p:=DominantLSPath( R, [1,3] );;
gap> p1:=Falpha( p, 1 );
<LS path of shape [ 1, 3 ] ending in [ -1, 4 ] >
gap> Falpha( p1, 1 );
fail

# doc/quagroup.xml:1973-1981
gap> R:= RootSystem( "G", 2 );;
gap> p:=DominantLSPath( R, [1,3] );;
gap> Ealpha( p, 2 );
fail
gap> p1:=Falpha( p, 1 );;
gap> Ealpha( p1, 1 );
<LS path of shape [ 1, 3 ] ending in [ 1, 3 ] >

# doc/quagroup.xml:1990-1996
gap> R:= RootSystem( "G", 2 );;
gap> p:=DominantLSPath( R, [1,3] );;
gap> p1:= Falpha( Falpha( p, 1 ), 2 );;
gap> LSSequence( p1 );
[ [ [ 11, -4 ], [ -1, 4 ] ], [ 0, 1/4, 1 ] ]

# doc/quagroup.xml:2008-2014
gap> R:= RootSystem( "G", 2 );;
gap> p:=DominantLSPath( R, [1,3] );;
gap> p1:= Falpha( Falpha( Falpha( p, 1 ), 2 ), 1 );;
gap> WeylWord( p1 );
[ 1, 2, 1 ]

# doc/quagroup.xml:2023-2029
gap> R:= RootSystem( "G", 2 );;
gap> p:=DominantLSPath( R, [1,3] );;
gap> p1:= Falpha( Falpha( Falpha( p, 1 ), 2 ), 1 );;
gap> EndWeight( p1 );
[ 0, 3 ]

# doc/quagroup.xml:2046-2061
gap> R:= RootSystem( "A", 2 );;
gap> CrystalGraph( R, [1,1] );
rec( 
  edges := [ [ [ 1, 2 ], 1 ], [ [ 1, 3 ], 2 ], [ [ 2, 4 ], 2 ], 
      [ [ 3, 5 ], 1 ], [ [ 4, 6 ], 2 ], [ [ 5, 7 ], 1 ], [ [ 6, 8 ], 1 ], 
      [ [ 7, 8 ], 2 ] ], 
  points := [ <LS path of shape [ 1, 1 ] ending in [ 1, 1 ] >, 
      <LS path of shape [ 1, 1 ] ending in [ -1, 2 ] >, 
      <LS path of shape [ 1, 1 ] ending in [ 2, -1 ] >, 
      <LS path of shape [ 1, 1 ] ending in [ 0, 0 ] >, 
      <LS path of shape [ 1, 1 ] ending in [ 0, 0 ] >, 
      <LS path of shape [ 1, 1 ] ending in [ 1, -2 ] >, 
      <LS path of shape [ 1, 1 ] ending in [ -2, 1 ] >, 
      <LS path of shape [ 1, 1 ] ending in [ -1, -1 ] > ] )

# doc/quagroup.xml:2079-2085
gap> U:= QuantizedUEA( RootSystem( "F", 4 ) );;
gap> x:= One( U );
1
gap> Falpha( Falpha( x, 3 ), 2 );
F3*F9

# doc/quagroup.xml:2100-2109
gap> U:= QuantizedUEA( RootSystem( "F", 4 ) );;
gap> Ealpha( One( U ), 2 );
fail
gap> g:= GeneratorsOfAlgebra( U );;
gap> x:= g[1]*g[4]*g[7]*g[17];
F1*F4*F7*F17
gap> Ealpha( x, 3 );
F1*F2*F7*F17

# doc/quagroup.xml:2122-2126
gap> U:= QuantizedUEA( RootSystem( "F", 4 ) );;
gap> B:= CanonicalBasis( U );
<canonical basis of QuantumUEA( <root system of type F4>, Qpar = q ) >

# doc/quagroup.xml:2142-2155
gap> U:= QuantizedUEA( RootSystem( "F", 4 ) );;
gap> B:= CanonicalBasis( U );;
gap> PBWElements( B, [1,2,1,0] );
[ F1*F3^(2)*F9, F1*F3*F7+(q^4)*F1*F3^(2)*F9, (q^4)*F1*F3^(2)*F9+F2*F3*F9, 
  (q^2)*F1*F3*F7+(q^6+q^2)*F1*F3^(2)*F9+(q^2)*F2*F3*F9+F2*F7, 
  (q^4)*F1*F3*F7+(q^8)*F1*F3^(2)*F9+(q^4)*F2*F3*F9+(q^2)*F2*F7+F3*F4 ]
gap> U:= QuantizedUEA( RootSystem("G",2) );;
gap> B:= CanonicalBasis( U );;
gap> PBWElements( B, [2,3] : lowrank );
[ F1^(2)*F6^(3), F1*F5*F6^(2)+(q^10+q^8)*F1^(2)*F6^(3), 
  (q^2)*F1*F5*F6^(2)+(q^12+q^6)*F1^(2)*F6^(3)+F3*F6^(2), 
  (q^8)*F1*F5*F6^(2)+(q^18)*F1^(2)*F6^(3)+(q^6)*F3*F6^(2)+F5^(2)*F6 ]

# doc/quagroup.xml:2168-2174
gap> U:= QuantizedUEA( RootSystem( "F", 4 ) );;
gap> B:= CanonicalBasis( U );;
gap> MonomialElements( B, [1,2,1,0] );
[ F1*F3^(2)*F9, F1*F3*F9*F3+(-1)*F1*F3^(2)*F9, F3^(2)*F1*F9, F3*F1*F9*F3, 
  F3*F9*F3*F1+(-1)*F3^(2)*F1*F9 ]

# doc/quagroup.xml:2192-2202
gap> U:= QuantizedUEA( RootSystem( "F", 4 ) );;
gap> B:= CanonicalBasis( U );;
gap> Strings( B, [1,2,1,0] );
[ [ 1, 1, 2, 2, 3, 1 ], [ 1, 1, 2, 1, 3, 1, 2, 1 ], [ 2, 2, 1, 1, 3, 1 ], 
  [ 2, 1, 1, 1, 3, 1, 2, 1 ], [ 2, 1, 3, 1, 2, 1, 1, 1 ] ]
gap> Falpha( Falpha( Falpha( Falpha( One(U), 3 ), 1 ), 2 ), 2 );
F2*F3*F9
gap> PBWElements( B, [1,2,1,0] )[3];
(q^4)*F1*F3^(2)*F9+F2*F3*F9

# doc/quagroup.xml:2211-2219
gap> U:= QuantizedUEA( RootSystem("G",2) );;
gap> B:= CanonicalBasis( U );;
gap> p:= PBWElements( B, [4,4] : lowrank )[4];
(q^9)*F1^(2)*F3*F6^(3)+F1^(2)*F5^(2)*F6^(2)+(q^13+q^11+q^9)*F1^(3)*F5*F6^(
3)+(q^28+q^26+2*q^24+q^22+q^20)*F1^(4)*F6^(4)
gap> PrincipalMonomial( p );
F1^(2)*F5^(2)*F6^(2)

# doc/quagroup.xml:2230-2240
gap> U:= QuantizedUEA( RootSystem("G",2) );;
gap> B:= CanonicalBasis( U );;
gap> p:= PBWElements( B, [1,2] : lowrank )[2];;
gap> m:=PrincipalMonomial( p );
F5*F6
gap> StringMonomial( m );
[ 2, 2, 1, 1 ]
gap> Falpha( Falpha( Falpha( One(U), 1 ), 2 ), 2 );
F5*F6

# doc/quagroup.xml:2254-2259
gap> U:= QuantizedUEA( RootSystem("B",2) );;
gap> V:= HighestWeightModule( U, [1,1] );;
gap> Falpha( V, Basis(V)[1], 1 );
F1*v0

# doc/quagroup.xml:2273-2280
gap> U:= QuantizedUEA( RootSystem("B",2) );;
gap> V:= HighestWeightModule( U, [1,1] );;
gap> v:= Falpha( V, Basis(V)[2], 2 );
(q^2)*F1*F4*v0+F2*v0
gap> Ealpha( V, v, 2 );
F1*v0

# doc/quagroup.xml:2292-2304
gap> U:= QuantizedUEA( RootSystem( "B", 2 ) );;
gap> V:= HighestWeightModule( U, [1,1] );
<16-dimensional left-module over QuantumUEA( <root system of type B
2>, Qpar = q )>
gap>  CrystalBasis( V );
Basis( <16-dimensional left-module over QuantumUEA( <root system of type B
2>, Qpar = q )>, [ 1*v0, F1*v0, F4*v0, F1*F4*v0, (q^2)*F1*F4*v0+F2*v0, 
  F2*F4*v0, (q)*F2*F4*v0+F3*v0, (-q^-4)*F1*F2*v0, 
  (-q^-1)*F1*F3*v0+(-q^-3)*F2^(2)*v0, (-q^-2)*F2^(2)*v0, F3*F4*v0, 
  (-q^-4)*F2*F3*v0+(-q^-2)*F2^(2)*F4*v0, (-q^-2)*F2*F3*v0, (q^-4)*F2^(3)*v0, 
  (-q^-1)*F3^(2)*v0, (q^-5)*F2^(2)*F3*v0 ] )

# doc/quagroup.xml:2321-2331
gap> U:= QuantizedUEA( RootSystem( "B", 2 ) );;
gap> V:= HighestWeightModule( U, [1,1] );
<16-dimensional left-module over QuantumUEA( <root system of type B
2>, Qpar = q )>
gap> CrystalVectors( V );
[ <1*v0>, <F1*v0>, <F4*v0>, <F2*v0>, <F1*F4*v0>, <F3*v0>, <(-q^-4)*F1*F2*v0>, 
  <F2*F4*v0>, <F1*F3*v0>, <F3*F4*v0>, <(-q^-1)*F1*F3*v0+(-q^-3)*F2^(2)*v0>, 
  <(-q^-4)*F2*F3*v0+(-q^-2)*F2^(2)*F4*v0>, <F2^(2)*F4*v0>, <(q^-4)*F2^(3)*v0>,
  <(-q^-1)*F3^(2)*v0>, <(q^-5)*F2^(2)*F3*v0> ]

# doc/quagroup.xml:2344-2358
gap> U:= QuantizedUEA( RootSystem( "B", 2 ) );;
gap> V:= HighestWeightModule( U, [1,1] );;
gap> c:=CrystalVectors( V );;
gap> Falpha( c[2], 2 );
<F2*v0>
gap> Falpha( c[3], 2 );
fail
gap> Falpha( Falpha( Falpha( c[1], 1 ), 2 ), 1 );
fail
gap> p:= DominantLSPath( RootSystem( "B", 2 ), [1,1] );
<LS path of shape [ 1, 1 ] ending in [ 1, 1 ] >
gap> Falpha( Falpha( Falpha( p, 1 ), 2 ), 1 );
fail

# doc/quagroup.xml:2374-2382
gap> U:= QuantizedUEA( RootSystem( "B", 2 ) );;
gap> V:= HighestWeightModule( U, [1,1] );;
gap> c:=CrystalVectors( V );;
gap> Ealpha( c[3], 1 );
fail
gap> Ealpha( c[3], 2 );
<1*v0>

# doc/quagroup.xml:2392-2407
gap> U:= QuantizedUEA( RootSystem("A",2) );;
gap> V1:= HighestWeightModule( U, [1,0] );;
gap> V2:= HighestWeightModule( U, [0,1] );;
gap> W:= TensorProductOfAlgebraModules( V1, V2 );;
gap> CrystalGraph( W );
rec( 
  edges := [ [ [ 1, 2 ], 1 ], [ [ 1, 3 ], 2 ], [ [ 2, 4 ], 2 ], 
      [ [ 3, 5 ], 1 ], [ [ 4, 6 ], 2 ], [ [ 5, 7 ], 1 ], [ [ 6, 8 ], 1 ], 
      [ [ 7, 8 ], 2 ] ], 
  points := [ <1*(1*v0<x>1*v0)>, <1*(F1*v0<x>1*v0)>, <1*(1*v0<x>F3*v0)>, 
      <1*(1*v0<x>F2*v0)+q^-1*(F2*v0<x>1*v0)>, 
      <-q^-1*(1*v0<x>F2*v0)+q^-1*(F1*v0<x>F3*v0)>, <1*(F2*v0<x>F3*v0)>, 
      <-q^-1*(F1*v0<x>F2*v0)>, <-q^-1*(F2*v0<x>F2*v0)>, 
      <-q^-3*(1*v0<x>F2*v0)+-q^-1*(F1*v0<x>F3*v0)+1*(F2*v0<x>1*v0)> ] )

# doc/quagroup.xml:2425-2432
gap> L:= SimpleLieAlgebra( "B", 2, Rationals );
<Lie algebra of dimension 10 over Rationals>
gap> u:= UEA( L );
<algebra over Rationals, with 10 generators>
gap> g:= GeneratorsOfAlgebra( u );
[ y1, y2, y3, y4, x1, x2, x3, x4, ( h9/1 ), ( h10/1 ) ]

# doc/quagroup.xml:2441-2446
gap> L:= SimpleLieAlgebra( "B", 2, Rationals );;
gap> u:= UEA( L );;
gap> UnderlyingLieAlgebra( u );
<Lie algebra of dimension 10 over Rationals>

# doc/quagroup.xml:2458-2464
gap> L:= SimpleLieAlgebra( "B", 2, Rationals );;
gap> u:= UEA( L );;
gap> HighestWeightModule( u, [2,3] );
<140-dimensional left-module over <algebra over Rationals, with 
10 generators>>

# doc/quagroup.xml:2481-2501
gap> L:= SimpleLieAlgebra( "B", 2, Rationals );;
gap> f:= QUEAToUEAMap( L );
<mapping: QuantumUEA( <root system of rank 
2>, Qpar = q ) -> Algebra( Rationals, [ y1, y2, y3, y4, x1, x2, x3, x4, 
  ( h9/1 ), ( h10/1 ) ] ) >
gap> U:= Source( f );
QuantumUEA( <root system of rank 2>, Qpar = q )
gap> u:= Range( f );
<algebra over Rationals, with 10 generators>
gap> B:= CanonicalBasis( U );;
gap> p:= PBWElements( B, [1,2] );
[ F1*F4^(2), (q^3+q)*F1*F4^(2)+F2*F4, (q^4)*F1*F4^(2)+(q)*F2*F4+F3 ]
gap> pu:= List( p, x -> Image( f, x ) );
[ y1*y2^(2), 2*y1*y2^(2)+y2*y3-2*y4, y1*y2^(2)+y2*y3-1*y4 ]
gap> V:= HighestWeightModule( u, [2,1] );
<40-dimensional left-module over <algebra over Rationals, with 10 generators>>
gap> List( pu, x -> x^Basis(V)[1] );
[ 0*v0, y2*y3*v0-2*y4*v0, y2*y3*v0-1*y4*v0 ]
gap> # Which gives us a piece of the canonical basis of V.

#
gap> STOP_TEST("quagroup02.tst", 1);

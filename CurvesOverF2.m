// Table 3, introductory paragraph of Section 11.2.
// Enumerate the F2 models and the origin-preserving automorphisms.
// All coordinates, point counts and group computations are exact.

k<w> := GF(4);
assert w^2+w+1 eq 0;
k2 := [k | 0,1];
R<X,Y> := PolynomialRing(k,2);
equations := [
    Y^2+Y+X^3+X,       // E1
    Y^2+X*Y+X^3+1,     // E2
    Y^2+Y+X^3,         // E3
    Y^2+X*Y+Y+X^3+1,   // E4
    Y^2+Y+X^3+X+1      // E5
];
traces := [-2,-1,0,1,2];
orders2 := [4,2,2,2,4];
orders4 := [4,2,24,2,4];
I3 := IdentityMatrix(k,3);
covered := 0;
autE3 := [MatrixAlgebra(k,3) | ];
for i in [1..5] do
    C := equations[i];
    points := 1;       // the point at infinity
    for x,y in k2 do
        if Evaluate(C,[x,y]) eq 0 then
            points +:= 1;
        end if;
    end for;
    assert 3-points eq traces[i];

    // Every origin-preserving isomorphism between Weierstrass models
    // has the form (X,Y) |-> (u^2*X+r, u^3*Y+s*u^2*X+t).
    over4 := [MatrixAlgebra(k,3) | ];
    over2 := [MatrixAlgebra(k,3) | ];
    for u in [k | 1,w,w^2] do
        for r,s,t in k do
            Xnew := u^2*X+r;
            Ynew := u^3*Y+s*u^2*X+t;
            if Evaluate(C,[Xnew,Ynew]) eq u^6*C then
                M := Matrix(k,3,3,[u^2,0,r, s*u^2,u^3,t, 0,0,1]);
                Append(~over4,M);
                if u in k2 and r in k2 and s in k2 and t in k2 then
                    Append(~over2,M);
                end if;
            end if;
        end for;
    end for;
    assert #over2 eq orders2[i] and #over4 eq orders4[i];
    if i eq 1 or i eq 5 then
        assert exists{M : M in over2 | M^2 ne I3 and M^4 eq I3};
        // The generator over F2 also has order four over F4.
    end if;
    if i eq 3 then
        autE3 := over4;
    end if;
    // There are eight F2 coordinate changes: u=1 and arbitrary r,s,t.
    // Their stabilizer has order #over2, so the orbit has size 8/#over2.
    covered +:= 8 div #over2;
    printf "E%o: trace %o, automorphism orders %o and %o\n",
           i,3-points,#over2,#over4;
end for;

// Distinct traces separate the five orbits. Count all nonsingular
// coefficient vectors directly with the discriminant in characteristic 2.
nonsingular := 0;
for a1,a2,a3,a4,a6 in k2 do
    b2 := a1^2;
    b4 := a1*a3;
    b6 := a3^2;
    b8 := a1^2*a6+a1*a3*a4+a2*a3^2+a4^2;
    disc := b2^2*b8+b6^2+b2*b4*b6;
    if disc ne 0 then
        nonsingular +:= 1;
    end if;
end for;
assert nonsingular eq 16 and covered eq nonsingular;

// Identify the group of order 24 in row 3 via its action on E3[3].
E := EllipticCurve([k | 0,0,1,0,0]);
U := E![0,0,1];
V := E![1,w,1];
O := E![0,1,0];
assert 3*U eq O and 3*V eq O;
assert #{a*U+b*V : a,b in [0..2]} eq 9;
p := Matrix(k,3,3,[w,0,w, 1,1,w, 0,0,1]);
q := Matrix(k,3,3,[w^2,0,w^2, 1,1,w^2, 0,0,1]);
assert p in autE3 and q in autE3;
assert E![w*U[1]+w,U[2]+U[1]+w,1] eq U+V;
assert E![w*V[1]+w,V[2]+V[1]+w,1] eq -U;
assert E![w^2*U[1]+w^2,U[2]+U[1]+w^2,1] eq U-V;
assert E![w^2*V[1]+w^2,V[2]+V[1]+w^2,1] eq U;
P := Matrix(GF(3),2,2,[1,-1,1,0]);
Q := Matrix(GF(3),2,2,[1,1,-1,0]);
assert Determinant(P) eq 1 and Determinant(Q) eq 1;
imageOnTorsion := MatrixGroup<2, GF(3) | P,Q>;
assert #imageOnTorsion eq #SL(2,3) and #imageOnTorsion eq #autE3;
print "Table 3 verified, including all five isomorphism classes.";

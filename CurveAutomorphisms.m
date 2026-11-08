// Lemma 11.2. Automorphisms of E3: y^2+y=x^3 over F4.

k<w> := GF(4);
E := EllipticCurve([k | 0,0,1,0,0]);
assert w^2+w+1 eq 0;

// Matrices act on affine columns (x,y,1). Thus p*q applies q first.
p := Matrix(k,3,3,[w,0,w,     1,1,w,     0,0,1]);  // psi_1
q := Matrix(k,3,3,[w^2,0,w^2, 1,1,w^2,   0,0,1]);  // psi_2
z := Matrix(k,3,3,[1,0,0,     0,1,1,     0,0,1]);  // (x,y+1) = [-1]
I := IdentityMatrix(k,3);
R<X,Y> := PolynomialRing(k,2);
cubic := Y^2+Y+X^3;
assert Evaluate(cubic,[w*X+w,Y+X+w]) eq cubic;
assert Evaluate(cubic,[w^2*X+w^2,Y+X+w^2]) eq cubic;
assert p^3 eq z and q^3 eq z and (p*q)^2 eq z and z^2 eq I;
assert z ne I;
assert IsomorphismData(NegationMap(E)) eq [k | 0,0,1,1];  // (x,y+1)
// The maps fix the origin at infinity. Every matrix has last row (0,0,1),
// so distinct matrices give distinct projective transformations.
G := MatrixGroup<3,k | p,q>;
assert #G eq 24 and #G eq #AutomorphismGroup(E);
P<a,b> := FPGroup<a,b | a^3=b^3, a^3=(a*b)^2>;
assert #P eq #G;  // The verified relations present the generated group.
print "psi_1, psi_2 and [-1] on column coordinates:",p,q,z;
print "Order of Aut_F4(E3):",#G;

// With basis U,V of E[3], compute the action of psi_1, psi_2 and the
// nontrivial field automorphism f of F4 (squaring the coordinates).
U := E![0,0,1];
V := E![1,w,1];
O := E![0,1,0];
assert 3*U eq O and 3*V eq O and #{i*U+j*V : i,j in [0..2]} eq 9;
assert E![w*U[1]+w,U[2]+U[1]+w,1] eq U+V;
assert E![w*V[1]+w,V[2]+V[1]+w,1] eq -U;
assert E![w^2*U[1]+w^2,U[2]+U[1]+w^2,1] eq U-V;
assert E![w^2*V[1]+w^2,V[2]+V[1]+w^2,1] eq U;
assert E![U[1]^2,U[2]^2,1] eq U and E![V[1]^2,V[2]^2,1] eq -V;

k3 := GF(3);
p3 := Matrix(k3,2,2,[1,-1, 1,0]);
q3 := Matrix(k3,2,2,[1,1, -1,0]);
f3 := Matrix(k3,2,2,[1,0, 0,-1]);
assert Determinant(p3) eq 1 and Determinant(q3) eq 1;
G3 := MatrixGroup<2,k3 | p3,q3>;
assert #G3 eq #G and #G3 eq #SL(2,3);
assert f3^2 eq IdentityMatrix(k3,2) and f3*p3*f3^-1 eq q3;
assert Determinant(f3) eq -1;
H := MatrixGroup<2,k3 | p3,q3,f3>;
assert #H eq 2*#G3 and #H eq #GL(2,3);
S<a,b,f> := FPGroup<a,b,f | a^3=b^3, a^3=(a*b)^2, f^2, f*a*f^-1=b>;
assert #S eq #H;
print "psi_1, psi_2 and f on E3[3]:",p3,q3,f3;
print "Order of the semidirect product GL(2,3):",#H;

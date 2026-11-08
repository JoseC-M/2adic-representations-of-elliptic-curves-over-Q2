// Lemma 8.2. The ramified twist of the defect-3 model has defect 6.
// Matrices act on columns. B gives the target basis in candidate coordinates.

Q := Rationals();
P<z> := PolynomialRing(Q);
C<zeta3> := NumberField(z^2+z+1);
zeta6 := -zeta3^2;

// Target normal form for defect 6.
A := Matrix(C,2,2,[0,-2,1,0]);
X := Matrix(C,2,2,[zeta6,0,0,zeta6^-1]);
T := Matrix(C,2,2,[1,0,0,1]);

// Candidate: twist the defect-3 model by the character x |-> -1, t |-> 1.
Ac := Matrix(C,2,2,[0,-2,1,0]);
Xc := Matrix(C,2,2,[-zeta3,0,0,-zeta3^2]);
Tc := Matrix(C,2,2,[1,0,0,1]);

B := Matrix(C,2,2,[0,-2,1,0]);
assert Determinant(B) eq 2;
// B is rational, so its coefficient conjugate is B.
assert Ac*B eq B*A;
assert Xc*B eq B*X;
assert Tc*B eq B*T;

// For w^3=2, B sends the target line with parameter [-4b:a]
// to the candidate line with parameter [a:b], including 0 and infinity.
PC<z> := PolynomialRing(C);
K<w> := NumberField(z^3-2);
S<a,b> := PolynomialRing(K,2);
candidateLine := Matrix(S,2,1,[a,b*w^2]);
targetLine := Matrix(S,2,1,[-4*b,a*w]);
assert ChangeRing(B,S)*targetLine eq (S!(-2*w))*candidateLine;
print "Lemma 8.2 verified.";

// Lemma 9.5. The unramified quadratic twist interchanges the two defect-8 models.

Q := Rationals();
P<z> := PolynomialRing(Q);
H<h0> := NumberField(z^2+15);
PH<w> := PolynomialRing(H);
C<r> := NumberField(w^2+3);
h := C!h0;
q := h/r;  // q=sqrt(5), r=sqrt(-3), h=q*r is in Q_2.
bar := hom<C -> C | -r>;
assert q^2 eq 5 and bar(q) eq -q and bar(h) eq h;
phi1 := (1+q)/2;
phi2 := (1-q)/2;

// Target: the minus model.
A := Matrix(C,2,2,[0,-2,1,0]);
X := Matrix(C,2,2,[-r,2*phi2,-phi1,r]);
Y := Matrix(C,2,2,[r,2*phi1,-phi2,-r]);
T := Matrix(C,2,2,[1,0,0,1]);

// Candidate: the plus model twisted by the unramified quadratic character.
Ac := Matrix(C,2,2,[0,2,-1,0]);
Xc := Matrix(C,2,2,[r,-2*phi2,phi1,-r]);
Yc := Matrix(C,2,2,[-r,-2*phi1,phi2,r]);
Tc := Matrix(C,2,2,[1,0,0,1]);

B := Matrix(C,2,2,[h,6,3,-h]);
barB := Matrix(C,2,2,[bar(h),6,3,-bar(h)]);
assert Determinant(B) eq -3;
assert Ac*barB eq B*A;
assert Xc*B eq B*X;
assert Yc*B eq B*Y;
assert Tc*barB eq B*T;

// The target parameter is [h*a+6*b : 3*a-h*b] for candidate parameter [a:b].
// B carries its line back to the candidate line.
S<a,b> := PolynomialRing(C,2);
candidateLine := Matrix(S,2,1,[a,b]);
targetLine := Matrix(S,2,1,[h*a+6*b,3*a-h*b]);
assert ChangeRing(B,S)*targetLine eq 3*candidateLine;
// The conjugation identities imply stability of this target line under x,y,t.
// At the only possible pole [h:3], inertia fixes the coordinates and moves
// the line. Hence the affine denominator is nonzero for admissible parameters.
pole := Matrix(C,2,1,[h,3]);
image := Xc*pole;
assert 3*image[1,1]-h*image[2,1] eq -3*phi1;
assert phi1 ne 0;
print "Lemma 9.5 verified.";

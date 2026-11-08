// Lemma 10.4. The unramified twist sends (+,alpha) to (-,-alpha).

Q := Rationals();
P<z> := PolynomialRing(Q);
H<q0> := NumberField(z^2-5);
PH<w> := PolynomialRing(H);
C<r> := NumberField(w^2+3);
q := C!q0;
phi1 := (1+q)/2;
phi2 := (1-q)/2;
zeta := (1+r)/2;
zetaInv := (1-r)/2;
assert zeta*zetaInv eq 1;

// Target: the minus model.
A := Matrix(C,2,2,[0,-2,1,0]);
X := Matrix(C,2,2,[phi1,2*zetaInv,-zeta,phi2]);
Y := Matrix(C,2,2,[phi2,2*zeta,-zetaInv,phi1]);
T := Matrix(C,2,2,[1,0,0,1]);

// Candidate: the plus model twisted by the unramified quadratic character.
Ac := Matrix(C,2,2,[0,2,-1,0]);
Xc := Matrix(C,2,2,[phi1,-2*zetaInv,zeta,phi2]);
Yc := Matrix(C,2,2,[phi2,-2*zeta,zetaInv,phi1]);
Tc := Matrix(C,2,2,[1,0,0,1]);

B := Matrix(C,2,2,[1,0,0,-1]);
assert Determinant(B) eq -1;
// B is rational, so its coefficient conjugate is B.
assert Ac*B eq B*A;
assert Xc*B eq B*X;
assert Yc*B eq B*Y;
assert Tc*B eq B*T;

// The target parameter is [-a:b] for candidate parameter [a:b].
S<a,b> := PolynomialRing(C,2);
candidateLine := Matrix(S,2,1,[a,b]);
targetLine := Matrix(S,2,1,[-a,b]);
assert ChangeRing(B,S)*targetLine eq -candidateLine;
print "Lemma 10.4 verified.";

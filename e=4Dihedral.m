// Proposition 7.2. Dihedral case of semistability defect 4.
// A is Frobenius, X is the single inertia generator and T is descent.
// Matrices act on columns. B takes normal-form coordinates to candidate coordinates.

P<z> := PolynomialRing(Rationals());
// Choose h=sqrt(-15) in Q_2. Then r=sqrt(-3) and q=h/r=sqrt(5).
H<h0> := NumberField(z^2+15);
PH<w> := PolynomialRing(H);
C<r> := NumberField(w^2+3);
h := C!h0;
q := h/r;
sigma := hom<C -> C | -r>;
assert sigma(h) eq h and sigma(q) eq -q and q^2 eq 5;
D<U,V> := PolynomialRing(C,2);
R<u1,u2> := quo<D | 6*V^2-5*U^2-1>;

// Normal form. Both Frobenius and t act by sigma on coefficients.
A := Matrix(R,2,2,[0, -2, 1, 0]);
X := Matrix(R,2,2,[q, 2*r, r, -q]);
T := Matrix(R,2,2,[1, 0, 0, 1]);
sigmaX := Matrix(R,2,2,[sigma(q),2*sigma(r),sigma(r),-sigma(q)]);
assert X^2 eq -T and X*sigmaX eq T and A*sigmaX eq X*A;

print "Normal form: A, X, T", A, X, T;

// u1 and u2 are fixed by sigma, as is h.
// Thus sigma(B)=B for every basis matrix written below; the two
// semilinear identities reduce to Ac*B=B*A and Tc*B=B*T.

// det([[a,-2b],[b,a]])=a^2+2b^2 vanishes in Q_2 only for a=b=0,
// since nonzero a^2 and 2b^2 have distinct valuation parity.

// First sign. Generic case (u1,u2) != (-1,1).
Ac := Matrix(R,2,2,[0, -2, 1, 0]);
Xc := Matrix(R,2,2,[q*u1, 2*r*u2, r*u2, -q*u1]);
Tc := Matrix(R,2,2,[1, 0, 0, 1]);
Bgen := Matrix(R,2,2,[5*(u1+1), -2*h*(u2-1), h*(u2-1), 5*(u1+1)]);
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Tc*Bgen eq Bgen*T;
print "Ac, Xc, Tc, Bgen", Ac, Xc, Tc, Bgen;
assert Determinant(Xc) eq 1;
assert Determinant(Bgen) eq (5*(u1+1))^2 + 2*(h*(u2-1))^2;
X1 := Xc;

// First sign, singular case (u1,u2)=(-1,1).
Ac := Matrix(R,2,2,[0, -2, 1, 0]);
Xc := Matrix(R,2,2,[-q, 2*r, r, q]);
Tc := Matrix(R,2,2,[1, 0, 0, 1]);
Bsing := Matrix(R,2,2,[2*h, -10, 5, 2*h]);
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Tc*Bsing eq Bsing*T;
print "Ac, Xc, Tc, Bsing", Ac, Xc, Tc, Bsing;
assert Determinant(Bsing) eq -10;

// Other sign: replace u2 by -u2. Generic case (u1,u2) != (-1,-1).
Ac := Matrix(R,2,2,[0, -2, 1, 0]);
Xc := Matrix(R,2,2,[q*u1, -2*r*u2, -r*u2, -q*u1]);
Tc := Matrix(R,2,2,[1, 0, 0, 1]);
Bgen := Matrix(R,2,2,[5*(u1+1), 2*h*(u2+1), -h*(u2+1), 5*(u1+1)]);
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Tc*Bgen eq Bgen*T;
print "Ac, Xc, Tc, Bgen", Ac, Xc, Tc, Bgen;
assert Determinant(Xc) eq 1;
assert Determinant(Bgen) eq (5*(u1+1))^2 + 2*(h*(u2+1))^2;

X2 := Xc;

// Other sign, singular case (u1,u2)=(-1,-1).
Ac := Matrix(R,2,2,[0, -2, 1, 0]);
Xc := Matrix(R,2,2,[-q, 2*r, r, q]);
Tc := Matrix(R,2,2,[1, 0, 0, 1]);
Bsing := Matrix(R,2,2,[2*h, -10, 5, 2*h]);
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Tc*Bsing eq Bsing*T;
print "Ac, Xc, Tc, Bsing", Ac, Xc, Tc, Bsing;
assert Determinant(Bsing) eq -10;

// A direct intertwiner for the two candidate matrices, invertible everywhere.
S := Matrix(R,2,2,[5*u1, -2*h*u2, h*u2, 5*u1]);
assert X1*S eq S*X2 and Ac*S eq S*Ac;
assert Determinant(S) eq -5;

// The commutator with Frobenius forces an unfiltered automorphism c*I+d*A to have d=0.
assert (A*X-X*A)[1,1] eq -4*r and r ne 0;
// For an inertia matrix with lower-left v*r and upper-right d*r,
// Frobenius commutation gives d=2*v.
E<u,v,d> := PolynomialRing(C,3);
Frob := Matrix(E,2,2,[0,-2,1,0]);
M := Matrix(E,2,2,[q*u,r*d,r*v,-q*u]);
assert Frob*(-M)-M*Frob eq (2*v-d)*r*IdentityMatrix(E,2);

// Check the projective filtration map on independent homogeneous coordinates.
L<a,b> := PolynomialRing(C,2);
X := Matrix(L,2,2,[q,2*r,r,-q]);
line := Matrix(L,2,1,[a,b]);
image := Matrix(L,2,1,[q*a+2*r*b,r*a-q*b]);
assert X*line eq image and X*image eq -line;
// The slope is fixed by x^2 and t. Identify the quadratic field in each quartic.
L1<s1> := NumberField(z^4+8*z+18);
d1 := (4-s1^2)/(2*s1+1);
assert d1^2 eq -2;
L2<s2> := NumberField(z^4+4*z^2+6);
d2 := s2^2+2;
assert d2^2 eq -2;

print "Proposition 7.2 verified.";

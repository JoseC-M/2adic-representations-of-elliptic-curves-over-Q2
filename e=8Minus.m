// Proposition 9.3, defect 8: the branch mu+t(mu)=-1.
// Columns of each B give the normal basis in candidate coordinates.

P<z> := PolynomialRing(Rationals());
H<h0> := NumberField(z^2+15);
PH<w> := PolynomialRing(H);
K<r> := NumberField(w^2+3);
h := K!h0;                         // choose h=sqrt(-15) in Q_2
q := h/r;
sigma := hom<K -> K | -r>;
assert h^2 eq -15 and r^2 eq -3 and q^2 eq 5;
assert sigma(h) eq h and sigma(r) eq -r and sigma(q) eq -q;
phi1 := (1+q)/2;
phi2 := (1-q)/2;

// u1,u2 are fixed by sigma and satisfy the determinant-one equation.
P2<u,v> := PolynomialRing(K,2);
R<u1,u2> := quo<P2 | 6*u^2-20*v^2-1>;

// Normal form: A=M(phi), X=M(x), Y=M(y), T=M(t).
A := Matrix(R,2,2,[0,-2, 1,0]);
X := Matrix(R,2,2,[-r, 2*phi2,
                         -phi1, r]);
Y := Matrix(R,2,2,[r, 2*phi1,
                         -phi2, -r]);
T := Matrix(R,2,2,[1,0, 0,1]);
assert X^2 eq -T and Y^2 eq -T and X*Y eq -Y*X;
assert A*Y eq X*A and A*X eq Y*A;
print "Normal form: A, X, Y, T", A,X,Y,T;

// The semilinear checks read Ac*sigma(B)=B*A and Tc*sigma(B)=B*T.
// Every B below is fixed by sigma: its entries involve only h,u1,u2.
// Over Q_2, det([[a,-2b],[b,a]])=a^2+2b^2 vanishes only if a=b=0,
// since v_2(a^2) is even and v_2(2b^2) is odd for nonzero a,b.

// Root u2. Generic case: (u1,u2) != (1,-1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[r*u1, 1+2*q*u2,
                         -1/2+q*u2, -r*u1]);
Yc := Matrix(R,2,2,[-r*u1, 1-2*q*u2,
                         -1/2-q*u2, r*u1]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bgen := Matrix(R,2,2,[3*(1-u1), -2*h*(u2+1/2),
                         h*(u2+1/2), 3*(1-u1)]);
assert Determinant(Bgen) eq Bgen[1,1]^2 + 2*Bgen[2,1]^2;
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Yc*Bgen eq Bgen*Y;
assert Tc*Bgen eq Bgen*T;
print "Candidate and change of basis: Ac, Xc, Yc, Tc, Bgen", Ac,Xc,Yc,Tc,Bgen;
assert Xc[2,1]+Yc[2,1] eq -1 and Determinant(Xc) eq 1;
X1 := Xc;
Y1 := Yc;

// Root u2. Singular case: (u1,u2) = (1,-1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[r, 2*phi2,
                         -phi1, -r]);
Yc := Matrix(R,2,2,[-r, 2*phi1,
                         -phi2, r]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bsing := Matrix(R,2,2,[-h, -6,
                         3, -h]);
assert Determinant(Bsing) eq 3;
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Yc*Bsing eq Bsing*Y;
assert Tc*Bsing eq Bsing*T;
print "Candidate and change of basis: Ac, Xc, Yc, Tc, Bsing", Ac,Xc,Yc,Tc,Bsing;

// Root -u2. Generic case: (u1,u2) != (1,1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[r*u1, 1-2*q*u2,
                         -1/2-q*u2, -r*u1]);
Yc := Matrix(R,2,2,[-r*u1, 1+2*q*u2,
                         -1/2+q*u2, r*u1]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bgen := Matrix(R,2,2,[3*(1-u1), 2*h*(u2-1/2),
                         -h*(u2-1/2), 3*(1-u1)]);
assert Determinant(Bgen) eq Bgen[1,1]^2 + 2*Bgen[2,1]^2;
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Yc*Bgen eq Bgen*Y;
assert Tc*Bgen eq Bgen*T;
print "Candidate and change of basis: Ac, Xc, Yc, Tc, Bgen", Ac,Xc,Yc,Tc,Bgen;
X2 := Xc;
Y2 := Yc;

// Root -u2. Singular case: (u1,u2) = (1,1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[r, 2*phi2,
                         -phi1, -r]);
Yc := Matrix(R,2,2,[-r, 2*phi1,
                         -phi2, r]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bsing := Matrix(R,2,2,[-h, -6,
                         3, -h]);
assert Determinant(Bsing) eq 3;
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Yc*Bsing eq Bsing*Y;
assert Tc*Bsing eq Bsing*T;
print "Candidate and change of basis: Ac, Xc, Yc, Tc, Bsing", Ac,Xc,Yc,Tc,Bsing;

// A direct intertwiner between the two choices of root.
S := Matrix(R,2,2,[3*u1, 2*h*u2,
                         -h*u2, 3*u1]);
assert Determinant(S) eq 3/2;
assert X1*S eq S*X2 and Y1*S eq S*Y2;
assert Ac*S eq S*Ac and Tc*S eq S*Tc;

print "e=8Minus.m: all checks passed.";

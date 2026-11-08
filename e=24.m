// Proposition 10.2. Semistability defect 24, a2=0.
// Matrices act on columns. A, X, Y, T describe Frobenius, x, y, t.
// The sign of mu+t(mu) selects the model. Each model allows both roots for u2.

Q := Rationals();
Qz<z> := PolynomialRing(Q);
H<h0> := NumberField(z^2+15);
Hw<w> := PolynomialRing(H);
C<r> := NumberField(w^2+3);
h := C!h0;
q := h/r;                         // r=sqrt(-3), q=sqrt(5), h=r*q
t := hom<C -> C | -r>;
assert t(h) eq h and t(q) eq -q and q^2 eq 5;
phi1 := (1+q)/2;
phi2 := (1-q)/2;
zeta := (1+r)/2;
zetaInv := (1-r)/2;
assert t(phi1) eq phi2 and t(zeta) eq zetaInv and zeta*zetaInv eq 1;

P<U,V> := PolynomialRing(C,2);
R<u1,u2> := quo<P | 24*V^2-20*U^2-1>;

// B gives the normal basis in candidate coordinates. Both semilinear
// operators conjugate coefficients by t. Every B below has entries in
// h,u1,u2, all fixed by t; thus Ac*t(B)=B*A reduces to Ac*B=B*A,
// and likewise for Tc. Choose the embedding h in Q_2 (-15 is 1 mod 8).
// Each Bgen has rows (a,-2b), (b,a). Its determinant a^2+2b^2 vanishes
// over Q_2 only when a=b=0, by the parity of the two valuations.

// Model +, mu+t(mu)=+1. Normal form.
A := Matrix(R,2,2,[0,-2, 1,0]);
X := Matrix(R,2,2,[phi1,-2*zetaInv, zeta,phi2]);
Y := Matrix(R,2,2,[phi2,-2*zeta, zetaInv,phi1]);
T := Matrix(R,2,2,[1,0, 0,1]);
assert X^3 eq -T and Y^3 eq -T and (X*Y)^2 eq -T;
assert A*Y eq X*A and A*X eq Y*A;    // Y=t(X)
print "Normal form (+): A, X, Y, T", A,X,Y,T;

// Model +, root u2. Generic case: (u1,u2) != (-1/2,1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[1/2+q*u1,-1+2*r*u2, 1/2+r*u2,1/2-q*u1]);
Yc := Matrix(R,2,2,[1/2-q*u1,-1-2*r*u2, 1/2-r*u2,1/2+q*u1]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bgen := Matrix(R,2,2,[5*(u1+1/2), -2*h*(u2-1/2),
                         h*(u2-1/2), 5*(u1+1/2)]);
assert Determinant(Xc) eq 1 and Determinant(Yc) eq 1;
assert Determinant(Bgen) eq (5*(u1+1/2))^2 + 2*(h*(u2-1/2))^2;
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Yc*Bgen eq Bgen*Y;
assert Tc*Bgen eq Bgen*T;
print "Generic (+, u2): Ac, Xc, Yc, Tc, Bgen", Ac,Xc,Yc,Tc,Bgen;
X1 := Xc; Y1 := Yc;

// Model +, root u2. Singular case: (u1,u2) = (-1/2,1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[phi2,-2*zetaInv, zeta,phi1]);
Yc := Matrix(R,2,2,[phi1,-2*zeta, zetaInv,phi2]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bsing := Matrix(R,2,2,[2*h,-10, 5,2*h]);
assert Determinant(Bsing) eq -10;
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Yc*Bsing eq Bsing*Y;
assert Tc*Bsing eq Bsing*T;
print "Singular (+, u2): Ac, Xc, Yc, Tc, Bsing", Ac,Xc,Yc,Tc,Bsing;

// Model +, root -u2. Generic case: (u1,u2) != (-1/2,-1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[1/2+q*u1,-1-2*r*u2, 1/2-r*u2,1/2-q*u1]);
Yc := Matrix(R,2,2,[1/2-q*u1,-1+2*r*u2, 1/2+r*u2,1/2+q*u1]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bgen := Matrix(R,2,2,[5*(u1+1/2), -2*h*(-u2-1/2),
                         h*(-u2-1/2), 5*(u1+1/2)]);
assert Determinant(Xc) eq 1 and Determinant(Yc) eq 1;
assert Determinant(Bgen) eq (5*(u1+1/2))^2 + 2*(h*(-u2-1/2))^2;
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Yc*Bgen eq Bgen*Y;
assert Tc*Bgen eq Bgen*T;
print "Generic (+, -u2): Ac, Xc, Yc, Tc, Bgen", Ac,Xc,Yc,Tc,Bgen;
X2 := Xc; Y2 := Yc;

// Model +, root -u2. Singular case: (u1,u2) = (-1/2,-1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[phi2,-2*zetaInv, zeta,phi1]);
Yc := Matrix(R,2,2,[phi1,-2*zeta, zetaInv,phi2]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bsing := Matrix(R,2,2,[2*h,-10, 5,2*h]);
assert Determinant(Bsing) eq -10;
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Yc*Bsing eq Bsing*Y;
assert Tc*Bsing eq Bsing*T;
print "Singular (+, -u2): Ac, Xc, Yc, Tc, Bsing", Ac,Xc,Yc,Tc,Bsing;

// Direct comparison of the two roots for u2, valid everywhere on the conic.
S := Matrix(R,2,2,[5*u1,-2*h*u2, h*u2,5*u1]);
assert Determinant(S) eq -5/4;
assert A*S eq S*A and T*S eq S*T;     // t fixes h and both parameters
assert X1*S eq S*X2 and Y1*S eq S*Y2;

// Filtration for model +: x sends [a:b] to the following matrix times
// [a:b], as in Definition 10.1. The nonzero entry X[2,1] excludes infinity.
filtration := Matrix(R,2,2,[-phi2,-2*zetaInv, zeta,-phi1]);
assert X*filtration eq -T and X[2,1] ne 0;
// The fixed central element x^3 acts by -T, hence trivially on lines.
// Any endomorphism is c0*T+c1*A; commuting with X forces c1=0.
assert A*X ne X*A;
assert Trace(X*A) eq -2;

// Model -, mu+t(mu)=-1. Normal form.
A := Matrix(R,2,2,[0,-2, 1,0]);
X := Matrix(R,2,2,[phi1,2*zetaInv, -zeta,phi2]);
Y := Matrix(R,2,2,[phi2,2*zeta, -zetaInv,phi1]);
T := Matrix(R,2,2,[1,0, 0,1]);
assert X^3 eq -T and Y^3 eq -T and (X*Y)^2 eq -T;
assert A*Y eq X*A and A*X eq Y*A;    // Y=t(X)
print "Normal form (-): A, X, Y, T", A,X,Y,T;

// Model -, root u2. Generic case: (u1,u2) != (-1/2,-1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[1/2+q*u1,1+2*r*u2, -1/2+r*u2,1/2-q*u1]);
Yc := Matrix(R,2,2,[1/2-q*u1,1-2*r*u2, -1/2-r*u2,1/2+q*u1]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bgen := Matrix(R,2,2,[5*(u1+1/2), -2*h*(u2+1/2),
                         h*(u2+1/2), 5*(u1+1/2)]);
assert Determinant(Xc) eq 1 and Determinant(Yc) eq 1;
assert Determinant(Bgen) eq (5*(u1+1/2))^2 + 2*(h*(u2+1/2))^2;
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Yc*Bgen eq Bgen*Y;
assert Tc*Bgen eq Bgen*T;
print "Generic (-, u2): Ac, Xc, Yc, Tc, Bgen", Ac,Xc,Yc,Tc,Bgen;
X1 := Xc; Y1 := Yc;

// Model -, root u2. Singular case: (u1,u2) = (-1/2,-1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[phi2,2*zetaInv, -zeta,phi1]);
Yc := Matrix(R,2,2,[phi1,2*zeta, -zetaInv,phi2]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bsing := Matrix(R,2,2,[2*h,10, -5,2*h]);
assert Determinant(Bsing) eq -10;
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Yc*Bsing eq Bsing*Y;
assert Tc*Bsing eq Bsing*T;
print "Singular (-, u2): Ac, Xc, Yc, Tc, Bsing", Ac,Xc,Yc,Tc,Bsing;

// Model -, root -u2. Generic case: (u1,u2) != (-1/2,1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[1/2+q*u1,1-2*r*u2, -1/2-r*u2,1/2-q*u1]);
Yc := Matrix(R,2,2,[1/2-q*u1,1+2*r*u2, -1/2+r*u2,1/2+q*u1]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bgen := Matrix(R,2,2,[5*(u1+1/2), -2*h*(1/2-u2),
                         h*(1/2-u2), 5*(u1+1/2)]);
assert Determinant(Xc) eq 1 and Determinant(Yc) eq 1;
assert Determinant(Bgen) eq (5*(u1+1/2))^2 + 2*(h*(1/2-u2))^2;
assert Ac*Bgen eq Bgen*A;
assert Xc*Bgen eq Bgen*X;
assert Yc*Bgen eq Bgen*Y;
assert Tc*Bgen eq Bgen*T;
print "Generic (-, -u2): Ac, Xc, Yc, Tc, Bgen", Ac,Xc,Yc,Tc,Bgen;
X2 := Xc; Y2 := Yc;

// Model -, root -u2. Singular case: (u1,u2) = (-1/2,1/2).
Ac := Matrix(R,2,2,[0,-2, 1,0]);
Xc := Matrix(R,2,2,[phi2,2*zetaInv, -zeta,phi1]);
Yc := Matrix(R,2,2,[phi1,2*zeta, -zetaInv,phi2]);
Tc := Matrix(R,2,2,[1,0, 0,1]);
Bsing := Matrix(R,2,2,[2*h,10, -5,2*h]);
assert Determinant(Bsing) eq -10;
assert Ac*Bsing eq Bsing*A;
assert Xc*Bsing eq Bsing*X;
assert Yc*Bsing eq Bsing*Y;
assert Tc*Bsing eq Bsing*T;
print "Singular (-, -u2): Ac, Xc, Yc, Tc, Bsing", Ac,Xc,Yc,Tc,Bsing;

// Direct comparison of the two roots for u2, valid everywhere on the conic.
S := Matrix(R,2,2,[5*u1,-2*h*u2, h*u2,5*u1]);
assert Determinant(S) eq -5/4;
assert A*S eq S*A and T*S eq S*T;     // t fixes h and both parameters
assert X1*S eq S*X2 and Y1*S eq S*Y2;

// Filtration for model -: x sends [a:b] to the following matrix times
// [a:b], as in Definition 10.1. The nonzero entry X[2,1] excludes infinity.
filtration := Matrix(R,2,2,[phi2,-2*zetaInv, zeta,phi1]);
assert X*filtration eq T and X[2,1] ne 0;
// The fixed central element x^3 acts by -T, hence trivially on lines.
// Any endomorphism is c0*T+c1*A; commuting with X forces c1=0.
assert A*X ne X*A;
assert Trace(X*A) eq 2;

// The Frobenius relation gives Yraw=t(Xraw) in the shape below.
// For det(Xraw)=1, the relation (Xraw*Yraw)^2=-I gives trace zero.
// Hence (mu+t(mu))^2=(mu-nu/2)^2=1, giving the two model signs.
D<ell,mu,nu> := PolynomialRing(C,3);
Xraw := Matrix(D,2,2,[ell,nu, mu,1-ell]);
Yraw := Matrix(D,2,2,[1-ell,-2*mu, -nu/2,ell]);
assert Trace(Xraw*Yraw) eq 2*(Determinant(Xraw)-(mu-nu/2)^2);

// An isomorphism must commute with t, hence is t-fixed. It must then
// conjugate both X and A. The traces of X*A (-2 and 2) distinguish the models.
print "Proposition 10.2 verified for both models and both roots for u2.";

// Theorem 4.4 (T: realization e=1). All models below have integral
// coefficients and odd discriminant, so reduction at 2 is good.
// The ordinary splitting criterion is the cited theorem of Serre.


Q := Rationals();
k := GF(2);

// The two ordinary curves displayed in the proof, in the order printed.
Es := EllipticCurve([Q | 1,-1,0,-2,-1]);
Ens := EllipticCurve([Q | 1,-1,0,0,-27]);
assert Discriminant(Es) eq -343;
assert Discriminant(Ens) eq -315657;
assert jInvariant(Es) eq -3375;
assert jInvariant(Ens) eq -1/433;
assert 3 - #ChangeRing(Es,k) eq 1;
assert 3 - #ChangeRing(Ens,k) eq 1;

// CM by the maximal order of discriminant -7 for Es.
// The polynomial of (1+sqrt(-7))/2 is X^2-X+2. Its reduction at 2
// has two distinct linear factors, so 2 splits in the CM field.
H := HilbertClassPolynomial(-7);
assert H eq Parent(H).1 + 3375;
assert Evaluate(H,Integers()!jInvariant(Es)) eq 0;
R<X> := PolynomialRing(k);
assert X^2-X+2 eq X*(X+1);
assert GCD(X,X+1) eq 1;

// Every CM j-invariant is an algebraic integer. Since j(Ens) is
// rational with denominator 433, Ens has no geometric CM.
assert Denominator(jInvariant(Ens)) eq 433;

// Q_2(sqrt(5)) is unramified: (1+sqrt(5))/2 has polynomial
// X^2-X-1, whose reduction is irreducible over F_2.
assert IsIrreducible(X^2-X-1);

// For E: y^2+xy=x^3+a2*x^2+a4*x+a6, completing the square gives
// (2*y+x)^2=f(x), where f(x)=4*x^3+(1+4*a2)*x^2+4*a4*x+4*a6.
// The displayed d=5 models satisfy f_tw(5*x)=5^3*f(x). Over
// Q(sqrt(5)), take x_tw=5*x and (2*y_tw+x_tw)=5*sqrt(5)*(2*y+x).
EsTw := EllipticCurve([Q | 1,-4,0,-50,-125]);
EnsTw := EllipticCurve([Q | 1,-4,0,0,-3375]);
P<T> := PolynomialRing(Q);
fS := 4*T^3-3*T^2-8*T-4;
fSTw := 4*T^3-15*T^2-200*T-500;
fNs := 4*T^3-3*T^2-108;
fNsTw := 4*T^3-15*T^2-13500;
assert Evaluate(fSTw,5*T) eq 5^3*fS;
assert Evaluate(fNsTw,5*T) eq 5^3*fNs;
assert Discriminant(EsTw) eq 5^6*Discriminant(Es);
assert Discriminant(EnsTw) eq 5^6*Discriminant(Ens);
assert jInvariant(EsTw) eq jInvariant(Es);
assert jInvariant(EnsTw) eq jInvariant(Ens);
assert 3 - #ChangeRing(EsTw,k) eq -1;
assert 3 - #ChangeRing(EnsTw,k) eq -1;

// Integral lifts of E1,E3,E5 of Table 3 give the three even traces.
Em2 := EllipticCurve([Q | 0,0,1,1,0]);
E0 := EllipticCurve([Q | 0,0,1,0,0]);
Ep2 := EllipticCurve([Q | 0,0,1,1,1]);
assert Discriminant(Em2) eq -91;
assert Discriminant(E0) eq -27;
assert Discriminant(Ep2) eq -739;
assert 3 - #ChangeRing(Em2,k) eq -2;
assert 3 - #ChangeRing(E0,k) eq 0;
assert 3 - #ChangeRing(Ep2,k) eq 2;

print "Theorem 4.4: ordinary curves, unramified twists and supersingular lifts verified.";

// Section 8, before Definition 8.1; also the field choice in Corollary 8.3.
// For each of the three polynomials in Table 2, L=Q_2(w,sqrt(d))
// with w^3=2. Its Galois closure is K=L(zeta_3).

Q := Rationals();
P<T> := PolynomialRing(Q);
f1 := T^6+2*T^3+2;
f2 := T^6+14;
f3 := T^6+2;

// All three sextics, the cubic, and defining polynomials of the three
// ramified quadratic fields are Eisenstein at 2. For i use (i-1)^2+
// 2(i-1)+2=0. The checks take place in Q[T], without 2-adic rounding.
for f in [f1,f2,f3,T^3-2,T^2+2*T+2,T^2-2,T^2+2] do
    assert LeadingCoefficient(f) eq 1;
    assert (Integers()!Coefficient(f,0)) mod 4 eq 2;
    for j in [1..Degree(f)-1] do
        assert (Integers()!Coefficient(f,j)) mod 2 eq 0;
    end for;
end for;

// Row 1: i=a1^3+1 and w=-i*a1^2.
L1<a1> := NumberField(f1);
i := a1^3+1;
w1 := -i*a1^2;
assert i^2 eq -1 and w1^3 eq 2;

// Row 2: in Q_2 choose c^3=-7 and b^2=-7. For c use the simple root
// 1 of T^3+7 mod 2. For b put b=1+4k and lift the simple root k=1
// of 2k^2+k+1 mod 2. These elementary Hensel certificates are exact.
cubeUnit := T^3+7;
squareUnit := 2*T^2+T+1;
assert (1+4*T)^2+7 eq 8*squareUnit;
for f in [cubeUnit,squareUnit] do
    assert (Integers()!Evaluate(f,1)) mod 2 eq 0;
    assert (Integers()!Evaluate(Derivative(f),1)) mod 2 eq 1;
end for;
// Then w=a2^2/c and sqrt(2)=a2^3/b; clear their unit denominators.
L2<a2> := NumberField(f2);
assert (a2^2)^3 eq 2*(-7) and (a2^3)^2 eq 2*(-7);

// Row 3: w=-a3^2 and sqrt(-2)=a3^3.
L3<a3> := NumberField(f3);
assert (-a3^2)^3 eq 2 and (a3^3)^2 eq -2;

// In each L the cubic and quadratic subfields just exhibited have coprime
// degrees, so their compositum has degree six and equals L. It is totally
// ramified. Over Q_2 the cubic closure M=Q_2(w,zeta_3) has group S_3
// and unique quadratic subfield Q_2(zeta_3), unramified because
// T^2+T+1 mod 2 is irreducible. Hence M intersects Q_2(sqrt(d))
// trivially, and K=M(sqrt(d)) has group S_3 x C_2.
R<V> := PolynomialRing(GF(2));
assert IsIrreducible(V^2+V+1);

// Label w,zeta_3*w,zeta_3^2*w as 1,2,3 and +/-sqrt(d) as 4,5.
// An inertia generator x cycles the first triple and swaps the last pair.
// The Frobenius t fixes w and sqrt(d), and interchanges the other roots.
S := Sym(5);
x := S![2,3,1,5,4];
t := S![1,3,2,4,5];
G := sub<S | x,t>;
assert #G eq 12 and Order(x) eq 6 and Order(t) eq 2;
assert t*x*t eq x^-1;
assert x^3 eq S![1,2,3,5,4]; // K^<x^3> = M
fixesQuadratic := sub<S | x^2,t>;
assert #fixesQuadratic eq 6; // fixes sqrt(d), hence its fixed field is Q_2(sqrt(d))
print "Verified the cubic and quadratic subfields of all three sextic rows and the action on their closures.";

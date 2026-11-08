// Lemma 3.1, Table 2. The i-th curve attains good reduction over L_{24,i}.

Q2 := pAdicField(2, 200);
R<X> := PolynomialRing(Q2);

// The eight defining polynomials of L_{24,i}, in table order.
polynomials := [
    X^24 + 2*X^9 + 2*X^6 + 2,
    X^24 + 2*X^15 + 2*X^6 + 2,
    X^24 + 4*X^15 + 2*X^6 + 4*X^3 + 2,
    X^24 + 4*X^21 + 2*X^6 + 4*X^3 + 2,
    X^24 + 4*X^21 + 4*X^6 + 8*X^3 + 2,
    X^24 + 4*X^21 + 8*X^9 + 4*X^6 + 8*X^3 + 2,
    X^24 + 4*X^21 + 4*X^6 + 2,
    X^24 + 4*X^21 + 8*X^9 + 4*X^6 + 2
];

// The twists by 1, -1, 2, -2 of each curve in Dembele--Freitas--Voight (7.1.1).
curves := [
    EllipticCurve([Q2 | 0,0,0,-3,-1]),
    EllipticCurve([Q2 | 0,0,0,-3, 1]),
    EllipticCurve([Q2 | 0,0,0,-12,-8]),
    EllipticCurve([Q2 | 0,0,0,-12, 8]),
    EllipticCurve([Q2 | 0,0,0,3, 2]),
    EllipticCurve([Q2 | 0,0,0,3,-2]),
    EllipticCurve([Q2 | 0,0,0,12, 16]),
    EllipticCurve([Q2 | 0,0,0,12,-16])
];

// Good reduction is equivalent to conductor exponent zero over the local field L.
assert #polynomials eq 8 and #curves eq 8;
for i in [1..8] do
    L := ext<Q2 | polynomials[i]>;
    E := ChangeRing(curves[i], L);
    assert Valuation(Conductor(E)) eq 0;
    printf "L_{24,%o}: good reduction verified.\n", i;
end for;

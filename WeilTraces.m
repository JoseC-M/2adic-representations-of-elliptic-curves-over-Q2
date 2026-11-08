// Remark 3.15. For every inertia matrix g compute Tr(g) and Tr(g*A),
// where A is the matrix of Frobenius in the adapted basis. A Weil element
// of degree d acts by g*A^(-d): the coefficient actions of t^d and
// Frobenius^(-d) cancel because M(t)=I and A has rational entries.
// Since A^2 = a2*A - 2*I, the two traces determine Tr(g*A^n) for every
// integer n, using the same recurrence backwards as well as forwards.

Q := Rationals();
I2 := IdentityMatrix(Q,2);

// e=1 and e=2. Scalar inertia allows a rational companion basis for A.
for a2 in [-2..2] do
    A := Matrix(Q,2,2,[0,-2,1,a2]);
    assert A^2 eq a2*A-2*I2;
    X := Matrix(Q,2,2,[1,0,0,1]);            // e=1
    assert X eq I2 and Trace(X) eq 2 and Trace(X*A) eq a2;
    X := Matrix(Q,2,2,[-1,0,0,-1]);         // e=2
    assert X ne I2 and X^2 eq I2;
    assert Trace(X) eq -2 and Trace(X*A) eq -a2;
end for;

// e=4, cyclic Galois group. The two choices of inertia generator
// are X and -X=X^3. They give the same four matrices for each trace.
for a2 in [-2,2] do
    A := Matrix(Q,2,2,[0,-2,1,a2]);
    X := Matrix(Q,2,2,[1,a2,-a2/2,-1]);
    assert A^2 eq a2*A-2*I2 and X^2 eq -I2;
    inertia := [I2,X,-I2,-X];
    assert #Seqset(inertia) eq 4;
    assert {Trace(g) : g in inertia} eq {Q | -2,0,2};
    assert {Trace(g*A) : g in inertia} eq {Q | -2,2};
end for;

// Remaining models have a2=0 and Q_4 as unramified coefficient field.
// The displayed entries are algebraic numbers, so we compute exactly in
// Q(sqrt(5),sqrt(-3)) with the choices of roots fixed in the manuscript.
P<z> := PolynomialRing(Q);
H<q0> := NumberField(z^2-5);
PH<w> := PolynomialRing(H);
C<r> := NumberField(w^2+3);
q := C!q0;
A := Matrix(C,2,2,[0,-2,1,0]);
T := Matrix(C,2,2,[1,0,0,1]);              // matrix of semilinear t
assert A^2 eq -2*T;

// e=3.
X := Matrix(C,2,2,[(-1+r)/2,0,0,(-1-r)/2]);
inertia := [T,X,X^2];
assert X^3 eq T and #Seqset(inertia) eq 3;
assert {Trace(g) : g in inertia} eq {C | -1,2};
assert {Trace(g*A) : g in inertia} eq {C | 0};

// e=4, dihedral Galois group.
X := Matrix(C,2,2,[q,2*r,r,-q]);
inertia := [T,X,X^2,X^3];
assert X^4 eq T and #Seqset(inertia) eq 4;
assert {Trace(g) : g in inertia} eq {C | -2,0,2};
assert {Trace(g*A) : g in inertia} eq {C | 0};

// e=6.
X := Matrix(C,2,2,[(1+r)/2,0,0,(1-r)/2]);
inertia := [T,X,X^2,X^3,X^4,X^5];
assert X^6 eq T and #Seqset(inertia) eq 6;
assert {Trace(g) : g in inertia} eq {C | -2,-1,1,2};
assert {Trace(g*A) : g in inertia} eq {C | 0};

// e=8. In each of the two normal forms X and Y generate Q8.
for sign in [1,-1] do
    X := Matrix(C,2,2,[sign*r,sign*(-1+q),sign*(1+q)/2,-sign*r]);
    Y := Matrix(C,2,2,[-sign*r,sign*(-1-q),sign*(1-q)/2,sign*r]);
    assert X^2 eq -T and Y^2 eq -T and X*Y eq -Y*X;
    inertia := [T,-T,X,-X,Y,-Y,X*Y,-X*Y];
    assert #Seqset(inertia) eq 8;
    assert {Trace(g) : g in inertia} eq {C | -2,0,2};
    assert {Trace(g*A) : g in inertia} eq {C | -2,0,2};
end for;

// e=24. Generate the 24 inertia matrices as three right cosets of Q8.
for sign in [1,-1] do
    X := Matrix(C,2,2,[(1+q)/2,sign*(-1+r),sign*(1+r)/2,(1-q)/2]);
    Y := Matrix(C,2,2,[(1-q)/2,sign*(-1-r),sign*(1-r)/2,(1+q)/2]);
    U := X*Y;
    V := Y*X;
    assert U^2 eq -T and V^2 eq -T and U*V eq -V*U;
    quaternion := [T,-T,U,-U,V,-V,U*V,-U*V];
    inertia := [g*X^j : g in quaternion, j in [0..2]];
    assert #Seqset(inertia) eq 24;
    for g in inertia do
        assert g*X in inertia and g*Y in inertia;
    end for;
    assert {Trace(g) : g in inertia} eq {C | -2,-1,0,1,2};
    assert {Trace(g*A) : g in inertia} eq {C | -2,0,2};
end for;

print "Remark 3.15: all inertia and Frobenius-coset traces are rational.";

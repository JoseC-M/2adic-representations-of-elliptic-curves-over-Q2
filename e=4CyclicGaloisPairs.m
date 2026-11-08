// Lemma 11.4, the two cyclic cases at the end of the proof.
// On E1 the coordinate automorphism u equals 1+Frob_2.
// On E5 it equals 1-Frob_2. This identifies both named module signs.

k := GF(2);
R<X,Y> := PolynomialRing(k,2);
curves := [Y^2+Y+X^3+X, Y^2+Y+X^3+X+1];  // E1, E5
traces := [-2,2];
U := Matrix(k,3,3,[1,0,1, 1,1,0, 0,0,1]); // (X+1,Y+X)
V := Matrix(k,3,3,[1,0,1, 1,1,1, 0,0,1]); // (X+1,Y+X+1)
N := Matrix(k,3,3,[1,0,0, 0,1,1, 0,0,1]); // [-1]
I3 := IdentityMatrix(k,3);
assert U^2 eq N and N ne I3 and N^2 eq I3;
assert U*V eq I3 and V*U eq I3;
for i in [1,2] do
    C := curves[i];
    assert Evaluate(C,[X+1,Y+X]) eq C;
    assert Evaluate(C,[X+1,Y+X+1]) eq C;

    // Over F2 every change fixing the origin has u-scaling equal to 1.
    // Check that these two inverse generators give the whole group.
    autOrder := 0;
    for r,s,t in k do
        if Evaluate(C,[X+r,Y+s*X+t]) eq C then
            autOrder +:= 1;
        end if;
    end for;
    assert autOrder eq 4;
    points := 1;
    for x,y in k do
        if Evaluate(C,[x,y]) eq 0 then
            points +:= 1;
        end if;
    end for;
    assert 3-points eq traces[i];
end for;

// Compare endomorphisms at the generic point P=(X,Y). The other point
// is Q=(X^2,Y^2) on E1 or Q=(X^2,Y^2+1) on E5. In the respective
// coordinate rings, (Y_Q+Y)/(X^2+X) is X+1. Use polynomial identities
// before division so that no finite sample of curve points is needed.
slope := X+1;
assert Y^2+Y-(X^2+X)*slope eq curves[1];
assert (Y^2+1)+Y-(X^2+X)*slope eq curves[2];
Xsum := slope^2+X+X^2;
Ysum := slope*(X+Xsum)+Y+1;
assert Xsum eq X+1 and Ysum eq Y+X;
// The two morphisms agree on a dense open and therefore everywhere.

// In Definition 7.4 the + generator is Id-(a2/2)*F. By additivity of
// the contravariant Dieudonne functor the equalities above give exactly
// this generator for u. The inverse gives the negative of that matrix.
I := IdentityMatrix(Rationals(),2);
F1 := Matrix(Rationals(),2,2,[0,-2,1,-2]);
F5 := Matrix(Rationals(),2,2,[0,-2,1, 2]);
U1 := I+F1;
U5 := I-F5;
assert U1 eq Matrix(Rationals(),2,2,[1,-2,1,-1]);
assert U5 eq Matrix(Rationals(),2,2,[1, 2,-1,-1]);
assert U1^2 eq -I and U5^2 eq -I;
assert U1^-1 eq -U1 and U5^-1 eq -U5;
print "For both traces, nu(x)=u gives +, and nu(x)=u^(-1) gives -.";

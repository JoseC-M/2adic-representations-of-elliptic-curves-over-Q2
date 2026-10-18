// Checks for 2adicRepV7.tex. Matrix arithmetic is exact.

procedure CheckExceptionalFields()
    // Lemma L: InTypes: the eight exceptional fields, in Table 1 order.
    Q2 := pAdicField(2, 200);
    R2<X> := PolynomialRing(Q2);
    // DFV (7.1.1): r*y^2=x^3-3*x-1 and r*y^2=x^3+3*x+2.
    E := [EllipticCurve([Q2|0,0,0,-3*r^2,-r^3]) : r in [1,-1,2,-2]]
      cat [EllipticCurve([Q2|0,0,0,3*r^2,2*r^3]) : r in [1,-1,2,-2]];
    polys := [
        X^24+2*X^9+2*X^6+2,
        X^24+2*X^15+2*X^6+2,
        X^24+4*X^15+2*X^6+4*X^3+2,
        X^24+4*X^21+2*X^6+4*X^3+2,
        X^24+4*X^21+4*X^6+2,
        X^24+4*X^21+8*X^9+4*X^6+2,
        X^24+4*X^21+4*X^6+8*X^3+2,
        X^24+4*X^21+8*X^9+4*X^6+8*X^3+2
    ];
    L := [* ext<Q2|f> : f in polys *];
    curve_index := [1..8];
    for j in [1..8] do
        assert Valuation(Conductor(ChangeRing(E[curve_index[j]], L[j]))) eq 0;
        printf "Exceptional field L_24,%o: good reduction verified.\n", j;
    end for;
end procedure;

// Exact matrix checks for 2adicRepV7.tex. Embed h=sqrt(-15) in Q_2;
// r=sqrt(-3), q=h/r=sqrt(5), and t fixes h and negates r and q.
procedure CheckMatrices()
    QZ<z> := PolynomialRing(Rationals());
    K<h> := NumberField(z^2+15);
    KZ<z> := PolynomialRing(K);
    C<r> := NumberField(z^2+3);
    q := C!h/r;
    t := hom<C -> C | -r>;
    bar := func<M | Matrix(C,2,2,[t(a) : a in Eltseq(M)])>;
    F := Matrix(C,2,2,[0,-2,1,0]);
    Nt := IdentityMatrix(C,2);
    P<u1,u2> := PolynomialRing(C,2);

    // <e, model sign, relation, A, N, B, exceptional point, B_exception>.
    cases := [*
      <3,1,4*u1^2+8*u2^2-1,
       Matrix(P,2,2,[-1/2+u1*r,2*u2*r,u2*r,-1/2-u1*r]),
       DiagonalMatrix(C,[(-1+r)/2,(-1-r)/2]),
       Matrix(P,2,2,[u1+1/2,-2*u2,u2,u1+1/2]),[-1/2,0],F>,
      <4,1,6*u2^2-5*u1^2-1,
       Matrix(P,2,2,[u1*q,2*u2*r,u2*r,-u1*q]),Matrix(C,2,2,[q,2*r,r,-q]),
       Matrix(P,2,2,[5*(u1+1),-2*h*(u2-1),h*(u2-1),5*(u1+1)]),
       [-1,1],Matrix(C,2,2,[2*h,-10,5,2*h])>
    *];
    for s in [1,-1] do
        Append(~cases,<8,s,6*u1^2-20*u2^2-1,
          Matrix(P,2,2,[u1*r,-s+2*u2*q,s/2+u2*q,-u1*r]),
          s*Matrix(C,2,2,[r,-1+q,(1+q)/2,-r]),
          Matrix(P,2,2,[3*(s*u1+1),2*h*(s*u2-1/2),-h*(s*u2-1/2),3*(s*u1+1)]),
          [-s,s/2],Matrix(C,2,2,[-h,-6,3,-h])>);
        Append(~cases,<24,s,24*u2^2-20*u1^2-1,
          Matrix(P,2,2,[1/2+u1*q,-s+2*u2*r,s/2+u2*r,1/2-u1*q]),
          Matrix(C,2,2,[(1+q)/2,s*(-1+r),s*(1+r)/2,(1-q)/2]),
          Matrix(P,2,2,[5*(u1+1/2),-2*h*(u2-s/2),h*(u2-s/2),5*(u1+1/2)]),
          [-1/2,s/2],Matrix(C,2,2,[2*h,-10*s,5*s,2*h])>);
    end for;

    print "h^2=-15, r^2=-3, q=h/r; semilinear Frobenius F:", F;
    for c in cases do
        e,s,g,A,N,B,p,Bex := Explode(c);
        Apoly := A;
        // B is invertible at every point of the conic except p. These two
        // ideal-membership certificates prove that no other exception exists.
        H := ideal<P | g,Determinant(B)>;
        assert (P.1-p[1])^2 in H and (P.2-p[2])^2 in H;
        assert Matrix(C,2,2,[Evaluate(b,[C!p[1],C!p[2]]) : b in Eltseq(B)]) eq 0;
        R<u1,u2> := quo<P | g>;
        tc := hom<C -> R | -R!r>;
        tr := hom<R -> R | tc,[u1,u2]>;
        barR := func<M | Matrix(R,2,2,[tr(a) : a in Eltseq(M)])>;
        A := ChangeRing(A,R); B := ChangeRing(B,R);
        NR := ChangeRing(N,R); FR := ChangeRing(F,R);
        for eps in [1,-1] do
            sign := hom<R -> R | [u1,eps*u2]>;
            As := Matrix(R,2,2,[sign(a) : a in Eltseq(A)]);
            Bs := Matrix(R,2,2,[sign(b) : b in Eltseq(B)]);
            assert As*Bs eq Bs*NR and barR(As)*Bs eq Bs*barR(NR);
            assert barR(Bs) eq Bs and FR*barR(Bs) eq Bs*FR;
            printf "e=%o, model sign=%o, u2 sign=%o; relation: %o=0\n",e,s,eps,g;
            print "A:",As,"N:",NR,"B:",Bs;
            print "A*B = B*N:",As*Bs;
            print "t(A)*B = B*t(N):",barR(As)*Bs,"F*t(B) = B*F:",FR*barR(Bs);
            // The same determinant certificate, transported by u2 -> eps*u2,
            // gives the unique exceptional point for this sign.
            pex := [C | p[1],eps*p[2]];
            AsP := Matrix(P,2,2,[Evaluate(a,[P.1,eps*P.2]) : a in Eltseq(Apoly)]);
            Aex := Matrix(C,2,2,[Evaluate(a,pex) : a in Eltseq(AsP)]);
            assert Determinant(Bex) ne 0 and Nt*bar(Bex) eq Bex*Nt;
            assert Aex*Bex eq Bex*N and bar(Aex)*Bex eq Bex*bar(N);
            assert F*bar(Bex) eq Bex*F;
            printf "Exceptional point for u2 sign %o: %o\n",eps,pex;
            print "A_exception:",Aex,"B_exception:",Bex;
            print "A_exception*B_exception = B_exception*N:",Aex*Bex;
            print "t(A_exception)*B_exception = B_exception*t(N):",bar(Aex)*Bex;
        end for;
        G := MatrixGroup<2,C | N,bar(N),Nt>;
        assert IsFinite(G) and forall{a : a in G | Trace(a) in Rationals()};
        // F^2=-2I reduces all Weil--Deligne traces to these two checks.
        assert F^2 eq -2*Nt;
        assert forall{a : a in G | Trace(a*F) in Rationals()};
        print "Verified: Tr(g) and Tr(g*F) are rational for every g in G.";
    end for;

    // The two twist changes of basis, with twisted Frobenius -F.
    for e in [8,24] do
        if e eq 8 then
            A := Matrix(C,2,2,[r,-1+q,(1+q)/2,-r]); N := -A;
            B := Matrix(C,2,2,[h,6,3,-h]);
        else
            A := Matrix(C,2,2,[(1+q)/2,-1+r,(1+r)/2,(1-q)/2]);
            N := Matrix(C,2,2,[(1+q)/2,1-r,-(1+r)/2,(1-q)/2]);
            B := DiagonalMatrix(C,[1,-1]);
        end if;
        assert Determinant(B) ne 0 and bar(B) eq B;
        assert A*B eq B*N and bar(A)*B eq B*bar(N) and (-F)*bar(B) eq B*F;
        printf "Twist e=%o:\n",e;
        print "A:",A,"N:",N,"B:",B,"A*B = B*N:",A*B;
        print "t(A)*B = B*t(N):",bar(A)*B,"(-F)*t(B) = B*F:",(-F)*bar(B);
    end for;
end procedure;

procedure CheckGaloisPairs()
    print "  E_3: computing its automorphisms and the coefficient Galois action...";
    k<w> := GF(4);
    E0 := EllipticCurve([GF(2)|0,0,1,0,0]);
    E := BaseExtend(E0,k);
    A, ev := AutomorphismGroup(E);
    A0 := AutomorphismGroup(E0);
    assert #A eq 24 and #A0 eq 2 and 3-#E0 eq 0;
    print E;

    // Magma composes maps left-to-right. geom(a*b)=geom(a) o geom(b).
    geom := func<a | ev(a^-1)>;
    // Compare maps exactly; ev may return MapSch or MapIsoSch.
    elt := func<m | Rep({a : a in A | geom(a) eq m})>;
    R := CoordinateRing(Ambient(E));
    sigma := hom<k -> k | w^2>;
    conjugate := hom<R -> R | sigma,[R.1,R.2,R.3]>;
    gal := func<m | map<E -> E |
        [conjugate(h) : h in DefiningPolynomials(m)]>>;
    // gal conjugates coefficients; it is not the inseparable Frobenius isogeny.
    p := elt(Automorphism(E,[w,w^2,w,w^2]));
    q := elt(Automorphism(E,[w^2,w,w^2,w]));
    z := elt(NegationMap(E));
    print "psi_1 =", geom(p);
    print "psi_2 =", geom(q);
    print "psi_1 o psi_2 =", geom(p*q);
    assert geom(p*q) eq geom(q)*geom(p);
    assert #sub<A|p,q> eq #A;
    assert Order(p) eq 6 and Order(q) eq 6 and Order(p*q) eq 4;
    assert p^3 eq z and q^3 eq z and (p*q)^2 eq z and Order(z) eq 2;
    print "psi_1^3 = psi_2^3 = (psi_1 o psi_2)^2 = [-1] =", geom(z);
    assert IsIsomorphic(A,PCGroup(SL(2,3)));
    P<a,b> := FPGroup<a,b | a^3=b^3, a^3=(a*b)^2>;
    assert IsSatisfied(Relations(P),[p,q]) and #P eq #A;

    theta := hom<A -> A |
        [elt(gal(geom(A.i))) : i in [1..Ngens(A)]]>;
    assert forall{a : a in A | geom(theta(a)) eq gal(geom(a))};
    assert forall{a : a in A | theta(theta(a)) eq a};
    assert theta(p) eq q and theta(q) eq p;
    assert #[a : a in A | theta(a) eq a] eq #A0;
    print "sigma(psi_1) = psi_2 =", gal(geom(p));
    C2 := CyclicGroup(GrpPC,2);
    AutA := AutomorphismGroup(A);
    action := hom<C2 -> AutA | [theta]>;
    H, inclA, inclC, projection := SemidirectProduct(A,C2,action);
    f := inclC(C2.1);
    assert #H eq 48 and Order(f) eq 2;
    assert forall{a : a in A | f*inclA(a)*f^-1 eq inclA(theta(a))};
    assert IsIsomorphic(PCGroup(H),PCGroup(GL(2,3)));
    print "    OK: Aut(E/F_4) = SL(2,3); Aut(E/F_4) semidirect Gal(F_4/F_2) = GL(2,3).";

    G3<x,t> := FPGroup<x,t | x^3, t^2, t*x*t=x^-1>;
    G4<x,t> := FPGroup<x,t | x^4, t^2, t*x*t=x^-1>;
    G8<x,y,t> := FPGroup<x,y,t |
        x^4, y^2=x^2, y^-1*x*y=x^-1, t^2, t*x*t=y>;
    G24<x,y,t> := FPGroup<x,y,t |
        x^3=y^3, x^3=(x*y)^2, t^2, t*x*t=y>;
    assert IsSatisfied(Relations(G24),[inclA(p),inclA(q),f]) and #G24 eq #H;

    // Table entries are actual curve automorphisms; nu(t) is coefficient sigma.
    for row in [* <3,G3,[p*q^2]>, <4,G4,[q*p^2*q]>,
                  <8,G8,[z*p*q,z*q*p]>, <24,G24,[z*p^2,z*q^2]> *] do
        e,G,auts := Explode(row);
        printf "  e = %o: checking the Galois pair...\n", e;
        print "nu(x) =", geom(auts[1]);
        if e in [8,24] then print "nu(y) =", geom(auts[2]); end if;
        print "nu(t) = sigma on coefficients (c |-> c^2).";
        images := [inclA(a) : a in auts] cat [f];
        // nu(g)=rho(g)^(-1): verify the antihomomorphism, not a homomorphism.
        assert IsSatisfied(Relations(G),[a^-1 : a in images]);
        rho := hom<G -> H | [a^-1 : a in images]>;
        J := Image(rho); Gamma := sub<H | [inclA(a) : a in auts]>;
        assert #G eq 2*e and #J eq 2*e and #Gamma eq e;
        assert Gamma subset Image(inclA) and f notin Gamma and Gamma^f eq Gamma;
        assert forall{a : a in auts | projection(inclA(a)) eq C2!1};
        assert projection(f) eq C2.1;
        assert exists{a : a in auts | theta(a) ne a}; // F_4 is minimal.
        assert Order(auts[1]) eq (e eq 24 select 6 else (e eq 8 select 4 else e));
        if e eq 8 then
            assert auts[1]^2 eq z and auts[2]^2 eq z;
            assert auts[2]^-1*auts[1]*auts[2] eq auts[1]^-1;
        elif e eq 24 then
            assert #Gamma eq #A and Order(auts[2]) eq 6;
        end if;
        printf "    OK: injective antihomomorphism; image order %o, inertia order %o.\n", #J,#Gamma;
    end for;

    for c in [0,1] do
        printf "  a_2 = %o: checking both cyclic C_4 pairs over F_2...\n", 4*c-2;
        C := EllipticCurve([GF(2)|0,0,1,1,c]);
        B, evB := AutomorphismGroup(C);
        B4 := AutomorphismGroup(BaseExtend(C,k));
        u := Automorphism(C,[GF(2)|1,1,0,1]);
        assert #B eq 4 and #B4 eq 4 and 3-#C eq 4*c-2;
        assert u*u eq NegationMap(C);
        assert (u*u)*(u*u) eq IdentityMap(C);
        print C;
        print "u =", u;
        print "u o u = [-1] =", u*u;
        for m in [u,Inverse(u)] do
            b := Rep({a : a in B | evB(a) eq m});
            assert Order(b) eq 4; // Each choice nu(x)=u or u^-1 is injective.
        end for;
        print "    OK: trace, automorphism group and both injective C_4 pairs.";
    end for;
end procedure;

procedure CheckAll()
    SetAssertions(1);
    print "[1/3] Exceptional curves: good reduction over the eight fields";
    CheckExceptionalFields();
    print "[2/3] Matrix changes of basis and rational traces";
    CheckMatrices();
    print "[3/3] Automorphisms and Galois pairs";
    CheckGaloisPairs();
    print "All checks passed (with the exceptional-table permutation stated above).";
end procedure;
CheckAll();

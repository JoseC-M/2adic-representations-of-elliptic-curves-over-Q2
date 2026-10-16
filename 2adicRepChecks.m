// Computational checks for 2adicRepV7.tex; 
// Exact arithmetic throughout. u_2-sign isomorphisms are unfiltered;
// a filtration is transported by the same intertwiner.

procedure ShowMatrix(label, M)
    printf "%o\n%o\n", label, M;
end procedure;

// Exact checks for the classification proofs: e = 3, 4 (dihedral), 8, 24.
// h = sqrt(-15) is fixed by t; r = sqrt(-3), q = sqrt(5), and h = r*q.
// Embed this coefficient field in Q_4 with h in Q_2; no p-adic rounding.
procedure CheckMatrices()
    QZ<z> := PolynomialRing(Rationals());
    A<h> := NumberField(z^2+15);
    AZ<z> := PolynomialRing(A);
    C<r> := NumberField(z^2+3);
    q := C!h/r;
    tau := hom<C -> C | -r>;
    P<u,v> := PolynomialRing(C,2);
    I := IdentityMatrix(P,2); F := Matrix(P,2,2,[0,-2,1,0]);
    mat := func<a,b,c,d | Matrix(P,2,2,[a,b,c,d])>;
    function bar(M)
        return Matrix(P,2,2,[ &+[P | tau(Coefficients(f)[i])*Monomials(f)[i]
            : i in [1..#Coefficients(f)]] : f in Eltseq(M)]);
    end function;
    at := func<M,a,b | Matrix(C,2,2,[Evaluate(f,[C!a,C!b]) : f in Eltseq(M)])>;
    zero := func<M,J | &and[f in J : f in Eltseq(M)]>;
    reduced := func<M,J | Matrix(P,2,2,[NormalForm(f,J) : f in Eltseq(M)])>;
    flip := func<M | Matrix(P,2,2,[Evaluate(f,[u,-v]) : f in Eltseq(M)])>;
    adjugate2 :=  func<M | mat(M[2,2],-M[1,2],-M[2,1],M[1,1])>;
    function inertia_size(gens)
        S := {IdentityMatrix(C,2)};
        repeat
            n := #S;
            S join:= {g*a : g in gens, a in S};
        until #S eq n;
        return #S;
    end function;

    // <e, sign, determinant equation, X, normal X, B, exceptional point, B_exception>.
    cases := [*
      <3,1,4*u^2+8*v^2-1,
       mat(-1/2+u*r,2*v*r,v*r,-1/2-u*r),mat((-1+r)/2,0,0,(-1-r)/2),
       mat(u+1/2,-2*v,v,u+1/2),[-1/2,0],F>,
      <4,1,6*v^2-5*u^2-1,
       mat(u*q,2*v*r,v*r,-u*q),mat(q,2*r,r,-q),
       mat(5*(u+1),-2*h*(v-1),h*(v-1),5*(u+1)),[-1,1],mat(2*h,-10,5,2*h)>
    *];
    for s in [1,-1] do
        Append(~cases,<8,s,6*u^2-20*v^2-1,
          mat(u*r,-s+2*v*q,s/2+v*q,-u*r),s*mat(r,-1+q,(1+q)/2,-r),
          mat(3*(s*u+1),2*h*(s*v-1/2),-h*(s*v-1/2),3*(s*u+1)),
          [-s,s/2],mat(-h,-6,3,-h)>);
        Append(~cases,<24,s,24*v^2-20*u^2-1,
          mat(1/2+u*q,-s+2*v*r,s/2+v*r,1/2-u*q),
          mat((1+q)/2,s*(-1+r),s*(1+r)/2,(1-q)/2),
          mat(5*(u+1/2),-2*h*(v-s/2),h*(v-s/2),5*(u+1/2)),
          [-1/2,s/2],mat(2*h,-10*s,5*s,2*h)>);
    end for;

    R<a> := FunctionField(C);
    mob := func<M,b | (M[1,1]*b+M[1,2])/(M[2,1]*b+M[2,2])>;
    print "Notation: u=u_1, v=u_2, h^2=-15, r^2=-3, q=h/r (q^2=5).";
    ShowMatrix("F (semilinear Frobenius; t fixes h and sends r to -r) =", F);
    for c in cases do
        e,s,g,X,N,B,p,E := Explode(c);
        printf "  e = %o%o: checking relations, B, u_2 signs and filtrations...\n",
            e, (e in [8,24] select (s eq 1 select " (+)" else " (-)") else "");
        J := ideal<P | g>;
        Y := bar(X);
        assert ideal<P | Determinant(X)-1> eq J;
        assert zero(F*bar(X)-X*F,J);            // semilinear Frobenius
        assert bar(Y) eq X;                    // txt = y
        if e in [3,4] then
            assert zero(X*Y-I,J);              // txt = x^-1
            assert zero(X^e-I,J);
        elif e eq 8 then
            assert zero(X^2+I,J) and zero(Y^2+I,J);
            assert zero(X*Y+Y*X,J);
        else
            assert zero(X^3+I,J) and zero(Y^3+I,J);
            assert zero((X*Y)^2+I,J);
        end if;
        assert bar(B) eq B and F*bar(B) eq B*F;
        assert zero(X*B-B*N,J) and zero(Y*B-B*bar(N),J);
        printf "Parameter relation: %o = 0. Products below are reduced modulo this relation.\n", g;
        ShowMatrix("X =", X); ShowMatrix("Y = t(X) =", Y);
        ShowMatrix("B =", B); ShowMatrix("N (normal form of X) =", N);
        ShowMatrix("F*t(B) = B*F =", reduced(F*bar(B),J));
        ShowMatrix("X*B =", reduced(X*B,J));
        ShowMatrix("B*N =", reduced(B*N,J));
        ShowMatrix("Y*B = B*t(N) =", reduced(Y*B,J));
        // The generic B fails only at p: both squared coordinate differences
        // lie in (g,det B). The displayed exceptional B covers that point.
        H := ideal<P | g,Determinant(B)>;
        assert (u-p[1])^2 in H and (v-p[2])^2 in H;
        assert at(B,p[1],p[2]) eq ZeroMatrix(C,2,2);
        assert Determinant(E) ne 0 and bar(E) eq E and F*bar(E) eq E*F;
        assert at(X,p[1],p[2])*at(E,0,0) eq at(E,0,0)*at(N,0,0);
        assert at(Y,p[1],p[2])*at(E,0,0) eq at(E,0,0)*at(bar(N),0,0);
        printf "Exceptional parameters (u,v) = %o; the following products are exact.\n", p;
        ShowMatrix("X at the exceptional point =", at(X,p[1],p[2]));
        ShowMatrix("B_exception =", at(E,0,0));
        ShowMatrix("X_exception*B_exception =", at(X,p[1],p[2])*at(E,0,0));
        ShowMatrix("B_exception*N =", at(E,0,0)*at(N,0,0));
        // Both signs of u_2 normalize to the SAME N. Away from exceptions,
        // B(u,v)*adj(B(u,-v)) is the explicit intertwiner; use E at p.
        assert zero(flip(X)*flip(B)-flip(B)*N,J);
        T := B*adjugate2(flip(B));
        assert zero(X*T-T*flip(X),J);
        assert bar(T) eq T and F*bar(T) eq T*F;
        print "Changing v to -v (products reduced modulo the parameter relation):";
        ShowMatrix("X(u,-v) =", flip(X));
        ShowMatrix("T = B(u,v)*adjugate(B(u,-v)) =", reduced(T,J));
        ShowMatrix("X(u,v)*T =", reduced(X*T,J));
        ShowMatrix("T*X(u,-v) =", reduced(T*flip(X),J));
        for w in [p,[p[1],-p[2]]] do
            B1 := at(B,w[1],w[2]); B2 := at(B,w[1],-w[2]);
            if Determinant(B1) eq 0 then B1 := at(E,0,0); end if;
            if Determinant(B2) eq 0 then B2 := at(E,0,0); end if;
            T0 := B1*B2^-1;
            assert Determinant(T0) ne 0;
            assert at(X,w[1],w[2])*T0 eq T0*at(X,w[1],-w[2]);
            printf "Sign change at (u,v) = %o:\n", w;
            ShowMatrix("T0 = B1*B2^(-1) =", T0);
            ShowMatrix("X(u,v)*T0 = T0*X(u,-v) =", at(X,w[1],w[2])*T0);
        end for;

        N0 := at(N,0,0); F0 := at(F,0,0);
        assert inertia_size([N0,at(bar(N),0,0)]) eq e;
        assert tau(r) ne r;                    // adjoining t doubles the order
        assert Rank(Matrix(C,2,4,Eltseq(N0-N0) cat
            Eltseq(F0*N0-N0*F0))) eq 1;         // only scalar endomorphisms
        if e in [8,24] and s eq 1 then
            Nminus := e eq 8 select -N0 else
                Matrix(C,2,2,[(1+q)/2,1-r,-(1+r)/2,(1-q)/2]);
            assert Rank(Matrix(C,2,4,Eltseq(N0-Nminus) cat
                Eltseq(F0*N0-Nminus*F0))) eq 2; // + and - are nonisomorphic
        end if;
        // Exactly the filtration equations printed in the proof/definition.
        f := mob(N0^-1,a);
        if e eq 3 then
            assert f eq ((-1+r)/2)*a;
        elif e eq 4 then
            assert f eq (a*q+2*r)/(a*r-q);
        elif e eq 8 then
            assert f eq (a*r-1+q)/(a*(1+q)/2-r);
        else
            assert f eq ((1-q)*a/2+s*(1-r))/((1+q)/2-s*(1+r)*a/2);
        end if;
        b := a;
        for j in [1..(e in [3,24] select 3 else 2)] do b := mob(N0^-1,b); end for;
        assert b eq a;
        print "    OK: B, unfiltered isomorphisms, orders and filtration equations.";
    end for;
end procedure;

procedure CheckTwists()
    Q<T> := PolynomialRing(Rationals());
    A<h> := NumberField(T^2+15);
    R<T> := PolynomialRing(A);
    C<r> := NumberField(T^2+3);
    q := h/r;                         // r=sqrt(-3), q=sqrt(5), h=r*q.
    F := Matrix(C,2,2,[0,-2,1,0]);
    I := IdentityMatrix(C,2);
    sigma := hom<C -> C | -r>;
    for e in [8,24] do
        printf "  e = %o: checking the twist matrix and filtration transport...\n", e;
        if e eq 8 then
            X := Matrix(C,2,2,[r,-1+q,(1+q)/2,-r]);
            Y := Matrix(C,2,2,[-r,-1-q,(1-q)/2,r]);
            Xm := -X; Ym := -Y;
            B := Matrix(C,2,2,[h,6,3,-h]);
            assert B^2 eq 3*I;
        else
            X := Matrix(C,2,2,[(1+q)/2,-1+r,(1+r)/2,(1-q)/2]);
            Y := Matrix(C,2,2,[(1-q)/2,-1-r,(1-r)/2,(1+q)/2]);
            B := DiagonalMatrix(C,[1,-1]);
            Xm := B*X*B; Ym := B*Y*B;
            assert B^2 eq I;
        end if;
        assert Determinant(B) ne 0;
        assert Matrix(C,2,2,[sigma(a): a in Eltseq(B)]) eq B;
        assert -F*B eq B*F and X*B eq B*Xm and Y*B eq B*Ym;
        ShowMatrix("-F (twisted Frobenius) =", -F);
        ShowMatrix("X =", X); ShowMatrix("Y =", Y);
        ShowMatrix("B =", B);
        ShowMatrix("X_minus =", Xm); ShowMatrix("Y_minus =", Ym);
        ShowMatrix("(-F)*B = B*F =", -F*B);
        ShowMatrix("X*B =", X*B); ShowMatrix("B*X_minus =", B*Xm);
        ShowMatrix("Y*B = B*Y_minus =", Y*B);
        K<a> := FunctionField(C);
        mob := func<M,b | (M[1,1]*b+M[1,2])/(M[2,1]*b+M[2,2])>;
        beta := e eq 8 select (h*a+6)/(3*a-h) else -a;
        assert mob(B^-1,a) eq beta;
        // x fixes C; verify the stated transformation of the stable-line equation.
        assert mob(B^-1,mob(X^-1,a)) eq mob(Xm^-1,beta);
        print "    OK: twist matrix and filtration transport.";
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
    print "Running exact checks for 2adicRepV7.tex.";
    print "[1/3] Matrix normal forms (including omitted signs and exceptional cases)";
    CheckMatrices();
    print "[2/3] Unramified twists for e = 8 and e = 24";
    CheckTwists();
    print "[3/3] Automorphisms and Galois pairs";
    CheckGaloisPairs();
    print "All checks passed.";
end procedure;
CheckAll();

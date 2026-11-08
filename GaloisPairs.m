// Lemma 11.4, Table 4. The four antihomomorphisms with trace zero.

// In the basis (0,0),(1,w) of E3[3], Lemma 11.2 identifies the target
// with GL(2,3). Its geometric subgroup is SL(2,3), so the determinant
// is the projection to Gal(F4/F2). Matrix multiplication is composition.
k := GF(3);
H := GL(2,3);
p := H!Matrix(k,2,2,[1,-1, 1,0]);   // psi_1
q := H!Matrix(k,2,2,[1,1, -1,0]);   // psi_2
z := H!Matrix(k,2,2,[-1,0, 0,-1]);  // [-1]
f := H!Matrix(k,2,2,[1,0, 0,-1]);   // coefficient conjugation
assert p^3 eq z and q^3 eq z and f*p*f^-1 eq q;
assert Order(f) eq 2 and Determinant(f) eq -1;

// For each row, rho(g)=nu(g)^(-1) is a homomorphism. Check its relators
// on the inverse matrices, and compare the source order with the image
// order to verify injectivity. Since det(f)=-1 and f normalizes Gamma,
// the full image is Gamma semidirect <f>. If f does not centralize nu(x),
// the displayed inertia action requires F4.

// e=3. G=S3 and Gamma=C3.
G<x,t> := FPGroup<x,t | x^3,t^2,t*x*t=x^-1>;
nx := p*q^2;  nt := f;
rx := nx^-1;  rt := nt^-1;
assert rx^3 eq H!1 and rt^2 eq H!1 and rt*rx*rt eq rx^-1;
full := sub<H | nx,nt>;
Gamma := sub<H | nx>;
assert Order(nx) eq 3 and #Gamma eq 3;
assert Determinant(nx) eq 1 and Gamma^f eq Gamma and f*nx*f^-1 ne nx;
assert #G eq 6 and #full eq #G;
print "e=3: inertia and full image orders",#Gamma,#full;

// e=4. G=D4 and Gamma=C4.
G<x,t> := FPGroup<x,t | x^4,t^2,t*x*t=x^-1>;
nx := q*p^2*q;  nt := f;
rx := nx^-1;  rt := nt^-1;
assert rx^4 eq H!1 and rt^2 eq H!1 and rt*rx*rt eq rx^-1;
full := sub<H | nx,nt>;
Gamma := sub<H | nx>;
assert Order(nx) eq 4 and nx^2 eq z and #Gamma eq 4;
assert Determinant(nx) eq 1 and Gamma^f eq Gamma and f*nx*f^-1 ne nx;
assert #G eq 8 and #full eq #G;
print "e=4: inertia and full image orders",#Gamma,#full;

// e=8. G=SD16 and Gamma=Q8.
G<x,y,t> := FPGroup<x,y,t | x^4,y^2=x^2,y^-1*x*y=x^-1,t^2,t*x*t=y>;
nx := z*p*q;  ny := z*q*p;  nt := f;
rx := nx^-1;  ry := ny^-1;  rt := nt^-1;
assert rx^4 eq H!1 and ry^2 eq rx^2 and ry^-1*rx*ry eq rx^-1;
assert rt^2 eq H!1 and rt*rx*rt eq ry;
full := sub<H | nx,ny,nt>;
Gamma := sub<H | nx,ny>;
assert nx^2 eq z and ny^2 eq z and (nx*ny)^2 eq z and #Gamma eq 8;
assert Determinant(nx) eq 1 and Determinant(ny) eq 1;
assert Gamma^f eq Gamma and f*nx*f^-1 ne nx;
assert #G eq 16 and #full eq #G;
print "e=8: inertia and full image orders",#Gamma,#full;

// e=24. G=GL(2,3) and Gamma=SL(2,3).
G<x,y,t> := FPGroup<x,y,t | x^3=y^3,x^3=(x*y)^2,t^2,t*x*t=y>;
nx := z*p^2;  ny := z*q^2;  nt := f;
rx := nx^-1;  ry := ny^-1;  rt := nt^-1;
assert rx^3 eq ry^3 and rx^3 eq (rx*ry)^2;
assert rt^2 eq H!1 and rt*rx*rt eq ry;
full := sub<H | nx,ny,nt>;
Gamma := sub<H | nx,ny>;
assert Determinant(nx) eq 1 and Determinant(ny) eq 1 and #Gamma eq #SL(2,3);
assert Gamma^f eq Gamma and f*nx*f^-1 ne nx;
assert #G eq 48 and #full eq #G and full eq H;
print "e=24: inertia and full image orders",#Gamma,#full;

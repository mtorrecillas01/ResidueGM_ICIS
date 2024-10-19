// Computation of the Gauss-Manin connection of an ICIS

Q := RationalField();
Z := IntegerRing();

// Order of f
Order := function(f)
 if f in Z then
  return 0;
 else
  of := Min([Degree(m) : m in Monomials(f)]);
  return of;
 end if;
end function;

// k-jet of a polynomial
jetK := function(f, k)
 R := Parent(f);
 return &+[R| x : x in Terms(f) | Degree(x) le k];
end function;

//Inverse of a unit until order N
InverseUnit := function(u, N)
 Part := func<f, k | &+[Parent(f) | m : m in Terms(f) | Degree(m) eq k]>;

 u0 := LeadingTerm(u); v := 1/u0;

 for i in [1..N] do
  v -:= &+[(Part(v, k)*Part(u, i - k))/u0 : k in [0..(i-1)]];
 end for;

 return v;
end function;

// Jacobian matrix of a (local) polynomial map given by F = (f1,...,fk)
jacobMat := function(F)
 R := Universe(F);
 N := Rank(R);
 k := #F;
 S := [Derivative(F[i],j) : j in [1..N], i in [1..k]];
 return Matrix(R,k,N,S);
end function;

// Returns the kxk minors of the jacobian matrix of F (k = #F) and the corresponding indices
minors_ind := function(F)
 R := Universe(F);
 N := Rank(R);
 k := #F;
 I := [1..k];
 Ind := {1..N};
 J := [Sort(Setseq(s)) : s in Subsets(Ind,k)]; // sorted subsets of card k of {1..N}
 DF := jacobMat(F);
 Min := [Minor(DF,I,j) : j in J];

 return Min, J;

end function;

// Returns true if the ideal I defines an icis
IsIcis := function(I)
 R := Universe(Basis(I));
 N := Rank(R);
 k := #Basis(I);
 Max := Ideal([R.i : i in [1..N]]);
 M := jacobMat(Basis(I));
 kMin := Minors(M,k);
 S := Basis(I) cat kMin;
 J := Ideal(S);
 RJ := R/J;
 if HasFiniteDimension(RJ) then return true;
 else return false; end if;
end function;

// Find "canonical form" of the icis defined by the ideal I
// We apply an upper triangular generic linear change of coordinates
nf_icis := function(I)
 F := Basis(I);
 R := Universe(F);
 N := Rank(R);
 k := #F;

 // General linear change of coordinates
 M := (k^2+k-2)/2;
 S := [Random(Z,50) : i in [1..M]] cat [Q|1];  // we pick it upper triangular with 1 in position s_kk
 P := UpperTriangularMatrix(S);
 while Determinant(P) eq 0 do
  S := [Random(Z,50) : i in [1..M]] cat [Q|1];
  P := UpperTriangularMatrix(S);
 end while;
 
 // Apply the change of coordinates
 F2 := [&+[P[i,j]*F[j] : j in [1..k]] : i in [1..k]];

 b1 := false; // true if, after the change of coordinates, F_(l) is icis for l = 1,..,k
 while not b1 do
  b2 := true; // true if (f1,..,fl) is an icis for the current l and lower values
  l := 1;
  while b2 and l le k do
   J := Ideal([F2[i] : i in [1..l]]);
   b2 := IsIcis(J);
   l := l+1;
  end while;
  if not b2 then // look for another change of coordinates
   S := [Random(Z,50) : i in [1..M]] cat [Q|1];
   P := UpperTriangularMatrix(S);
   while Determinant(P) eq 0 do
    S := [Random(Z,50) : i in [1..M]] cat [Q|1];
    P := UpperTriangularMatrix(S);
   end while;
   F2 := [&+[P[i,j]*F[j] : j in [1..k]] : i in [1..k]];
  else b1 := true;
  end if;
 end while;

 return IdealWithFixedBasis(F2), P;

end function;

// Milnor number of an icis I (in normal form)
MilnorNumber := function(I)
 F := Basis(I);
 R := Universe(F);
 N := Rank(R);
 k := #F;

 f := F[1];
 Jacobian := Ideal([Derivative(f,i) : i in [1..N]]);
 RJ := R/Jacobian;
 mu := (-1)^(k-1)*Dimension(RJ);
 
 MilnAlg := func<F,i | R/(Ideal([F[j] : j in [1..i-1]]) + Ideal(Minors(jacobMat(F), Min({i,N}))))>;
 if k gt 1 then
  mu := mu + &+[(-1)^(k-i)*Dimension(MilnAlg(F,i)) : i in [2..k]];
 end if;

 return mu;

end function;

// Discriminant when the domain is non smooth (X = ideal defining the domain)
discriminant := function(I, X)
  R := Universe(Basis(I)); 
  n := Rank(R); // Ambient dimension
  m := #Basis(I);
  //Codimension
  if IsZero(X) then 
   k := m;
  else 
   k := m + #Basis(X);
  end if;

  M := Minors(jacobMat(Basis(I) cat Basis(X)), k) cat Basis(X);

  S := PolynomialRing(BaseRing(R), n + m, "elim", n);
  Phi := hom<R -> S | [S.i : i in [1..n]]>;
  AssignNames(~S, Names(R) cat ["T" cat IntegerToString(i - 1) : i in [1..m]]);

  J := ideal<S | [Phi(m) : m in M] cat [Phi(Basis(I)[i]) - S.(i + n) : i in [1..m]]>;
  Groebner(J);

  S := Universe(Basis(J));
  Disc := [g : g in Basis(J) | Evaluate(g, [0 : i in [1..n]] cat
  [S.(i + n) : i in [1..m]]) eq g];
 
  T := LocalPolynomialRing(BaseRing(R), m);
  AssignNames(~T, ["t" cat IntegerToString(i - 1) : i in [1..m]]);
  Phi := hom<S -> T | [0 : i in [1..n]] cat [T.i : i in [1..m]]>;

  // Discriminant equation
  D := Phi(Disc[1]);
  return D;
end function;

// Find minimal k with u*f^k in C_f for a unit u, and the coordinates xi
jacoblift := function(F)
 R := Universe(F);
 k := #F;
 BI, J := minors_ind(F); // J are the indices
 BI := BI cat [F[i] : i in [1..k-1]];
 I := IdealWithFixedBasis(BI); // Critical ideal
 r := 1;
 f := F[k];

 while f^r notin I do
  r := r + 1;
 end while;

 xi, u := Coordinates(I, f^r);

 return r, xi, J, u;

end function;

// get V (basis of a complementary subspace of H_f"/t^KH_f")
getV1 := function(f,X,K,N)
 R := Parent(f);
 Max := Ideal([R.i : i in [1..Rank(R)]]);
 RM := R/Max^(N - K*Order(f)+1);
 F := hom<RM -> R | Basis(Max)>;
 V1 := [R | f^K*m : m in F(MonomialBasis(RM))];
 V1 := [R|jetK(v,N-1) : v in V1];

 if IsZero(X) then
  return V1;
 else 
  RM := R/Max^N;
  Phi := hom<RM -> R | Basis(Max)>;
  F := Basis(X);
  V1 := V1 cat [R | F[i]*m : m in Phi(MonomialBasis(RM)), i in [1..#F]];
  return [R| jetK(v,N-1) : v in V1];
 end if;
end function;

getV2 := function(f,X,M) // until order M-1
 R := Parent(f);
 if IsZero(X) then
  F := [f];
 else
  F := Basis(X) cat [R|f];
 end if;
 k := #F;
 N := Rank(R);
 Ind := {1..N};
 DF := jacobMat(F);

 Max := Ideal([R.i : i in [1..N]]);
 RM := R/Max^(M+1);
 Phi := hom<RM -> R | Basis(Max)>;

  V2 := [&+[R | (-1)^i * Minor(DF, [1..k], Remove(J, i)) * Derivative(m, J[i]) : i in [1..k + 1]] : m in Phi(MonomialBasis(RM)), \
  J in [Setseq(J): J in Subsets({1..N}, k + 1)]];

 return [R|jetK(v,M-1) : v in V2];

end function;

// get basis of H2/t^K H2 from a basis e of H2/tH2
getVe := function(f,e,K)
 R := Parent(f);
 return [R | f^j*e[i] : i in [1..#e], j in [0..(K-1)]];
end function;

// codimension of <S>_C in C{z}/m^N
codim := function(S,N)
 R := Universe(S);
 Max := Ideal([R.i : i in [1..Rank(R)]]);
 RM := R/(Max^N);
 V, Phi := VectorSpace(RM);
 D := Dimension(V);
 if IsEmpty(S) or IsZero(Ideal(S)) then
  return D;
 else
  WS := Phi(S);
  M := Matrix(BaseRing(R),#S,D,WS);
  codim := D - Rank(M);
  return codim;
 end if;
end function;

// basis of the quotient (C{z}/m^N)/(<S>_C/m^N)
quotbas := function(S,N)
 R := Universe(S);
 Max := Ideal([R.i : i in [1..Rank(R)]]);
 RM := R/Max^N;
 V, Phi := VectorSpace(RM);
 if IsEmpty(S) then
  U := V;
 else
  WS := sub<V | Phi(S)>;
  U := Complement(V,WS);
 end if;
 B := Basis(U);
 Psi := Inverse(Phi); // from coordinates to polynomials
 F := hom<RM -> R | [R.i : i in [1..Rank(R)]]>; // lift from the quotient
 return F(Psi(B));
end function;

// Increase K by dK, compute N(K) and update V1, V2,Ve
incK := function(f,X,mu,K,deltaK,N,e)
 R := Parent(f);
 deltaN := deltaK*Order(f);

 V1 := getV1(f,X,K+deltaK,N+deltaN);
 V2 := getV2(f,X,N+deltaN);

 Ve := getVe(f,e,K+deltaK);

 K := K+deltaK;
 N := N+deltaN;
 deltaN := 1;

 if IsZero(X) then k := 1;
 else k := #Basis(X) + 1;
 end if;

 if Rank(R)-k eq 0 then A := K*(mu+1);
 else A := K*mu;
 end if;

 while codim(V1 cat V2, N) lt A do
  V1 := getV1(f,X,K,N+deltaN);
  V2 := getV2(f,X,N+deltaN);

  N := N+deltaN;
 end while;

 return V1,V2,Ve,N,K;

end function;

// Use explicit formulas to compute t^k \partial_t restricted to the Brieskorn lattice
nablaK := function(f,X,kappa,xi,u,N,e)
 R := Parent(f);
 xi := [jetK(a,N) : a in xi];
 u := InverseUnit(u,N);
 fkappa := kappa*f^(kappa-1);
 n := Rank(R);
 
 if IsZero(X) then 
  k := 1;
  DF := Matrix(R,1,1,[1]);
 else 
  F := Basis(X);
  k := #F + 1;
  DF := jacobMat(F);
 end if;

 
 Ind := {1..n};
 I := [Sort(Setseq(s)) : s in Subsets(Ind,k)]; // sorted subsets of card k of {1..n}
 m := #I;

 Vnablae := [R|];
 for i in [1..(#e)] do
  q := [jetK(e[i]*xi[j],N) : j in [1..m]]; // By construction, xi is ordered in the same way as S1
  p := &+[&+[(-1)^(k-l)*Minor(DF,[1..k-1],Remove(I[j],l))*Derivative(q[j]*u,I[j,l]) : l in [1..k]] : j in [1..m]] - fkappa*e[i];
  Vnablae[i] := jetK(p,N-1);
 end for;
 return Vnablae;
end function;

// Matrix of t^k*\partial_t in basis e dz
residue := function(f,X,mu,kappa,xi,u,K,N,e,V1,V2,Ve,S)
 R := Parent(f);
 n := Rank(R);
 Vnablae := nablaK(f,X,kappa,xi,u,N,e); // aproximation of order K-1 of t^kappa*Nabla(e dz)
 V := Ve cat V1 cat V2; // C-basis of Omega^{n+1}/m^N Omega^{n+1} (Revise this!)

 // Transform V, Vnablae into matrices
 // we work in the canonical basis of Omega^{n+1}/m^N Omega^{n+1}
 Max := Ideal([R.i : i in [1..n]]);
 RM := R/Max^(N);
 E, Phi := VectorSpace(RM);
 Psi := Inverse(Phi);
 D := Dimension(E);

 // We are interested in row spaces
 A := [Coordinates(E,Phi(v)) : v in V];
 MV := Matrix(BaseField(E),#V,D,A);

 B := [Coordinates(E,Phi(v)) : v in Vnablae];
 MB := Matrix(BaseField(E),#(Vnablae),D,B);

 //Obtain the matrix C st C*A = B: coordinates of Vnablae in basis V
 b, C1 := IsConsistent(MV,MB);

 // Choose the columns of C corresponding to the coordinates in the subspace Ve
 if b then
  C := ColumnSubmatrix(C1, 1, #Ve);
 else
  C := ZeroMatrix(S,#Vnablae,#Ve);
  printf "Inconsistent system  \n";
 end if;


 // Change from C{z} (R) to C{t} (S)
 ElmM := [&+[S|C[i,j+k*(#e)]*(S.1)^k : k in [0..(K-1)]] : j in [1..#e], i in [1..#e]];
 M := Matrix(S,#e,#e,ElmM);

 return M;
end function;

// k-jet of a matrix
jetM := function(M,k)
 R := CoefficientRing(M);
 m := NumberOfRows(M);
 n := NumberOfColumns(M);
 S := [jetK(M[i,j],k) : j in [1..n], i in [1..m]];
 return Matrix(R,m,n,S);
end function;

// First derivative of a matrix with respect to R1
Der := function(U)
 R := CoefficientRing(U);
 m := NumberOfRows(U);
 n := NumberOfColumns(U);
 S := [R|Derivative(U[i,j],1) : j in [1..n], i in [1..m]];
 return Matrix(R,m,n,S);
end function;

// Divide all the elements of a matrix of polynomials in a ring R by p in R
divMat := function(M,p)
 R := CoefficientRing(M);
 S := PolynomialRing(BaseRing(R),Rank(R));
 m := NumberOfRows(M);
 n := NumberOfColumns(M);
 L := [R!(S!M[i,j] div S!p) : j in [1..n], i in [1..m]];
 return Matrix(R,m,n,L);
end function;

// Order of a square matrix of polynomials
OrdMat := function(U)
 n := NumberOfRows(U);
 ord := 0;
 if not U in MatrixAlgebra(RationalField(),n) then
  ord := Min([Degree(U[i,j]) : i in [1..n], \
   j in [1..n]| not U[i,j] in RationalField()]); // to avoid optional outputs
 end if;
 return ord;
end function;

// Saturation (following Gerard and Levelt) and computation of the residue matrix
sat := function(f,X,mu,kappa,xi,u,e)
 R2 := Parent(f);
 R<t> := LocalPolynomialRing(BaseRing(R2),1); // C{t} in the theory

 // Codimension of the icis
 if IsZero(X) then k := 1;
 else k := #Basis(X) + 1;
 end if;

 // Particular case of a point
 if Rank(R2) - k eq 0 then D := mu + 1;
 else D := mu;
 end if;

 U := (R.1)^((D-1)*(kappa-1))*ScalarMatrix(R,D,1); // We start with the canonical basis of C{t}^mu shifted t^(mu-1)*(k-1)
 prevU := ZeroMatrix(R,D);

 Mod := EModule(R,D); // ambient module, C{t}^mu
 L1 := sub<Mod | 0>; // submodule associated to the matrix prevU
 C2 := [U[i] : i in [1..D]];
 L := sub<Mod | C2>; // submodule associated to matrix U

 i := D-1;
 K := 0;
 N := 0;

 while L1 ne L and i ge 1 do // we have to iterate at most until j = mu-1 and stop when L_{j+1} = L_j
  prevU := U;
  V1,V2,Ve,N,K := incK(f,X,mu,K,kappa-1,N,e); // consider a higher approximation of the matrix M
  M := residue(f,X,mu,kappa,xi,u,K,N,e,V1,V2,Ve,R);
  U2 := divMat(prevU*M,(R.1)^(kappa-1));
  U3 := (R.1)*Der(prevU);

  C1 := [prevU[j] : j in [1..D]];
  C2 := [U2[j] : j in [1..D]];
  C3 := [U3[j] : j in [1..D]];

  L1 := sub<Mod | C1>; // submodule associated to the matrix prevU
  L2 := sub<Mod | C2>; // submodule associated to matrix U2
  L3 := sub<Mod | C3>; // submodule associated to matrix U3
  L := L1 + L2 + L3;
  Groebner(L); Groebner(L1);
  U := BasisMatrix(L);
  U := jetM(U,(kappa-1)*(D-1));

  i := i-1;
 end while;

 // Determine the change of coordinates to the saturated latttice
 C := [U[j] : j in [1..D]];
 L := sub<Mod | C>;
 Groebner(L);
 U := BasisMatrix(L);

 // We divide U by t^{pol U}
 O := OrdMat(U);
 U := divMat(U,(R.1)^O);
 beta := (D-1)*(kappa-1)-O;

 printf "Lattice resulting from the saturation \n";
 U;

 // We apply the change of basis to the connection matrix
 printf "Computing determinant and adjoint matrix of U \n";
 adjU := Adjoint(U);
 det := Determinant(U);
 if det eq 0 then
  printf "Non invertible U \n";
  M := ZeroMatrix(R,D,D);
 else
  odt := Order(det);
  oadj := Min([Order(e) : e in Eltseq(adjU) | e ne 0]);
  adjU := divMat(adjU, (R.1)^oadj);
  if K lt kappa+odt-oadj then // check if we need a higher approximation of the connection matrix
   V1,V2,Ve,N,K := incK(f,X,mu,K,kappa+odt-oadj-K,N,e);
   M := residue(f,X,mu,kappa,xi,u,K,N,e,V1,V2,Ve,R);
  end if;

  S := PolynomialRing(BaseRing(R),1);
  invUDet := S!InverseUnit(ExactQuotient(det, (R.1)^odt), kappa+odt-oadj-1);
  A := invUDet*((R.1)^(kappa)*Der(U)+U*(M-beta*(R.1)^(kappa-1)*ScalarMatrix(D,1)))*adjU;
  M := divMat(A,(R.1)^(kappa+odt-oadj-1));
 end if;

 return M;

end function;

// MAIN
S<t> := LocalPolynomialRing(Q,1);

// ICIS
R<x,y,z> := LocalPolynomialRing(Q,3);
I := Ideal([x*y+z^3, x^2+y*z]);

printf "The ideal I defines an icis: \n";
IsIcis(I);
I, P := nf_icis(I); // we keep calling I the ideal with the new generators, P is the change of coordinates
F := Basis(I);
k := #F;
f := F[k]; // one-parametric smoothing
printf "Smoothing of I: \n";
f;
mu := MilnorNumber(I);
printf "Milnor Number: \n";
mu;
if k gt 1 then
 X := Ideal([F[i] : i in [1..k-1]]);
else 
 X := Ideal(Zero(R));
end if;

// Discrimiant computation (check that kappa = order(disc))
h := discriminant(Ideal(f),X);
ordDisc := Order(h);
printf "Order of the discriminant: \n";
ordDisc;

kappa, xi, J, u := jacoblift(F); // J are the indices of coordinates xi
printf "Kappa: ";
kappa;

// C{t}-basis of the Brieskorn lattice
e := [R|];

// Initially, K = 0 and dK = 1; N = 0
V1,V2,Ve,N,K := incK(f,X,mu,0,1,0,e);
e := quotbas(V1 cat V2, N); // C-basis of H2/t*H2 (and, by Nakayama, C{t}-basis of H2)
Ve := getVe(f,e,K);

printf "Cardinality of the C{t}-basis of H2: ";
#e;

printf "Saturation \n";
M := sat(f,X,mu,kappa,xi,u,e);
M0 := ChangeRing(jetM(M,0),BaseRing(CoefficientRing(M))); // residue matrix
printf "Factored Bernstein-Sato polynomial: \n";
FactoredMinimalPolynomial((-1)*M0 - ScalarMatrix(NumberOfRows(M0),1));
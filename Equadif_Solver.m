/***
 *
 *  Distributed under the terms of the GNU Lesser General Public License (L-GPL)
 *                  http://www.gnu.org/licenses/
 *
 *  Copyright (C) 2022 E. Eid
 */
 
 

 /*
   The following is a magma script that implements
   the main algorithm of the paper "Efficient computation of Cantor's division polynomials of hyperelliptic curves over finite fields" 
   by  E. Eid.

*/


// Some defines
Iso_t := recformat<f, U0, V0, W0, G>;
forward IsoSolveInternal, MySqrtInvPad, MySqrtInv, integral, MyInv, PolynomialChangePrecision, NewtonSumsAndDerivatives, MySqrtInvMod, MyInvMod, HankelProduct;


// Main function
// We look for a separable (ell, ..., ell)-isogeny defined over the p-adics from 
// y^2 = hC(x) to y^2 = hD(x)
// _Mij is the normalization matrix
// _U0, _V0, _W0, _u0, _v0 are some initial conditions
// PrP is the p-adic precision

function EquadifSolver(ell , hC , hD , _Mij, _U0 , _V0, _W0,  _u0 , _v0, PrP)
  
    vprintf SEA, 1 : "Precomputations...\n";

    CK := Parent(_u0);  /* The p-adic field*/ 
    PDef := DefiningPolynomial(CK);
    p := Prime(CK); 

    K := pAdicQuotientRing(p, PrP); 
    if PDef ne Parent(PDef).1-1 then
	K<u> := UnramifiedExtension(K, DefiningPolynomial(CK));
    end if;

    x := PolynomialRing(K).1;
    nb := NumberOfColumns(_Mij);
    N := 2*nb*ell +1;
    L<t> := LaurentSeriesRing(K : Precision := N+1); S<z> := PolynomialRing(L);  


    Mij := ZeroMatrix(L, nb , nb);
    
    for i:=1 to nb do  
        for j:=1 to nb do 
            Mij[i,j]:= L!ChangeUniverse(Eltseq(_Mij[i,j]), Integers());
        end for;
    end for;


    u0 := K!ChangeUniverse(Eltseq(_u0), Integers());
    v0 := K!ChangeUniverse(Eltseq(_v0), Integers());

    U0 := ChangeRing(_U0, L);
    V0:= ChangeRing(_V0,L);
    W0 := ChangeRing(_W0,L);
 
    u := t + u0;

    tm := Cputime(); 

    h := Parent(x)![ K!ChangeUniverse(Eltseq(Coefficient(hC , i-1)), Integers()) : i in [1..2*nb + 2] ];
    h := Evaluate(h, u);


    r0 := 1 div v0;
    r1 := - (Coefficient(h,1) * r0) div (2*Coefficient(h,0));
    r2 := -(r0 * Coefficient(h,2)) div (2*Coefficient(h,0)) - (r1^2) div (2*r0) - ( r1 * Coefficient(h,1)) div Coefficient(h,0);
    vinv := MySqrtInv(h, N: PRC0 := [* 2, [*r0 + r1*t + r2*t^2, 3*nb * ell +1*] *] );

    G := [[L!vinv]];
    for i in [1..nb-1] do   
        Append(~G , [G[i,1]*u]);
    end for;

   
    G := Mij * Matrix(L,G);
    G := [G[i,1]: i in [1..nb]];
    
    h2 := S![ K!ChangeUniverse(Eltseq(Coefficient(hD , i-1)), Integers()) : i in [1..2*nb + 2] ];
    _timings :=Cputime(tm);

    vprintf SEA, 1 : "Precomputations time: %8o \n",_timings;

    Prc:= rec<Iso_t | f :=h2 , U0:= U0 , V0 := V0, W0:=W0,  G := G>;
    
    U, timings := IsoSolveInternal(N, Prc); 

    return U,vinv,[_timings] cat timings;

end function;



// Solving the differential system 

function IsoSolveInternal(N, Prc: Timings := [])


    S<z> := Parent(Prc`U0);
    if N le 1 then
	    U := Prc`U0; 
	    return U, [RealField(6) | 0 : i in [1..5]] ;
    end if;

    M :=Ceiling((N)/2);


    U, _Timings :=IsoSolveInternal(M, Prc: Timings := Timings) ;


    vprintf SEA, 1 : "From (M+1 =) %8o to (N =) %8o ...", M+1, N;
    vprintf SEA, 2 : "\n";
    
    idxtm := 0;

    U := PolynomialChangePrecision(U,N);

    // Compting W = 1/V mod U, then V

    tm := Cputime(); 
    W := MySqrtInvMod(Prc`f, N, Prc`W0, U );    
    V := ((Prc`f mod U) * W) mod U;
    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "\t\t... W and V \t\t: %o\n", Cputime(tm);

    // Computing H(X)X' 
    tm := Cputime();
    _, Sump := NewtonSumsAndDerivatives(U , 2*#Prc`G-1, N);
    HXp:= HankelProduct(Sump, Coefficients(W));
    
    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "\t\t... H(X).X' \t\t: %o\n", Cputime(tm);

    // Compute int (G - H(X)X')
    tm:= Cputime();
    F := [integral(ChangePrecision(Prc`G[i],N)- HXp[i]): i in [1..#HXp]];
    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "\t\t... int (G - H(X)X')' \t\t: %o\n", Cputime(tm);

    // Computing U
    tm:= Cputime();
    D := z*Reverse(S!F);
    Q := U*D; Q:= S![Coefficient(Q,i) : i in [Degree(D)+1 .. 2*Degree(D)]];
    T := Q*V mod U;   
    U:= PolynomialChangePrecision(U - T , N);
    idxtm +:= 1; _Timings[idxtm] +:= Cputime(tm);
    vprintf SEA, 2 : "\t\t... U' \t\t: %o\n", Cputime(tm);


   return U,_Timings;

end function;





function PolynomialChangePrecision(P,N)
    S:=Parent(P);
    coeffs := Coefficients(P);
    return S![ChangePrecision(i,N) : i in coeffs];
end function;




// 1 / sqrt(A) computed with a Newton iteration
// --------------------------------------------
function MySqrtInv(A, N : PRC0 := [* 2, [**] *] )

    L := Parent(A); t := L.1;
    K := BaseRing(L); PR := PolynomialRing(K);

    // Initial condition
    N0 := PRC0[1];
    if N le N0 then return PRC0[2, 1]; end if;

    // Let us recurse
    M := Max(N0, (N+2) div 2);
    R := MySqrtInv(A, M : PRC0 := PRC0);
    _A := ChangePrecision(A, N+1); _R := ChangePrecision(R, N+1);

    // Newton iteration

    /* R^2 */
    H := -_R^2;

    /* 3-A*R^2 */
    H *:= _A; H +:= 3;

    /* (3-A*R^2)/2 */
    Cof, v := Coefficients(H);
    H := L!Coefficients((PR!Cof) div 2); if v ne 0 then H *:= t^v; end if; ChangePrecision(~H, N+1);

    /* R*(3-A*R^2)/2 */
    H *:= _R;

    return H;

end function;




// Computing the integral F of a power series f s.t. F(0)=0
// --------------------------------------------------------

function integral(f)

    if IsWeaklyZero(f) then
        return ChangePrecision(f, AbsolutePrecision(f)+1);
    else
coeff, a := Coefficients(f);
return ChangePrecision(Parent(f) ! ([0 : i in [0..a]] cat [coeff[i] div (i+a) : i in [1..Degree(f)-a+1]]), AbsolutePrecision(f)+1);
    end if;
end function;



// 1 / A computed with a Newton iteration
// --------------------------------------
function MyInv(A, N : PRC0 := [* 0, [**] *])

    L := Parent(A); t := L.1;

    if N lt PRC0[1] or N eq 0 then
	if #(PRC0[2]) eq 0 then
	    H := Coefficient(A, 0)^(-1) + O(t);
	    return H, [* 0, [* H *] *];
	end if;
	return PRC0[2, 1], PRC0;
    end if;

    // Let us recurse
    B, _ := MyInv(A, N div 2 : PRC0 := PRC0);
    ChangePrecision(~B, N+1);

    H  := 2 - B * ChangePrecision(A, N+1);
    H *:= B;
    
    return H, [* N, [* H *] *];
    
end function;


// Half GCD (from Thome's PHD)
// ---------------------------
function PartialGCD(U, V, z, s)

    Px := Parent(U); X := Px.1; n := Degree(U);

    if s gt Degree(V) then
    return IdentityMatrix(Px, 2);
    end if;

    if s eq Degree(V) then
    return Matrix(2,2,[Px | 0, 1, 1, - (U div V) ]);
    end if;

    m := s - (n - z);
    pi_left := $$(U div X^m, V div X^m, z-m, Ceiling((z+s)/2)-m);

    next := Vector([U, V])*pi_left;
    nU := next[1]; nV := next[2];

    m := 2*s - Degree(nU);
    pi_right := $$(nU div X^m, nV div X^m, Ceiling((z+s)/2)-m,s-m);

    return pi_left * pi_right;

end function;


// Find A and B s.t. T = A / B
// ---------------------------
function FastBerlekampMassey(ell, T)

    L := Parent(T); t := L.1;
    K := CoefficientRing(L); PR := PolynomialRing(K); x := PR.1;

    U := x^(2*ell);

    C, v := Coefficients(T);
    V := (x^v * Parent(x)!C) mod U;

    vprintf SEA, 2 : "\t PartialGCD ";
    Tm := Cputime();
    PI := PartialGCD(U, V, (2*ell), (2*ell +1) div 2);
    vprintf SEA, 2 : "... done in %o\n", Cputime(Tm);

    A := V*PI[2, 2] mod x^(2*ell);
    B := PI[2, 2];
    return A, B;

end function;


// Reduce mod. p 
// -------------
function PadicToFF(T)

    L := Parent(T); K := BaseRing(L);

    FF, redmap := ResidueClassField(K);
    Px := PolynomialRing(FF); x := Px.1;
    
    Lp := ChangeRing(L, FF);

    Tp := Lp!T;

return Tp;

end function;


// Computing the first N Newton sums s_i of P and (1/i)*ds_i/dt
// ------------------------------------------------------------
function NewtonSumsAndDerivatives(P , g, N)

    L:=CoefficientRing(P);
    K:=CoefficientRing(L); p := Prime(K);
    Kp:=ChangePrecision(K, Precision(K)+ Floor(Log(p,g)));
    Lp<t> := LaurentSeriesRing(Kp); S<x> := PolynomialRing(Lp); Pp := S!P;

    Ps := Reverse(Pp);
    Lpp:=CoefficientRing(Pp); _<z> := LaurentSeriesRing(Lpp,g+1);

    Ps := Evaluate(Ps,z); Psinv := MyInv(Ps,g-1);
    f := - Derivative(Ps) * Psinv;

    coeff := Coefficients(f); coeffs:=[]; dercoeffs := []; 
    for i:=1 to #coeff do   
        Append(~coeffs , L!coeff[i]);
        if i mod p eq 0 then   
        Append(~dercoeffs, ChangePrecision(L![j div i : j in Coefficients(Derivative(coeff[i]))] , N-1)); 
        else  Append(~dercoeffs, ChangePrecision( L![j div i : j in Coefficients(Derivative(L!coeff[i]))] , N-1));  end if;

    end for;

    return coeffs , dercoeffs;

end function;



// 1/Sqrt(T) mod. U computed with a Newton iteration
// -------------------------------------------------
function MySqrtInvMod(T,N,T0,U)

    L:=Parent(U); t := L.1;
    T:= L![ChangePrecision(coeffs,N) : coeffs in Coefficients(T)];
    if N le 1 then 
        return L!T0;
    end if;

    M := Ceiling( (N)/2);
    
    u := MySqrtInvMod(T,M,T0,U);
    u := L![ChangePrecision(i , N) : i in Coefficients(u)];
    return  (u/2)*((-T*(u^2 mod U) +3) mod U) mod U;

end function;




// 1/T mod. U computed with a Newton iteration
// -------------------------------------------
function MyInvMod(T,N,T0,U)

    L:=Parent(U); t := L.1;
    T:= L![ChangePrecision(coeffs,N+1) : coeffs in Coefficients(T)];
    if N le 1 then 
        return L!T0;
    end if;

    M := N div 2;
    
    u := MyInvMod(T,M,T0,U);
    u := L![ChangePrecision(i , N+1) : i in Coefficients(u)];
    H:= (2 - u*T) mod U;
    H:=H*u mod U; 
    return H;

end function;




// Compute a Hankel matrix-vector product 
// --------------------------------------
function HankelProduct(v, b)   //v = [v0, v1 , ... , v2n-2], b =[b0,b1,...,bn-1]

    R<x> := PolynomialRing(Parent(v[1]));
    n:= #b;

    f := R!v;
    h := R!Reverse(b);

    w := Coefficients(f*h mod x^(2*n-1));
    w := w cat [0 : i in [1..2*n -1 -#w]];

    return w[n..2*n-1];

end function;




// Arithmetic on Jacobians of hyperelliptic curves
// -----------------------------------------------



function CantorReduce(D, J)

    H := Curve(J);
    g := Genus(H);
    f, _ := HyperellipticPolynomials(H);
    a, b, _ := Explode(Eltseq(D));

    a2 := (f - b^2) div a;
    a2 /:= LeadingCoefficient(a2);
    b2 := -b mod a2;

    if Degree(a2) eq Degree(a) then
        /* Ambiguous form of degree g+1. */
        return [a2, b2];
    end if;

    if Degree(a2) gt g then
        return CantorReduce([a2, b2], J);
    end if;

    return [a2, b2];

end function;



function CantorCompose(D1, D2, J)

    H := Curve(J);
    genus := Genus(H);
    f, _ := HyperellipticPolynomials(H);
    a1, b1, _ := Explode(Eltseq(D1));
    a2, b2, _ := Explode(Eltseq(D2));

    if a1 eq a2 and b1 eq b2 then
        // Duplication law
        d, h1, h3 := ExtendedGreatestCommonDivisor(a1, 2*b1);

        a := (a1 div d)^2;
        b := (b1 + h3*((f - b1^2) div d)) mod (a);
    else
        d0, _, h2 := ExtendedGreatestCommonDivisor(a1, a2);
        if d0 eq 1 then
            a := a1*a2;
            b := (b2 + h2*a2*(b1-b2)) mod (a);
        else
            d, l, h3 := ExtendedGreatestCommonDivisor(d0, b1+b2);
            a := (a1*a2) div (d^2);
            b := ((b2 + l*h2*(b1-b2)*(a2 div d)) + h3*((f - b2^2) div d)) mod (a);
        end if;
    end if;

    a /:= LeadingCoefficient(a);
    return [a, b];

end function;


function CantorAdd(D1, D2)
    J := Parent(D1);
    D := CantorCompose(D1, D2, J);
    return J!CantorReduce(D, J);
end function;



function CantorExp(D, n)

    J := Parent(D);
    x := D;
    y := IsOdd(n) select D else J!0;
    np := n div 2;
    while ( np gt 0 ) do
        x := CantorAdd(x, x);
        if (IsOdd(np)) then
            y := CantorAdd(x, y);
        end if;
        np := np div 2;
    end while;

    return y;
end function;


// Application to the multiplication by ell
// Initial condition is needed
// -----------------------------------------

SetVerbose("SEA", 0);

/* g: genus, p: characteristic */
g := 4; p := 5;
ell := 20; PadicTimings := [];


repeat

    repeat
        ell := ell +1;
    until ell mod p ne 0;

    PrP :=  10+ Floor(Log(p, 3*g*ell^2));
    
    "---";
    "- p =", p, ", ell =", ell, ", genus =", g, ", PrP = ", PrP;
    "-----------------------------------------";

    FF := GF(p); K := pAdicField(p ,PrP);
    _<x> := PolynomialRing(FF); S<z> := PolynomialRing(K);
    t:=0;

    while t eq 0 do 
    try 
        repeat
            repeat
                repeat
                    hC1 := RandomIrreduciblePolynomial(FF,2*g+1) ;
                    H := HyperellipticCurve(hC1); J := Jacobian(H);
                until #H ne 1;
                repeat
                    PtF:=Random(H);
                until PtF[3] ne 0;
                PF := J![x - PtF[1] , PtF[2]]; QF := ell *PF;           
            until Degree(QF[1]) eq g and Discriminant(QF[1]) ne 0  and Degree(QF[2]) eq g-1; //QF must be generic 

            f := QF[1]; 
            hC:= S!hC1;
            H := HyperellipticCurve(hC); J := Jacobian(H);
            Pt:= Points(H , PtF[1])[1];
            if Valuation(K!PtF[2] - Pt[2]) lt 1 then 
                Pt:= Points(H , PtF[1])[2];
            end if;
            P := J![z - Pt[1] , Pt[2]]; Q := CantorExp(P, ell);

        until Degree(Q[1]) eq g and Valuation(Discriminant(Q[1])) eq 0  and Precision(Coefficient(Q[1], 0)) ge 1+Floor(Log(p, 3*g*ell^2));
        t:=1;
    catch e 
        t:=0;
    end try;
    end while;
 
 

    PrP :=  1 + Floor(Log(p, 2*g*ell^2));
    K := pAdicField(p ,PrP); 
    L<t> := LaurentSeriesRing(K, 2*g*ell^2); S<z> := PolynomialRing(L);

    _U0 := S!Q[1]; _V0:= S!Q[2]; hC := S!hC;
    _,_,_W0:=XGCD(Q[1], Q[2]); _W0:=S!_W0; 

    
    _u0 := K!Evaluate(-P[1] ,0) ; _v0 := K!Evaluate( P[2], 0);
    _Mij := DiagonalMatrix( K , g , [ell : i in [1..g]]);


    U,vinv,timings:= EquadifSolver(ell^2  , hC , hC , _Mij, _U0, _V0, _W0, _u0 , _v0,PrP);
    tm:= Cputime();
    
     // Computing the coefficients of the first Mumford coordinate: U
     // -------------------------------------------------------------
     
    ListOfCoeffs := Coefficients(U);
    ListOfCoeffs:= [ PadicToFF(i) : i in ListOfCoeffs];

    Num, Denom:= FastBerlekampMassey( g*ell^2, ListOfCoeffs[1]); 

    L<t> := LaurentSeriesRing(FF , g*ell^2+1);
    Denom_U := L!Denom;
    Nums_U :=  [L!Num] cat [(Denom_U*L!ListOfCoeffs[k]) : k in [2..#ListOfCoeffs]];
    Nums_U:= [ Parent(Num)!Coefficients(i) : i in Nums_U]; // The numerators and the denominator of the coefficients of U are calculated up to a translation

    
    // Computing the coefficients of the second Mumford coordinate: V 
    // --------------------------------------------------------------

    N:=3*g*ell^2+ 2*g+2;
    L<t> := LaurentSeriesRing(FF , N);
    Denom_inv := MyInv(L!Denom_U, N);
    ListOfCoeffs_V:=[ChangePrecision(L!i, N)*Denom_inv : i in Nums_U];

    P<x> := PolynomialRing(L);
    U_V := P!ListOfCoeffs_V;

    hC := P![ChangePrecision(i,N ) : i in Coefficients(hC)];
    _W0:= P![ChangePrecision(i, N ) : i in Coefficients(_W0)];
    v_sq:= Evaluate(hC , t + PtF[1]);

    V:= MySqrtInvMod(v_sq* hC, N, (1/PtF[2])*_W0, U_V ) ;
    V := hC * v_sq * V mod U_V;
    ListOfCoeffs_V:= Coefficients(V);

    
    L<t> := LaurentSeriesRing(FF , Floor(N/2+1));

    Num_V, Denom_V:= FastBerlekampMassey( Floor(N/2), ListOfCoeffs_V[1] );

    Denom_V := L!Denom_V;
    Nums_V :=  [L!Num_V] cat [(Denom_V*L!ListOfCoeffs_V[k]) : k in [2..#ListOfCoeffs_V]];
    Nums_V:= [ Parent(Num_V)!Coefficients(i) : i in Nums_V]; // The numerators and the denominator of the coefficients of V are calculated up to a translation

    tm := Cputime(tm);

    Append(~PadicTimings, <ell^2,timings cat [tm]>);

until ell gt 100;



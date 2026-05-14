/////////////////////////////////////////////////////
// Stefano Marseglia, stefano.marseglia89@gmail.com
// https://stmar89.github.io/index.html
// 
// Distributed under the terms of the GNU Lesser General Public License (L-GPL)
//      http://www.gnu.org/licenses/
// 
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation; either version 3.0 of the License, or
// (at your option) any later version.
// 
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA
// 
// Copyright 2024, S. Marseglia
/////////////////////////////////////////////////////

declare verbose Algorithm_2,3;
declare verbose Algorithm_3,3;

////////////////////////////////////////////////////////////////////////////////////
//////////////////////// IsomorphismClassesDieudonneModules ////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic IsomorphismClassesDieudonneModulesCommEndAlg(isog::IsogenyClassFq : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AlgEtQIdl]
{Given an isogeny class of abelian varieties over Fq with commutative endomorphism algebra returns representatives of the isomorphism classes of the local-local parts of the Dieudonné modules of the varieties. These representatives are given as fractional WR-ideals, where WR is defined as in DiedudonneAlgebraCommEndAlg, which are stable under the action of semilinar operators F and V=pF^-1, where F has the Frobenius property and is of W-type. See the paper for the definitions. The action of F and V is computed on a quotient, whose size is determined by a precision parameter m. This m is calculated automatically to guarantee that the output of this function is correct. One can increase this parameter by setting the VarArg IncreaseMinimumPrecisionForSemilinearFVBy to a strinctly positive value. The operators can be recovered using SemilinearOperators.}
    require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
    vprintf DieudonneModules,1 : "Computing DiedudonneAlgebraCommEndAlg...";
    R:=ZFVOrder(isog);
    E:=Algebra(R);
    pi:=PrimitiveElement(E);
    //h:=DefiningPolynomial(E);
    g:=Dimension(isog);
    q:=FiniteField(isog);
    t,p,a:=IsPrimePower(q);
    assert t;
    L,_,_,_,A,pi_A,_,Delta_map,WR,sigma_OA_mod_I,alpha_at_precision:=DieudonneAlgebraCommEndAlg(isog);
    OA:=MaximalOrder(A);
    vprintf DieudonneModules,1 : "done\n";
    vprintf DieudonneModules,1 : "sing primes of R = %o\n",[Index(R,PP):PP in SingularPrimes(R)];
    vprintf DieudonneModules,1 : "[OE:R] = %o\ndim_Q(L)=%o\ndim_Q(A)=%o\n",Index(MaximalOrder(E),R),Degree(L),Dimension(A);
    _,plE_sl_in01,_:=PlacesOfQFAbove_p(isog);
    _,pl_01_R,_:=PrimesOfZFVAbove_p(isog);
    pl_01_R:=Setseq({ OneIdeal(R) meet (R!!P) : P in plE_sl_in01 });
    if #plE_sl_in01 ne 0 then
        assert #pl_01_R eq 1;
    end if;

    vprintf DieudonneModules,2 : "places of E w/ slope in (0,1) = %o\n",Sort([ Slope(P) : P in plE_sl_in01]);
    // Early exit if no places 
    if #plE_sl_in01 eq 0 then
        dm:=OneIdeal(WR);
        dm`DeltaEndomorphismRing:=R;
        return [dm],plE_sl_in01; 
    end if;

    //////////////////
    // Units quotient
    //////////////////
    // Let S be an order in A', containing R'. We want to compute OA'^*/S^*\Delta'(O_E'^*)

    units_quotient_01:=function(S)
    // Given an order S in A, representing an order S' in A' returns U=OA'^*/S'^* and a map u:U->OA,
    // together with an ideal I of OA such that OA'/S' = (OA/I)/(S/I).
        _,primes_01_S,_:=PrimesOfSAbove_p(isog,S);
        ff:=Conductor(S);
        primes_01_S_above_ff:=[ P : P in primes_01_S | ff subset P];
        assert2 forall{P : P in primes_01_S_above_ff | p in P};
        if #primes_01_S_above_ff eq 0 then
            U:=FreeAbelianGroup(0);
            // with test
            trivial_preimage:=function(y)
                assert2 forall{ P : P in primes_01_S_above_ff | not y in P };
                return Zero(U);
            end function;
            u:=map<U->Algebra(S) | x:->One(S), y:->trivial_preimage(y)>;
            // without test
            //u:=map<U->Algebra(S) | x:->One(S), y:->Zero(U)>;
            return U,u,OneIdeal(OA);
        end if;
        indff:=Index(S,ff);
        assert2 forall{P : P in primes_01_S_above_ff | indff mod Index(S,P) eq 0 };
        ks:=[ Valuation(indff,p) div Valuation(Index(S,P),p) : P in primes_01_S_above_ff ];
        prod:=&*([ primes_01_S_above_ff[i]^ks[i] : i in [1..#primes_01_S_above_ff]]);
        ff_prod:=ff+prod;
        assert not 1 in ff_prod;
        assert2 OneIdeal(S) meet S!!(OA!!ff_prod) eq ff_prod;        
      
        I:=OA!!(ff_prod);
        R,r:=ResidueRingUnits(I);
        gens:=ResidueRingUnitsSubgroupGenerators(ff_prod);
        U,u0:=quo<R | [ g@@r : g in gens]>;
        u:=map<U->Algebra(S) |  x:-> r(x@@u0), y:->u0(y@@r) >;
        return U,u,I;
    end function;

    fixed_pts_sigma:=function(S)
    // Given an order S in A, representing an order S' in A', 
    // which is stable by the action of sigma (eg. WR),
    // returns U,u,F,m where
    // - U=OA'^*/S'^*,
    // - u is a map u:U->OA giving representatives 
    // - F is the subgroup of elements of U=OA'^*/S'^* fixed by sigma
        U,u,I:=units_quotient_01(S); //u:U->A
        Q,q:=ResidueRing(OA,I);
        sigma:=sigma_OA_mod_I(Q,q,A); // sigma: Q->Q
        id_sigma:=hom< U->U | [ U.i-(U.i@u@q@sigma@@q@@u) : i in [1..Ngens(U)]]>; //additive notation
        F:=Kernel(id_sigma);
        return U,u,F;
    end function;

    // only for WR: F = Delta(OE')^*W'R^*/W'R^* inside OA'^*/W'R^*
    vprintf Algorithm_2,1 : "Computing fixed_pts_sigma...";
    U,u,F:=fixed_pts_sigma(WR);
    vprintf Algorithm_2,1 : "done\n";
    units_quotient_fixed_sigma_WR_gens:=[u(F.i) : i in [1..Ngens(F)]];
    vprintf Algorithm_2,2 : "Generators of Delta(OE^*)W'_R^* in U : %o\n", PrintSeqAlgEtQElt( units_quotient_fixed_sigma_WR_gens);
    delete U,u,F;

    units_quotient_fixed_sigma:=function(S)
    // Given an order S in A, representing an order S' in A', returns Q,q where
    // Q = OA'^*/S'^*Delta(OE'^*) 
    // q is a map Q->OA giving representatives
        if not assigned S`units_quotient_fixed_sigma then
            U,u:=units_quotient_01(S); //u:U=OA'^*/S'^* -> A
            fixed_pts_gens:=[ g@@u : g in units_quotient_fixed_sigma_WR_gens];
            Q,q0:=quo<U|fixed_pts_gens>; //q0: U->U/F=Q
            q:=map<Q->Algebra(S) |  x:->u(x@@q0), y:->q0(y@@u) >;
            gammas:=[q(x) : x in Q];
            S`units_quotient_fixed_sigma:=<Q,q,gammas>;
        end if;
        return Explode(S`units_quotient_fixed_sigma);
    end function;

    // ####################
    // F-V stable classes with maximal end,
    // using the exponents description from
    // Waterhouse's paper
    // ####################
    
    exponents_from_Waterhouse:=function(P)
        f_nu:=InertiaDegree(P);
        g_nu:=GCD(a,f_nu); //q=p^a
        e_nu:=RamificationIndex(P);
        exps:=[];
        cp:=CartesianProduct([ [0..e_nu] : i in [1..g_nu]]);
        for tup0 in cp do
            tup:=[ tup0[i] : i in [1..g_nu] ];
            if &+tup eq Integers()!(g_nu*Valuation(pi,P)/a) then
                exp:=[ i eq 1 select 0 else Self(i-1) + tup[i-1] : i in [1..g_nu]];
                Append(~exps,exp);
            end if;
        end for;
        return exps;
    end function;
    
    // ####################
    // Algorithm 2
    // ####################

    vprintf Algorithm_2,1 : "\n\n################\nAlgorithm 2\n################\n";

    exps_nus:=[];
    pp_A_nus:=[];
    for P in plE_sl_in01 do
        Append(~exps_nus,exponents_from_Waterhouse(P));
        Append(~pp_A_nus,PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,P)); // here the places of A need 
                                                                                       // to be sorted by sigma
    end for;
    exps_nus_cc:=CartesianProduct(exps_nus);
    exps_01:=[];
    for cc in exps_nus_cc do
        Append(~exps_01,&cat[ c : c in cc ]); 
    end for;
    vprintf Algorithm_2,2 : "F-V stable O_A' ideals = %o \n",exps_01;
    pp_A_01:=&cat(pp_A_nus);
    nice_unifs_01:=Uniformizers(pp_A_01);
    vprintf Algorithm_2,2 : "nice_unifs_01 = %o\n", PrintSeqAlgEtQElt(nice_unifs_01);

    vprintf Algorithm_2,1 : "Defining WR_01...";
    // We compute the W'_R-isomorphim classes of W'_R-ideals.
    k:=Valuation(Index(OA,WR),p);
    WR_01:=Order( ZBasis(WR) cat ZBasis(OA!!&*[ P^(k*RamificationIndex(P)) : P in pp_A_01 ]));
    // WR_01 order is locally equal to WR' at every place of slope 01 and to OA everywhere else
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "[OA:WR] = %o\n",Index(OA,WR);
    vprintf Algorithm_2,1 : "[OA:WR_01] = %o\n",Index(OA,WR_01);
    vprintf Algorithm_2,1 : "Computing WKICM(WR_01)...";
    // DUALITY could speed up the next computation. 
    // It would have to run for all pp_A_01 of slope <1/2 and =1/2, and deduce the output for >1/2 from the first.
    wk_01:=[ WR!!I : I in WKICM(WR_01)];
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "number of W_R'-isomorphism classes = %o\n",#wk_01;

    vprintf Algorithm_2,1 : "Computing WR_01_idls_with_ext_i_to_OA_F_V_stable...";
    WR_01_idls_with_ext_i_to_OA_F_V_stable:=[];
    for I in wk_01 do
        S:=MultiplicatorRing(I);
        J:=OA!!I;
        valsJ:=[ Valuation(J,P) : P in pp_A_01 ];
        deltas:=[];
        for exps in exps_01 do
            assert #exps eq #pp_A_01; 
            Append(~deltas,&*[nice_unifs_01[i]^(valsJ[i]-exps[i]) : i in [1..#pp_A_01]]);
        end for;
        QS,qS,gammas:=units_quotient_fixed_sigma(S); // this is now cached in an attributed
        vprintf Algorithm_2,2 : "valsJ = %o\n", valsJ;
        vprintf Algorithm_2,2 : "deltas = %o\n", PrintSeqAlgEtQElt(deltas);
        vprintf Algorithm_2,2 : "gammas = %o\n", PrintSeqAlgEtQElt(gammas);
        assert2 forall{ d : d in deltas | not IsZeroDivisor(d) };
        assert2 forall{ g : g in gammas | not IsZeroDivisor(g) };
        II:=[ ((d^-1)*g)*I : d in deltas, g in gammas ];
        vprintf Algorithm_2,2 : "#II = %o\n",#II;
        vprintf Algorithm_2,3 : "valuations of the of extensions O_A' of the ideals in II = %o\n",[ [ Valuation(OA!!ii,P) : P in pp_A_01 ] : ii in II ]; // computing this info might take a lot of time.
        WR_01_idls_with_ext_i_to_OA_F_V_stable cat:=II;
    end for;
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "number of Delta'-isomorphism classes with FV-stable extension to O_A' = %o\n",#WR_01_idls_with_ext_i_to_OA_F_V_stable;
   
    // ####################
    // Algorithm 3
    // ####################
    
    vprintf Algorithm_3,1 : "\n\n################\nAlgorithm 3\n################\n";
    exps:=exps_01[1];
    //"WARNING: changing J for test purposes";exps:=exps_01[2];
    JOA:=&*[ pp_A_01[i]^exps[i] : i in [1..#exps] ]; 
    assert MultiplicatorRing(J) eq OA;
    J:=WR !! JOA;
    ZBasisLLL(J);
    vprintf Algorithm_3,2 : "vals of the F-V stable OA-ideal J chosen for the container = %o\n",
                            [ Valuation(OA!!J,P) : P in pp_A_01 ];

    // We scale the ideals I by elements of Delta(E) so that they are in J
    vprintf Algorithm_3,1 : "Delta-scaling the ideals into J...";

    nus:=PlacesAboveRationalPrime(E,p);
    unifs:=Uniformizers(nus);

    pExponent:=function(A,B)
    // Given B c A, returns the vp(Exponent(Quotient(A,B))) without computing Quotient(A,B),
    // but only a quotient isomorphic to its p-part.
        vp_ind:=Valuation(Index(A,B),p);
        // now I only compute the quotient of the p-part.
        vp_exp:=Valuation(Exponent(Quotient(A,B+p^vp_ind*A)),p);
        return vp_exp;
    end function;

    Delta_scale_inside:=function(I,J)
    // given an OA-ideal WR!!J and a WR-ideal I, it finds an element x in E^* such that Delta(x)I c J.
    // This element is chosen so that [J:xI] will have a small p-adic valuation.
        vprintf Delta_scaling,1 : "Computing: colon ideal...";
        cc:=OA!!ColonIdeal(J,I);
        exps:=[];
        vprintf Delta_scaling,1 : "M_nu's";
        for nu in nus do
            M_nu:=Max([Valuation(cc,P) : P in PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)]);
            vprintf Delta_scaling,1 : ".";
            Append(~exps,M_nu);
        end for;
        x:=&*[unifs[i]^exps[i]:i in [1..#nus]];
        vprintf Delta_scaling,1 : "xI...";
        xI:=Delta_map(x)*I;
        vprintf Delta_scaling,1 : "y...";
        // Computing Quotient can give Magma Internal Error (I guess because of coefficients explosion)
        // We don't really care if y is big, since it will be coprime to p. So we take the index.
        // y:=Exponent(Quotient(xI,xI meet J));
        y:=Index(xI+J,J);
        assert (y mod p) ne 0; // y coprime p
        yxI:=y*xI;
        assert yxI subset J;
        vprintf Delta_scaling,1 : "ZBasisLLL...";
        ZBasisLLL(yxI);
        vprintf Delta_scaling,1 : "done";
        return yxI;
    end function;

    // We need to replace each ideal I in WR_01_idls_with_ext_i_to_OA_F_V_stable with a Delta(E)-equivalent 
    // ideal s*I such that s*I < J so that the maximal value m0 of vp(exp(J/s*I)) is as small as possible.
    // The optimal s can be obtained by the function Delta_scale_inside above, which requires to compute the 
    // colon ideal (J:I) and its valuations at the places of A above p. This can be expensive.
    // So we first try to take s=p^ss where ss=pExponent(I+J,J) which is faster.
    // If this scaling does not increase m0, ther are good. Otherwise we use Delta_scale_inside.
    m0:=0; 
    for i in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        I:=WR_01_idls_with_ext_i_to_OA_F_V_stable[i];
        ZBasisLLL(I);
        D_scale:=true;
        if I subset J then
            if pExponent(J,I) le m0 then
                D_scale:=false;
            end if;
        else
            vprintf Delta_scaling,1 : "\nAttempting to pExp-scaling the %o-th ideal into J...",i;
            ss:=pExponent(I+J,J);
            x:=p^ss;
            xI:=x*I;
            y:=Index(xI+J,J);
            assert (y mod p) ne 0; // y coprime p
            yxI:=y*xI;
            assert yxI subset J;
            if pExponent(J,yxI) le m0 then
                vprintf Delta_scaling,1 : "\nsuccess...",i;
                D_scale:=false;
                vprintf Delta_scaling,1 : "ZBasisLLL...";
                ZBasisLLL(yxI);
                vprintf Delta_scaling,1 : "done";
                WR_01_idls_with_ext_i_to_OA_F_V_stable[i]:=yxI;
            end if;
        end if;
        if D_scale then
            vprintf Delta_scaling,1 : "\nDelta-scaling the %o-th ideal into J...",i;
            I:=Delta_scale_inside(I,J);
            vpN:=pExponent(J,I);
            m0:=Max(m0,vpN);
            WR_01_idls_with_ext_i_to_OA_F_V_stable[i]:=I;
        end if;
    end for;
    assert2 forall{I:I in WR_01_idls_with_ext_i_to_OA_F_V_stable|I subset J};
    // The next assert tests that p^m0*J < I locally at p. Since I < J, this is equivalent to m0 ge val_p(exp(J/I))
    assert2 forall{I:I in WR_01_idls_with_ext_i_to_OA_F_V_stable|Valuation(Index((p^m0)*J+I,I),p) eq 0};
    vprintf Algorithm_3,1 : "done\n";

    if IncreaseMinimumPrecisionForSemilinearFVBy gt 0 then
        m0_old:=m0;
        m0+:=IncreaseMinimumPrecisionForSemilinearFVBy;
        vprintf Algorithm_3:"Incresing m0 from to %o, using IncreaseMinimumPrecisionForSemilinearFVBy\n",m0_old,m0;
    end if;
    //m1:=m0+10; "WARNING: m0 is forced now from ",m0,"to",m1; m0:=m1; //for debugging

    vprintf Algorithm_3 : "m0 = %o\n",m0;
    vprintf Algorithm_3,2 : "v_nu(pi) for all nu's = %o\n",[ Valuation( pi, P ) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "e_nu for all nu's = %o\n",[ RamificationIndex(P) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "f_nu for all nu's = %o\n",[ InertiaDegree(P) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "g_nu for all nu's = %o\n",[ GCD(a,InertiaDegree(P)) : P in plE_sl_in01 ];

    vprintf Algorithm_3,1 : "Computing M...";
    _,primes_01_WR,_:=PrimesOfSAbove_p(isog,WR);
    // Need M such that P^M*J c p^(m0+1)J, locally at P, for each P in primes_01_WR.
    // By looking at the composition series, one deduces that any 
    // M \geq Truncate(Log(Index(WR,P),Index(J,p^(m0+1)J)) will do.
    size:=(p^(m0+1))^AbsoluteDimension(A); // size = #J/p^(m0+1)J = (p^(m0+1))^dim_Q(A)
    M:=Max( [ Truncate(Log(Index(WR,P),size)) : P in primes_01_WR] );
    //M1:=M+10; "WARNING: M is forced now from ",M,"to",M1; M:=M1; //for debugging
    vprintf Algorithm_3,1 : "done. Got M=%o\n",M;
    PP01:=(&*(primes_01_WR))^M;

    vprintf Algorithm_3,1 : "Computing Qm0_1...";
    Qm0_1,qm0_1:=Quotient(J,p^(m0+1)*J+PP01*J);
    vprintf Algorithm_3,1 : "done\n";
    vprintf Algorithm_3,1 : "Computing Qm0...";
    den_ideal:=p^(m0)*J+PP01*J;
    Qm0,qm0:=Quotient(J,den_ideal);
    vprintf Algorithm_3,1 : "done\n";
    // these quotients are isomorphic to the (0,1)-part of J/p^(m0+1)J and J/p^m0J

    pr:=hom< Qm0_1->Qm0 | [ qm0(Qm0_1.i@@qm0_1) : i in [1..Ngens(Qm0_1)]] >;
    assert IsSurjective(pr);
    assert2 forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
    
    // ###################################
    // Semilinear Frobenius on Qm0, Qm0_1
    // ###################################
    assert JOA subset OA;
    m1:=m0+1+Valuation(Index(OA,JOA),p);
    //m2:=m1+10; "WARNING: m1 is forced now from ",m1,"to",m2; m1:=m2; //for debugging
    vprintf Algorithm_3,1 : "Computing sigma on OA/p^m1*OA for m1 = %o...",m1;
    // We have the following inclusions, locally at p: p^m1*OA c p^(m0+1)*J c I c J c OA.
    // This means the approximation of sigma on OA/p^m1*OA will give a well defined sigma on Q=J/I
    QOA,qOA:=ResidueRing(OA,p^m1*OA);
    sigma_QOA,powers_zz_diagonally_inOA_via_zbOE:=sigma_OA_mod_I(QOA,qOA,A);
    vprintf Algorithm_3,1 : "done\n";

    vprintf Algorithm_3,1 : "Computing alpha at precision %o...",m1;
    alpha:=alpha_at_precision(m1);
    vprintf Algorithm_3,1 : "done\n";

    vprintf Algorithm_3,1 : "Action of the semilinear Frobenius on Qm0,Qm0_1...\n";
    FQm0:=hom<Qm0->Qm0 | [ qm0(alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0)]]>;
    FQm0_1:=hom<Qm0_1->Qm0_1 | [ qm0_1(alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0_1)]]>;
    assert2 forall{ x : x in Generators(Qm0_1) | FQm0(pr(x)) eq pr(FQm0_1(x))};
    // in the next assert2's, we check that FQm0^a and FQm0_1^a are equal to multiplication by pi_A
    assert2 forall{ x : x in Generators(Qm0) | (FQm0^a)(x) eq qm0(pi_A*(x@@qm0))};
    assert2 forall{ x : x in Generators(Qm0_1) | (FQm0_1^a)(x) eq qm0_1(pi_A*(x@@qm0_1))};

    vprintf Algorithm_3,2 : "\tFQ's are computed\n";

    mp:=hom<Qm0_1->Qm0_1 | [ p*(Qm0_1.j) : j in [1..Ngens(Qm0_1)] ]>;
    assert2 mp eq hom<Qm0_1->Qm0_1 | [ qm0_1(p*(Qm0_1.j)@@qm0_1) : j in [1..Ngens(Qm0_1)] ]>;
    assert Image(mp) subset Image(FQm0_1);
    vprintf Algorithm_3,2 : "\tmp is computed\n";

    z_gamma_s:=[];
    for i in [1..Ngens(Qm0)] do
        vprintf Algorithm_3,2 : "\tComputing z_gamma for the %oth generator of Qm0...",i;
        gamma:=Qm0.i;
        x_gamma:=gamma@@pr;
        z_gamma:=(mp(x_gamma))@@FQm0_1;
        vprintf Algorithm_3,2 : "done\n";
        Append(~z_gamma_s,z_gamma);
    end for;
    VQm0:=hom<Qm0->Qm0 | [ pr(z_gamma_s[i]) : i in [1..Ngens(Qm0)] ] >;
    assert2 forall{ g : g in Generators(Qm0) | FQm0(VQm0(g)) eq p*g };
    assert2 forall{ g : g in Generators(Qm0) | VQm0(FQm0(g)) eq p*g };
    vprintf Algorithm_3,2 : "\tVQ is computed\n";

    // We check semilinearity for F, V: F*x = sigma(x)*F and x*V=V*sigma(x)  forall x in L?
    // It suffices to check if for powers of zz in OA.
    if GetAssertions() ge 2 then
        vprintf Algorithm_3,2 : "\tTesting semilinearity of F and V...";
        for z in powers_zz_diagonally_inOA_via_zbOE do
            sigma_z:=z@qOA@sigma_QOA@@qOA;
            z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
            sigma_z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(sigma_z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
            assert2 forall{i:i in [1..Ngens(Qm0)]| FQm0(z_action_Qm0(Qm0.i)) eq sigma_z_action_Qm0(FQm0(Qm0.i))};
            assert2 forall{i:i in [1..Ngens(Qm0)]| z_action_Qm0(VQm0(Qm0.i)) eq VQm0(sigma_z_action_Qm0(Qm0.i))};
        end for;
        vprintf Algorithm_3,2 : "all good.\n";
    end if;
    isog`SemilinearOperators:=<m0,J,den_ideal,Qm0,qm0,FQm0,VQm0>;

    is_F_V_stable:=function(I)
        I_Qm0:=sub<Qm0 | [qm0(z) : z in ZBasis(I) ]>;
        IFV_Qm0:=I_Qm0 + 
                        sub<Qm0 | [FQm0(z) : z in Generators(I_Qm0)] > +
                        sub<Qm0 | [VQm0(z) : z in Generators(I_Qm0)] >;
        vprintf Algorithm_3,3 : "[I_Q+F_Q(I_Q)+V_Q(I_Q):I_Q] = %o\n",Index(IFV_Qm0,sub<IFV_Qm0|I_Qm0>);
        return I_Qm0 eq IFV_Qm0;
    end function;

    Delta_isom_classes_WR_F_V:=[ ];
    vprintf Algorithm_3,2 : "Started checking for F-V stability:";
    delta_inverses_mult_rings:=[];
    for iI in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        vprintf Algorithm_3,3 : "\nfor the %oth ideal from WR_01_idls_with_ext_i_to_OA_F_V_stable:",iI;
        I:=WR!!WR_01_idls_with_ext_i_to_OA_F_V_stable[iI];
        if is_F_V_stable(I) then
            vprintf Algorithm_3,2 : "y";
            assert Order(I) eq WR;
            //TODO what are we doing here?
            mI:=MultiplicatorRing(I);
            t:=exists(S){pair[2]:pair in delta_inverses_mult_rings|pair[1] eq mI};
            if not t then
                Sid:=DeltaInverseIdeal(isog,WR!!OneIdeal(mI));
                S:=Order(ZBasis(Sid));
                assert Sid eq Order(Sid)!!OneIdeal(S);
                Append(~delta_inverses_mult_rings,<mI,S>);
            end if;
            I`DeltaEndomorphismRing:=S;
            Append(~Delta_isom_classes_WR_F_V,I);
        else
            vprintf Algorithm_3,2 : "n";
        end if;
    end for;
    vprintf Algorithm_3,2 : "\n";

    return Delta_isom_classes_WR_F_V;
end intrinsic;

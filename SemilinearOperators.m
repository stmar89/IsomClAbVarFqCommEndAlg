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

declare verbose AlphaWTypeAtPlace,3;
declare verbose AlphaDualAtNonConjStablePlace,3;

declare attributes IsogenyClassFq : AlphaWType,
                                    AlphaDualAtNonConjStablePlace,
                                    AlphaDualAtConjStablePlaceRhoId,
                                    AlphaDualAtConjStablePlaceRhoNotId,
                                    SemilinearOperatorsWType,
                                    SemilinearOperatorsDualComp,
                                    delta_inv;

integral_approx:=function(a,b,m,nus)
// Input: nus a list of places of the maximal order O of an étale algebra.
//        a,b in O, such that a/b is in O_nu, for every nu in nus.
//        m a positive integer.
// Output: an element y of O such that val_nu(y-a/b)>=m, for every nu in nus. 
    x:=a/b;
    O:=Order(nus[1]);
    if x in O then
        return x;
    end if;
    assert forall{nu:nu in nus|Valuation(a,nu) ge Valuation(b,nu)};
    bO:=b*O;
    fac_bO:=AssociativeArray(:Default:=0);
    for g in Factorization(bO) do
        fac_bO[g[1]]:=g[2];
    end for;
    
    ys:=[];
    for nu in nus do
        Enu,mnu:=Completion(nu: MinPrecision:=m+fac_bO[nu]);
        Append(~ys,(a@mnu/b@mnu)@@mnu);
    end for;
    assert forall{y:y in ys|y in O};
    if #nus eq 1 then
        y:=ys[1];
    else
        y:=CRT([nu^(m+fac_bO[nu]):nu in nus],ys);
    end if;
// OLD
//    fac_bO:=Factorization(bO);
//    supp_b:={ g[1]:g in fac_bO };
//    primes:=Setseq(supp_b join Seqset(nus));
//    cs:=[primes[i] in nus select One(O) else b:i in [1..#primes]];
//    c:=CRT([mu^m:mu in primes],cs);
//    y:=c*a/b; // y has positive valuation at every max ideal, hence it is integral
                // but I am not sure that it is congruent to a/b at nus ...
                // I should not merely put One(O), but actually compute b^-1 mod nu^(m+val_nu(b))
    assert y in O;
    assert2 forall{nu:nu in nus|Valuation(y,nu) eq Valuation(x,nu)};
    return y;
end function;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////Alpha of W-type/////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

intrinsic AlphaWTypeAtPlace(isog::IsogenyClassFq,nu::AlgEtQIdl,m::RngIntElt)->AlgEtQElt,AlgEtQIdl
{Given an isogeny class isog, a place nu of the DeligneAlgebra and a positive integer m, returns an integral element alpha of the DieudonneAlgebra A whose image in the quotient (OA/p^mOA)_nu is congruent to the nu-component alpha_nu of an element of of W-type, that is, such that alpha'_nu=(1,....,1,u) where N_(LE_nu/E_nu)(u)=pi_nu. Moreover, it returns also the product of maximal ideals of A above nu, raised to the power m*e where e is the common ramification index.}
    if not assigned isog`AlphaWType then
        isog`AlphaWType:=AssociativeArray();
    end if;
    nu_Hash:=myHash(nu);
    if not IsDefined(isog`AlphaWType,nu_Hash) then
        _,_,_,_,A,pi_A,_,Delta_map:=DieudonneAlgebraCommEndAlg(isog);
        p:=CharacteristicFiniteField(isog);
        a:=Ilog(p,FiniteField(isog));
        OA:=MaximalOrder(A);
        OA_mod_I,qOA_mod_I,sigma:=SigmaOnQuotientOfOA(isog,p^m*OA);
        PPs_nu:=PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu);
        f_nu:=InertiaDegree(nu);
        g_nu:=GCD(a,f_nu); //q=p^a
        assert #PPs_nu eq g_nu;

        Rs_nu:=[];
        rs_nu:=<>;
        Us_nu:=[];
        us_nu:=<>;
        PPs_nu_m:=[];
        for PP in PPs_nu do
            PP_m:=PP^(RamificationIndex(PP)*m);
            Append(~PPs_nu_m,PP_m);
            R,r:=ResidueRing(OA,PP_m);
            U,u:=ResidueRingUnits(OA,PP_m);
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
            Append(~Us_nu,U);
            Append(~us_nu,u);
        end for;
        PPs_nu_m_prod:=&*PPs_nu_m;

        Q,embs,projs:=DirectSum(Rs_nu);
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   y:->CRT(PPs_nu_m,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
        pi_Q:=pr(pi_A);
        assert forall{x:x in Generators(Q)|pr(x@@pr) eq x};

        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT(PPs_nu_m ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        sigma_U:=hom<U->U | [U.i@@U_pr@qOA_mod_I@sigma@@qOA_mod_I@U_pr : i in [1..Ngens(U)]]>; 
        assert forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};

        image_phi:=function(gamma)
            // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^m)^*
            // phi does the following two steps
            // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_{nu,i}^m
            // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
            beta:=&+[i lt g_nu select U_embs[i](Zero(Us_nu[i])) else U_embs[i](gamma):i in [1..g_nu]];
            // Action of the Frobenius on U
            img:=(&+[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
            assert sigma_U(img) eq img;
            return img;
        end function;
        phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
        
        t_nu:=UniformizersInQFAt_p(isog,[nu])[1]; // in E
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        val_nu:=Valuation(pi,nu); // in E
        w_nu:=integral_approx(pi,t_nu^val_nu,Dimension(E)*(m+a),[nu]); //FIXME the precision here is very 
                                                                     // likely high enough, but maybe not optimal
        wU:=U_pr(Delta_map(w_nu)); // in E->A->U
        gamma0:=wU@@phi; // in Us[g_nu], the last component of U
        gamma_A:=(&+[i lt g_nu select 
                                U_embs[i](One(A)@@us_nu[i]) else 
                                U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
        u0:=Delta_map(t_nu^(Integers()!(val_nu*g_nu/a)));
        beta_A:=(&+[i lt g_nu select 
                                embs[i](rs_nu[i](One(A))) else 
                                embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; 
        alpha_nu:=gamma_A*beta_A;
        // it is desirable that alpha_nu is not a zero divisor of A
        while IsZeroDivisor(alpha_nu) do
            alpha_nu+:=Random(PPs_nu_m_prod);
        end while;
        // Check that alpha_nu of W-type: 1 in all components but the last one, and with sigma-norm = pi_nu
        assert forall{i:i in [1..g_nu-1]|alpha_nu-1 in PPs_nu_m[i]};
        assert forall{i:i in [1..g_nu]|X-pi_A in PPs_nu_m[i]} where X:=&*[alpha_nu@qOA_mod_I@(sigma^i)@@qOA_mod_I:i in [0..a-1]];
        isog`AlphaWType[nu_Hash]:=<alpha_nu,PPs_nu_m_prod>;
    end if;
    return Explode(isog`AlphaWType[nu_Hash]);
end intrinsic;

intrinsic AlphaDualAtNonConjStablePlace(isog::IsogenyClassFq,nu::AlgEtQIdl,m::RngIntElt)->AlgEtQElt,AlgEtQElt
{Given an isogeny class isog, a non-conjugate stable place nu of the DeligneAlgebra and a positive integer m, returns // TODO 
// return alpha_nu,q_alpha_nu 
}
    if not assigned isog`AlphaDualAtNonConjStablePlace then
        isog`AlphaDualAtNonConjStablePlace:=AssociativeArray();
    end if;
    nu_Hash:=myHash(nu);
    if not IsDefined(isog`AlphaDualAtNonConjStablePlace,nu_Hash) then
        m2:=2*m; // later we need to take the pre-image on RR:=Rs_nu[g_nu] by the multiplication by the 
                 // the exact element u0. I think we need to double the precision to make sure that q_alpha_nu
                 // is computed at precision m.
        _,_,_,_,A,pi_A,_,Delta_map:=DieudonneAlgebraCommEndAlg(isog);
        p:=CharacteristicFiniteField(isog);
        q:=FiniteField(isog);
        a:=Ilog(p,FiniteField(isog));
        OA:=MaximalOrder(A);
        OA_mod_I,qOA_mod_I,sigma:=SigmaOnQuotientOfOA(isog,p^m2*OA);
        PPs_nu:=PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu);
        f_nu:=InertiaDegree(nu);
        g_nu:=GCD(a,f_nu); //q=p^a
        assert #PPs_nu eq g_nu;

        Rs_nu:=[];
        rs_nu:=<>;
        Us_nu:=[];
        us_nu:=<>;
        PPs_nu_m2:=[];
        for PP in PPs_nu do
            PP_m2:=PP^(RamificationIndex(PP)*m2);
            Append(~PPs_nu_m2,PP_m2);
            R,r:=ResidueRing(OA,PP_m2);
            U,u:=ResidueRingUnits(OA,PP_m2);
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
            Append(~Us_nu,U);
            Append(~us_nu,u);
        end for;
        PPs_nu_m2_prod:=&*PPs_nu_m2;
        Q,embs,projs:=DirectSum(Rs_nu);
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   y:->CRT(PPs_nu_m2,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
        pi_Q:=pr(pi_A);
        assert forall{x:x in Generators(Q)|pr(x@@pr) eq x};
        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT(PPs_nu_m2,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        sigma_U:=hom<U->U | [U.i@@U_pr@qOA_mod_I@sigma@@qOA_mod_I@U_pr : i in [1..Ngens(U)]]>; 
        assert forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};

        image_phi:=function(gamma)
            // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^m2)^*
            // phi does the following two steps
            // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_{nu,i}^m2
            // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
            beta:=&+[i lt g_nu select U_embs[i](Zero(Us_nu[i])) else U_embs[i](gamma):i in [1..g_nu]];
            // Action of the Frobenius on U
            img:=(&+[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
            assert sigma_U(img) eq img;
            return img;
        end function;
        phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
        
        t_nu:=UniformizersInQFAt_p(isog,[nu])[1]; // in E
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        val_nu:=Valuation(pi,nu); // in E
        w_nu:=integral_approx(pi,t_nu^val_nu,Dimension(E)*(m2+a),[nu]);
        wU:=U_pr(Delta_map(w_nu)); // in E->A->U

        gamma0:=wU@@phi; // in Us[g_nu], the last component of U
        gamma_A:=(&+[i lt g_nu select 
                                U_embs[i](One(A)@@us_nu[i]) else 
                                U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
        u0:=Delta_map(t_nu^(Integers()!(val_nu*g_nu/a)));
        beta_A:=(&+[i lt g_nu select 
                                embs[i](rs_nu[i](One(A))) else 
                                embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; 
        alpha_nu:=gamma_A*beta_A;
        // it is desirable that alpha_nu is not a zero divisor of A
        while IsZeroDivisor(alpha_nu) do
            alpha_nu+:=Random(PPs_nu_m2_prod);
        end while;
        // Check that alpha_nu of W-type: 1 in all components but the last one, and with sigma-norm = pi_nu
        assert forall{i:i in [1..g_nu-1]|alpha_nu-1 in PPs_nu_m2[i]};
        assert forall{i:i in [1..g_nu]|X-pi_A in PPs_nu_m2[i]} where X:=&*[alpha_nu@qOA_mod_I@(sigma^i)@@qOA_mod_I:i in [0..a-1]];

        // NEW 20260724 for q_alpha_nu, at precision m
        Rs_nu:=[];
        rs_nu:=<>;
        Us_nu:=[];
        us_nu:=<>;
        PPs_nu_m:=[];
        for PP in PPs_nu do
            PP_m:=PP^(RamificationIndex(PP)*m);
            Append(~PPs_nu_m,PP_m);
            R,r:=ResidueRing(OA,PP_m);
            U,u:=ResidueRingUnits(OA,PP_m);
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
            Append(~Us_nu,U);
            Append(~us_nu,u);
        end for;
        PPs_nu_m_prod:=&*PPs_nu_m;
        Q,embs,projs:=DirectSum(Rs_nu);
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   y:->CRT(PPs_nu_m,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
        pi_Q:=pr(pi_A);
        assert forall{x:x in Generators(Q)|pr(x@@pr) eq x};
        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT(PPs_nu_m,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        RR:=Rs_nu[g_nu];
        rr:=rs_nu[g_nu];
        mult_u0:=hom<RR->RR|[((RR.i@@rr)*u0)@rr : i in [1..Ngens(RR)]]>;
        q_u0:=(rr(A!q))@@mult_u0;
        q_gamma_A:=(-U_pr(gamma_A))@@U_pr; // in A
        q_beta_A:=(&+[i lt g_nu select 
                                embs[i](rs_nu[i](A!q)) else 
                                embs[i](q_u0) : i in [1..g_nu]])@@pr; // in A 
        q_alpha_nu:=q_gamma_A*q_beta_A; // in OA, at precision m
        assert alpha_nu*q_alpha_nu - q in PPs_nu_m_prod;
        isog`AlphaDualAtNonConjStablePlace[nu_Hash]:=<alpha_nu,q_alpha_nu>;
    end if;
    return Explode(isog`AlphaDualAtNonConjStablePlace[nu_Hash]);
end intrinsic;

intrinsic AlphaDualAtConjStablePlaceRhoId(isog::IsogenyClassFq,nu::AlgEtQIdl,m::RngIntElt)->AlgEtQElt,AlgEtQElt
{Given an isogeny class isog, a conjugate stable place nu of the DeligneAlgebra such that the action of the CM-involution on the places above nu is the ideantity and a positive integer m, returns // TODO 
// alpha_nu of W-type and delta_nu ...
}
// NEW 20260728
    if not assigned isog`AlphaDualAtConjStablePlaceRhoId then
        isog`AlphaDualAtConjStablePlaceRhoId:=AssociativeArray();
    end if;
    nu_Hash:=myHash(nu);
    if not IsDefined(isog`AlphaDualAtConjStablePlaceRhoId,nu_Hash) then
        _,_,_,_,A,pi_A,_,Delta_map:=DieudonneAlgebraCommEndAlg(isog);
        bar_onA:=BarOnDieudonneAlgebra(isog);
        p:=CharacteristicFiniteField(isog);
        q:=FiniteField(isog);
        a:=Ilog(p,q);
        OA:=MaximalOrder(A);
        PPs_nu:=PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu);
        f_nu:=InertiaDegree(nu);
        g_nu:=GCD(a,f_nu); //q=p^a
        assert #PPs_nu eq g_nu;
        // In the construction of delta_nu, we need to divide by g_nu. 
        // We increase the precision accordingly.
        m2:=m+g_nu;
        OA_mod_I,qOA_mod_I,sigma:=SigmaOnQuotientOfOA(isog,p^m2*OA);

        Rs_nu:=[];
        rs_nu:=<>;
        Us_nu:=[];
        us_nu:=<>;
        PPs_nu_m2:=[];
        for PP in PPs_nu do
            PP_m2:=PP^(RamificationIndex(PP)*m2);
            Append(~PPs_nu_m2,PP_m2);
            R,r:=ResidueRing(OA,PP_m2);
            U,u:=ResidueRingUnits(OA,PP_m2);
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
            Append(~Us_nu,U);
            Append(~us_nu,u);
        end for;
        PPs_nu_m2_prod:=&*PPs_nu_m2;

        Q,embs,projs:=DirectSum(Rs_nu);
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   y:->CRT(PPs_nu_m2,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
        pi_Q:=pr(pi_A);
        assert forall{x:x in Generators(Q)|pr(x@@pr) eq x};

        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT(PPs_nu_m2,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        sigma_U:=hom<U->U | [U.i@@U_pr@qOA_mod_I@sigma@@qOA_mod_I@U_pr : i in [1..Ngens(U)]]>; 
        assert forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};

        image_phi:=function(gamma)
            // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^m)^*
            // phi does the following two steps
            // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_{nu,i}^m
            // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
            beta:=&+[i lt g_nu select U_embs[i](Zero(Us_nu[i])) else U_embs[i](gamma):i in [1..g_nu]];
            // Action of the Frobenius on U
            img:=(&+[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
            assert sigma_U(img) eq img;
            return img;
        end function;
        phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
        
        t_nu:=UniformizersInQFAt_p(isog,[nu])[1]; // in E
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        val_nu:=Valuation(pi,nu); // in E
        w_nu:=integral_approx(pi,t_nu^val_nu,Dimension(E)*(m2+a),[nu]);
        wU:=U_pr(Delta_map(w_nu)); // in E->A->U
        gamma0:=wU@@phi; // in Us[g_nu], the last component of U
        gamma_A:=(&+[i lt g_nu select 
                                U_embs[i](One(A)@@us_nu[i]) else 
                                U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
        u0:=Delta_map(t_nu^(Integers()!(val_nu*g_nu/a)));
        beta_A:=(&+[i lt g_nu select 
                                embs[i](rs_nu[i](One(A))) else 
                                embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; 
        alpha_nu:=gamma_A*beta_A;
        // it is desirable that alpha_nu is not a zero divisor of A
        while IsZeroDivisor(alpha_nu) do
            alpha_nu+:=Random(PPs_nu_m2_prod);
        end while;
        // Check that alpha_nu of W-type: 1 in all components but the last one, and with sigma-norm = pi_nu
        assert forall{i:i in [1..g_nu-1]|alpha_nu-1 in PPs_nu_m2[i]};
        assert forall{i:i in [1..g_nu]|X-pi_A in PPs_nu_m2[i]} where X:=&*[alpha_nu@qOA_mod_I@(sigma^i)@@qOA_mod_I:i in [0..a-1]];

        // We want to compute delta_inv_nu:=delta_nu^-1, where
        //     delta_nu=delta_1*(1,1/p,...,1/p^(g_nu-1))
        // with delta_1 totally real satisfying 
        //     tau(delta_1)/delta_1 = u_nu*bar(u_nu)/p^g_nu.
        // So, we get 
        //     delta_inv_nu=delta_inv_1*(1,p,...,p^(g-1))
        // with delta_inv_1 totally real satisfying
        //     delta_inv_1/tau(delta_inv_1) = u_nu*bar(u_nu)/p^g_nu.
        pg_nu:=A!(p^g_nu);
        a_div_g_nu:=Integers()!(a/g_nu);
        U:=&*[alpha_nu@qOA_mod_I@(sigma^i)@@qOA_mod_I:i in [0..g_nu-1]]; // = (u_nu,...,u_nu) in A
        bU:=bar_onA(U);
        pA:=PlacesAboveRationalPrime(A,p);
        UbU:=U*bU;
        UU:=integral_approx(UbU,pg_nu,Dimension(A)+m+g_nu,PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu)); //FIXME the precision here is likely high enough, but maybe not optimal
        assert U in OA;
        assert bU in OA;
        assert UU in OA;
        assert Valuation(UU,P) eq 0 where P:=PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu)[g_nu];
        PPs_nu_m:=[PP^(RamificationIndex(PP)+m):PP in PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu)];
        PPs_nu_m_prod:=&*(PPs_nu_m);
        assert forall{k:k in [1..g_nu]|&*[bU@qOA_mod_I@(sigma^(g_nu*i))@@qOA_mod_I:i in [0..a_div_g_nu-1]]-(q/pi_A) in PPs_nu_m[k]};
        assert forall{k:k in [1..g_nu]|&*[ U@qOA_mod_I@(sigma^(g_nu*i))@@qOA_mod_I:i in [0..a_div_g_nu-1] ]-pi_A in PPs_nu_m[k]};
        assert forall{k:k in [1..g_nu]|&*[UU@qOA_mod_I@(sigma^(g_nu*i))@@qOA_mod_I:i in [0..a_div_g_nu-1]]-1 in PPs_nu_m[k]};
        U_gnu,u_gnu:=ResidueRingUnits(OA,PPs_nu_m[g_nu]);
        UU:=UU@@u_gnu; // in U_gnu

        bar_onU_gnu_over_id:=iso<U_gnu->U_gnu|[(U_gnu.i@u_gnu@bar_onA@@u_gnu)-U_gnu.i :i in [1..Ngens(U_gnu)]]>;
        U_gnu_TP:=Kernel(bar_onU_gnu_over_id);
        // tau = sigma^g_nu
        tau:=iso<U_gnu->U_gnu|[U_gnu.i@u_gnu@qOA_mod_I@(sigma^g_nu)@@qOA_mod_I@@u_gnu :i in [1..Ngens(U_gnu)]]>;
        assert forall{i:i in [1..Ngens(U_gnu)]|(tau^(a_div_g_nu))(U_gnu.i) eq U_gnu.i};
        // tau/id only on U_gnu_TP
        id_over_tau:=hom<U_gnu_TP->U_gnu_TP|[U_gnu_TP.i-U_gnu_TP!((U_gnu_TP.i@tau)) :i in [1..Ngens(U_gnu_TP)]]>;
        assert &+[UU@(tau^i) :i in [0..(a_div_g_nu)-1]] eq Zero(U_gnu); // N_{LE_nu/E_nu} = 1
        delta1_inv:=((U_gnu_TP!UU)@@id_over_tau)@u_gnu; //in A
        delta_inv_nu:=CRT(PPs_nu_m,[delta1_inv*p^(i-1):i in [1..g_nu]]);
        while IsZeroDivisor(delta_inv_nu) do
            delta_inv_nu+:=Random(PPs_nu_m_prod);
        end while;
        isog`AlphaDualAtConjStablePlaceRhoId[nu_Hash]:=<alpha_nu,delta_inv_nu>;
//        delta_nu:=[delta1*p^-(i-1):i in [1..g_nu]];
//        delta_nu:=[pg_nu*x:x in delta_nu]; // to make sure that it is in OA
//        assert forall{x:x in delta_nu|x in OA};
//        delta_nu:=pg_nu^-1 * CRT(PPs_nu_m,delta_nu); //in A
//        assert delta_nu in OA;
//        // to make sure that the lift is not a zero divisor
//        while IsZeroDivisor(delta_nu) do
//            delta_nu+:=Random(PPs_nu_m_prod);
//        end while;
//        isog`AlphaDualAtConjStablePlaceRhoId[nu_Hash]:=<alpha_nu,delta_nu>;
    end if;
    return Explode(isog`AlphaDualAtConjStablePlaceRhoId[nu_Hash]);
end intrinsic;

intrinsic AlphaDualAtConjStablePlaceRhoNotId(isog::IsogenyClassFq,nu::AlgEtQIdl,m::RngIntElt)->AlgEtQElt
{Given an isogeny class isog, a conjugate stable place nu of the DeligneAlgebra such that the action of the CM-involution on the places above nu is a permutation of order 2 and a positive integer m, returns // TODO 
// alpha_nu 
}
// NEW 20260728
    if not assigned isog`AlphaDualAtConjStablePlaceRhoNotId then
        isog`AlphaDualAtConjStablePlaceRhoNotId:=AssociativeArray();
    end if;
    nu_Hash:=myHash(nu);
    if not IsDefined(isog`AlphaDualAtConjStablePlaceRhoNotId,nu_Hash) then
        p:=CharacteristicFiniteField(isog);
        a:=Ilog(p,FiniteField(isog));
        assert IsEven(a);
        pa2:=p^(a div 2);
        t_nu:=UniformizersInQFAt_p(isog,[nu])[1]; // in E
        E:=DeligneAlgebra(isog);
        OE:=MaximalOrder(E);
        pi:=PrimitiveElement(E);
        // pi/p^(a/2) is in OE_nu^*, we want gamma such that bar(gamma)/gamma = pi/p^(a/2).
        UE,uE:=ResidueRingUnits(OE,nu^(RamificationIndex(nu)+m)); // uE:UE->OE
        bar_id:=iso<UE->UE|[-UE.i+(ComplexConjugate(UE.i@uE)@@uE):i in [1..Ngens(UE)]]>;

        pE0,pE01,pE1:=PlacesOfQFAbove_p(isog);
        pE:=pE0 cat pE01 cat pE1;
        gamma:=integral_approx(pi,E!pa2,RamificationIndex(nu)+m,[nu]); //FIXME is this precision enough?
        gamma:=gamma@@uE@@bar_id@uE;

        _,_,_,_,A,pi_A,_,Delta_map:=DieudonneAlgebraCommEndAlg(isog);
        bar_onA:=BarOnDieudonneAlgebra(isog);
        OA:=MaximalOrder(A);
        OA_mod_I,qOA_mod_I,sigma:=SigmaOnQuotientOfOA(isog,p^m*OA);
        PPs_nu:=PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu);
        f_nu:=InertiaDegree(nu);
        g_nu:=GCD(a,f_nu); //q=p^a
        assert #PPs_nu eq g_nu;

        Rs_nu:=[];
        rs_nu:=<>;
        Us_nu:=[];
        us_nu:=<>;
        PPs_nu_m:=[];
        for PP in PPs_nu do
            PP_m:=PP^(RamificationIndex(PP)*m);
            Append(~PPs_nu_m,PP_m);
            R,r:=ResidueRing(OA,PP_m);
            U,u:=ResidueRingUnits(OA,PP_m);
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
            Append(~Us_nu,U);
            Append(~us_nu,u);
        end for;
        PPs_nu_m_prod:=&*PPs_nu_m;

        Q,embs,projs:=DirectSum(Rs_nu);
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   y:->CRT(PPs_nu_m,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
        pi_Q:=pr(pi_A);
        assert forall{x:x in Generators(Q)|pr(x@@pr) eq x};

        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT(PPs_nu_m ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        sigma_U:=hom<U->U | [U.i@@U_pr@qOA_mod_I@sigma@@qOA_mod_I@U_pr : i in [1..Ngens(U)]]>; 
        assert forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};

        image_phi:=function(gamma)
            // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^m)^*
            // phi does the following two steps
            // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_{nu,i}^m
            // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
            beta:=&+[i lt g_nu select U_embs[i](Zero(Us_nu[i])) else U_embs[i](gamma):i in [1..g_nu]];
            // Action of the Frobenius on U
            img:=(&+[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
            assert sigma_U(img) eq img;
            return img;
        end function;
        phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
//FIXME
print g_nu;
        gammaU:=U_pr(Delta_map(gamma));
        eps_A:=(&+([ i lt g_nu select U_embs[i](Zero(Us_nu[i])) 
                               else gammaU@@phi@U_embs[g_nu] : i in [1..g_nu]]))@@U_pr; // (1,...,1,eps)
        eps_A_inv:=(&+([ i lt g_nu select U_embs[i](Zero(Us_nu[i])) 
                               else -gammaU@@phi@U_embs[g_nu] : i in [1..g_nu]]))@@U_pr; // (1,...,1,eps^-1)
        assert forall{i:i in [1..g_nu-1]|eps_A-1 in PPs_nu_m[i]};
        assert forall{i:i in [1..g_nu-1]|eps_A_inv-1 in PPs_nu_m[i]};
        assert forall{i:i in [1..g_nu]|eps_A*eps_A_inv-1 in PPs_nu_m[i]};

        eps_A_bar:=bar_onA(eps_A); // (1,...,1,bar(eps),1,...,1)
        assert forall{i:i in [1..g_nu]|i ne (g_nu div 2) select eps_A_bar-1 in PPs_nu_m[i] else true};

        p_half:=(&+([i le (g_nu div 2) select embs[i](rs_nu[i](One(A))) 
                                      else embs[i](rs_nu[i](p*One(A))) : i in [1..g_nu]]))@@pr; // (1,...,1,p,...,p)
        alpha_nu:=eps_A_inv*eps_A_bar*p_half; 
        assert forall{i:i in [1..(g_nu div 2)-1]|alpha_nu-1 in PPs_nu_m[i]};
        assert forall{i:i in [(g_nu div 2)+1..g_nu-1]|alpha_nu-p in PPs_nu_m[i]};
        assert alpha_nu-eps_A_bar in PPs_nu_m[g_nu div 2];
        assert alpha_nu-p*eps_A_inv in PPs_nu_m[g_nu];
        assert forall{i:i in [1..g_nu]|X-pi_A in PPs_nu_m[i]} where X:=&*[alpha_nu@qOA_mod_I@(sigma^i)@@qOA_mod_I:i in [0..a-1]];
        isog`AlphaDualAtConjStablePlaceRhoNotId[nu_Hash]:=alpha_nu;
    end if;
    return isog`AlphaDualAtConjStablePlaceRhoNotId[nu_Hash];
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////SemilinearOperators/////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic SemilinearOperatorsWType(isog::IsogenyClassFq,J::AlgEtQIdl,m0::RngIntElt,slopes::MonStgElt)->GrpAb,Map,Map,Map,AlgEtQIdl,RngIntElt,AlgEtQIdl
{Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of W-type, and a precision m0, returns Q,q,FQ,VQ where Q is isomorphic to direct sum of (J/p^m0*J)_nu for nu of slope in (0,1) or any --depending whether the argument slope is "(0,1)" or "all"-- q:J->Q is the natural projection and FQ,VQ are the reductions of F,V to Q. Moreover the intrinsic returns also the ideal den_ideal so that Q=J/den_ideal, and m0 and J.}
    if not assigned isog`SemilinearOperatorsWType then
        p:=CharacteristicFiniteField(isog);
        a:=Ilog(p,FiniteField(isog));
        _,_,_,_,A,pi_A,OA,_,WR,A_as_vector_space_over_L_data,OA_as_abelian_group_data:=DieudonneAlgebraCommEndAlg(isog);

        require slopes in {"(0,1)","all"} : "Invalid parameter slopes";
        pps0,pps01,pps1:=PrimesOfSAbove_p(isog,WR);
        nus0,nus01,nus1:=PlacesOfQFAbove_p(isog);
        if slopes eq "(0,1)" then
            pps:=pps01;
            nus:=nus01;
        elif slopes eq "all" then
            pps:=pps0 cat pps01 cat pps1;
            nus:=nus0 cat nus01 cat nus1;
        end if;

        // Need M such that P^M*J c p^(m0+1)J, locally at P, for each P in pps.
        // By looking at the composition series, one deduces that any 
        // M \geq Truncate(Log(Index(OA,P),Index(J,p^(m0+1)J)) will do.
        size:=(p^(m0+1))^AbsoluteDimension(Algebra(OA)); // size = #J/p^(m0+1)J = (p^(m0+1))^dim_Q(A)
        M:=Max( [ Truncate(Log(Index(WR,P),size)) : P in pps] );
        //M1:=M+10; "WARNING: M is forced now from ",M,"to",M1; M:=M1; //for debugging
        PP_M:=(&*pps)^M;
        PP_M_J:=J*PP_M;

        Qm0_1,qm0_1:=Quotient(J,p^(m0+1)*J+PP_M_J);
        den_ideal:=p^m0*J+PP_M_J;
        Qm0,qm0:=Quotient(J,den_ideal);

        pr:=hom< Qm0_1->Qm0 | [ qm0(Qm0_1.i@@qm0_1) : i in [1..Ngens(Qm0_1)]] >;
        assert IsSurjective(pr);
        assert forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
        
        JOA:=OA!!J;
        assert JOA subset OA;
        m1:=m0+1+Valuation(Index(OA,JOA),p);
        //m2:=m1+10; "WARNING: m1 is forced now from ",m1,"to",m2; m1:=m2; //for debugging
        // We have the following inclusions, locally at p: p^m1*OA c p^(m0+1)*J c I c J c OA.
        // This means the approximation of sigma on OA/p^m1*OA will give a well defined sigma on Q=J/I
        QOA,qOA,sigma_QOA:=SigmaOnQuotientOfOA(isog,p^m1*OA);

        PPs:=[];
        alpha_s:=[];
        for nu in nus do
            alpha_nu,PPs_nu:=AlphaWTypeAtPlace(isog,nu,m1);
            Append(~PPs,PPs_nu);
            Append(~alpha_s,alpha_nu);
        end for;
        alpha:=CRT(PPs,alpha_s);
        vprintf AlphaWTypeAtPlace,2 : "\n\talpha_s = %o",StripWhiteSpace(Sprint(PrintSeqAlgEtQElt(alpha_s)));
        vprintf AlphaWTypeAtPlace,2 : "\n\talpha = %o",StripWhiteSpace(Sprint(PrintSeqAlgEtQElt([alpha])[1]));

        FQm0:=hom<Qm0->Qm0 | [ qm0(alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0)]]>;
        FQm0_1:=hom<Qm0_1->Qm0_1 | [ qm0_1(alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0_1)]]>;
        assert forall{ x : x in Generators(Qm0_1) | FQm0(pr(x)) eq pr(FQm0_1(x))};
        // in the next assert's, we check that FQm0^a and FQm0_1^a are equal to multiplication by pi_A
        assert forall{ x : x in Generators(Qm0) | (FQm0^a)(x) eq qm0(pi_A*(x@@qm0))};
        assert forall{ x : x in Generators(Qm0_1) | (FQm0_1^a)(x) eq qm0_1(pi_A*(x@@qm0_1))};

        mp:=hom<Qm0_1->Qm0_1 | [ p*(Qm0_1.j) : j in [1..Ngens(Qm0_1)] ]>;
        assert mp eq hom<Qm0_1->Qm0_1 | [ qm0_1(p*(Qm0_1.j)@@qm0_1) : j in [1..Ngens(Qm0_1)] ]>;
        assert Image(mp) subset Image(FQm0_1);

        z_gamma_s:=[];
        for i in [1..Ngens(Qm0)] do
            gamma:=Qm0.i;
            x_gamma:=gamma@@pr;
            z_gamma:=(mp(x_gamma))@@FQm0_1;
            Append(~z_gamma_s,z_gamma);
        end for;
        VQm0:=hom<Qm0->Qm0 | [ pr(z_gamma_s[i]) : i in [1..Ngens(Qm0)] ] >;
        assert forall{ g : g in Generators(Qm0) | FQm0(VQm0(g)) eq p*g };
        assert forall{ g : g in Generators(Qm0) | VQm0(FQm0(g)) eq p*g };

        // We check semilinearity for F, V: F*x = sigma(x)*F and x*V=V*sigma(x)  forall x in L?
        // It suffices to check if for powers of zz in OA.
        E:=DeligneAlgebra(isog);
        _,_,_,mAW_zbOE:=Explode(A_as_vector_space_over_L_data);
        W:=Codomain(mAW_zbOE);
        FOA,fOA,_:=Explode(OA_as_abelian_group_data);
        _,F,_,LL,LLtoL,imgs_zz:=Explode(A`sigma_fin_prec);
        // - We construct the embedding F=ZZ[zz] -> OA=FOA induced by zz:->sum_i zz*zi 
        //   where zi is the image of a ZBasis of OA in FOA
        FtoFOA:=map<F->FOA|x:->fOA((W![ LLtoL(LL!Eltseq(x)):i in [1..AbsoluteDimension(E)]])@@mAW_zbOE)>; 
        powers_zz_diagonally_inOA_via_zbOE:=[ (FtoFOA(z))@@fOA : z in imgs_zz ];
        for z in powers_zz_diagonally_inOA_via_zbOE do
            sigma_z:=z@qOA@sigma_QOA@@qOA;
            z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
            sigma_z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(sigma_z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
            assert forall{i:i in [1..Ngens(Qm0)]|FQm0(z_action_Qm0(Qm0.i)) eq sigma_z_action_Qm0(FQm0(Qm0.i))};
            assert forall{i:i in [1..Ngens(Qm0)]|z_action_Qm0(VQm0(Qm0.i)) eq VQm0(sigma_z_action_Qm0(Qm0.i))};
        end for;
        isog`SemilinearOperatorsWType:=<Qm0,qm0,FQm0,VQm0,den_ideal,m0,J,slopes>;
    end if;
    return Explode(isog`SemilinearOperatorsWType);
end intrinsic;

intrinsic SemilinearOperatorsDualComp(isog::IsogenyClassFq,J::AlgEtQIdl,m0::RngIntElt)->GrpAb,Map,Map,Map,AlgEtQIdl,RngIntElt,AlgEtQIdl
{Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of XXXX //TODO update this description
, and a precision m0, returns Qm0,qm0,FQm0,VQm0 where Qm0 is isomorphic to direct sum of (J/p^m0*J)_nu where nu runs over all places above p, qm0:J->Qm0 is the natural projection and FQm0,VQm0 are the reductions of F,V to Qm0. Moreover the intrinsic returns also the ideal den_ideal so that Qm0=J/den_ideal, and m0 and J.}
// NEW 20260727
    if not assigned isog`SemilinearOperatorsDualComp then
        p:=CharacteristicFiniteField(isog);
        a:=Ilog(p,FiniteField(isog));
        _,_,_,_,A,pi_A,OA,_,_,A_as_vector_space_over_L_data,OA_as_abelian_group_data:=DieudonneAlgebraCommEndAlg(isog);
        bar_onA:=BarOnDieudonneAlgebra(isog);

        // Quotients
        Qm0_1,qm0_1:=Quotient(J,p^(m0+1)*J);
        den_ideal:=p^m0*J;
        Qm0,qm0:=Quotient(J,den_ideal);
        pr:=hom< Qm0_1->Qm0 | [ qm0(Qm0_1.i@@qm0_1) : i in [1..Ngens(Qm0_1)]] >;
        assert IsSurjective(pr);
        assert forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
       
        JOA:=OA!!J;
        assert JOA subset OA;
       
        // We divide nus in 3 categories, and construct alpha_nu, delta_nu according to the following recepies:
        conj_pairs,rho_id,rho_notid:=SortPlacesOfQFAbove_p(isog);
        // for <nu,nub> in conj_pairs, that is, nub=bar(nu):
        //      - pick one place in the pair (nu,bar(nu)), which it will be called of W-type.
        //      - store this info in an attribute of nu and of bar(nu), since it is needed to compute
        //        the Ms with maximal End which are F,V-stable.
        //      - Then we want alpha_nu = (1,...,1,u_nu) and alpha_{bar(nu)}=p/bar(alpha_nu) where
        //        N_{LE_nu/E_nu}(u_nu)=pi_nu, i.e. alpha_nu is of W-type.
        //      - Our method computes alpha_nu in OA, but then alpha_{bar(nu)} won't be integral.
        //      - We use the intrinisc AlphaDualAtNonConjStablePlace which returns approximations at 
        //        precision m2 of alpha_nu of W-type and of the integral element q/alpha_nu.
        //      - Then we 'divide' the latter by p^(a-1) by taking a preimage via the multiplication by p^(a-1)-map
        //        and apply the bar_onA to obtain the multiplication-by-alpha_bar(nu) at precision m0+1, as 
        //        required to compute FQm0_1 on the bar(nu)-component.
        //      - For to be well defined, we set m2:=(m0+1)+(a-1)=m0+a;
        //      - For this case, we can set delta_nu=delta_bar(nu)=1.
        //
        // for nu in rho_id, that is, nu=bar(nu) and bar_onA inducing the identity on places of A above nu:       
        //      - We take alpha_nu=(1,...,1,u_nu) of W-type.
        //      - We take delta_nu=delta_1*(1,1/p,...,1/p^(g-1)), where delta_1 is a totally real unit satisfying
        //        tau(delta_1)/delta_1=u_nu*bar(u_nu)/p^g.
        //      - We need to compute delta_nu at precision high enough so that the ideal delta*W_R is correctly
        //        computed. Note that delta_nu^-1 is integral and in the ideal p^(g-1)*OA.
        //      - So we need to compute delta_nu^-1 and hence also alpha_nu at precision m0+1)+(g-1)=m0+g.
        //      - We designed the intrinsic AlphaDualAtConjStablePlaceRhoId which returns alpha_nu, delta_nu^-1.
        //
        // for nu in rho_notid, that is, nu=bar(nu) and bar_onA inducing a permutation of order 2:       
        //      - We take delta_nu=1;
        //      - We take alpha_nu=(1,..,1,bar(eps),p,...,p,p/eps) where N_{LE_nu/E_nu}(eps)=gamma for
        //        gamma satisfying bar(gamma)/gamma=pi_nu/p^(a/2).
        //      - We designed the intrinsic AlphaDualAtConjStablePlaceRhoNotId for this purpose.

        PPs:=AssociativeArray(); // PPs[nu]:=(prod of primes of A above nu)^(ramif of any of these)
        PPs_m0:=AssociativeArray(); // PPs[nu]:=(prod of primes of A above nu)^(m0+ramif of any of these)
        PPs_m0_1:=AssociativeArray(); // PPs[nu]:=(prod of primes of A above nu)^(m0+1+ramif of any of these)
        nus:=&cat[[pair[1],pair[2]]:pair in conj_pairs] cat rho_id cat rho_notid;
        Hnus:=[myHash(nu):nu in nus];
        for nu in nus do
            PP:=PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu);
            e:=RamificationIndex(PP[1]);
            PP:=(&*PP)^e;
            PPs[myHash(nu)]:=PP;
            PPs_m0[myHash(nu)]:=PP^m0;
            PPs_m0_1[myHash(nu)]:=PP^(m0+1);
        end for;
        delta_inv_nus:=AssociativeArray();
        images_gens_Qm0:=AssociativeArray();
        images_gens_Qm0_1:=AssociativeArray();
        m1:=m0+1+Valuation(Index(OA,JOA),p);
        //m2:=m1+100; "WARNING: m1 is forced now from ",m1,"to",m2; m1:=m2; //for debugging
        // We have the following inclusions, locally at p: p^m1*OA c p^(m0+1)*J c I c J c OA.
        m2:=m1+a-1; //beause we need to take preimage via mult by p^(a-1)
        QOA,qOA,sigma_QOA:=SigmaOnQuotientOfOA(isog,p^m2*OA);
        m3:=m2+a-1; // precision at which alpha_nu, q_alpha_nu are computed.
                     //FIXME It seems to me that m3=m2 should suffice, but then I get an error at 788.
                     // adding a-1 solves it, but I don't get why.
        PPs_m3:=[PPs[Hmu]^m3:Hmu in Hnus];
        for pair in conj_pairs do
            nu:=pair[1];
            nub:=pair[2];
            Hnu:=myHash(nu);
            Hnub:=myHash(nub);
            delta_inv_nus[Hnu]:=One(A);
            delta_inv_nus[Hnub]:=One(A);
            alpha,q_alpha:=AlphaDualAtNonConjStablePlace(isog,nu,m3);
            q_alpha_b:=bar_onA(q_alpha);
            //TODO explains the next 3 lines
            alpha:=CRT(PPs_m3,[Hmu eq Hnu select alpha else Zero(A):Hmu in Hnus]);
            q_alpha_b:=CRT(PPs_m3,[Hmu eq Hnub select q_alpha_b else Zero(A):Hmu in Hnus]);
            images_gens_Qm0[Hnu]:=[alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA) : i in [1..Ngens(Qm0)]];
            images_gens_Qm0_1[Hnu]:=[alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA): i in [1..Ngens(Qm0_1)]];
            assert forall{g:g in images_gens_Qm0[Hnu]|g in J};
            assert forall{g:g in images_gens_Qm0_1[Hnu]|g in J};
            // now we divide by p^(a-1) by taking a preimage
            S,s:=Quotient((p^-(a-1))*OA,p^(m2-(a-1))*OA); 
            T,t:=ResidueRing(OA,p^m2*OA); 
            mult:=iso<S->T|[((S.i@@s)*(p^(a-1)))@t:i in [1..Ngens(S)]]>;
            image_qq:=function(g,qq)
            // qq can be either qm0 or qm0_1
                gg:=(q_alpha_b*(g@@qq@qOA@sigma_QOA@@qOA))@t@@mult@@s;
                // mult^-1 is mod (pOA)^m2, so I need to do a further CRT to isolate the nub component.
                // For simplicity we just do the CRT mod p^m3 also when working mod p^m0 or p^m0+1, since the
                // correspodning CRT-data has already been computed.
                gg:=CRT(PPs_m3,[mu eq nub select gg else Zero(A):mu in nus]);
                return gg;
            end function;
            images_gens_Qm0[Hnub]:=[image_qq(Qm0.i,qm0) : i in [1..Ngens(Qm0)]];
            images_gens_Qm0_1[Hnub]:=[image_qq(Qm0_1.i,qm0_1) : i in [1..Ngens(Qm0_1)]];
            assert forall{g:g in images_gens_Qm0[Hnub]|g in J};
            assert forall{g:g in images_gens_Qm0_1[Hnub]|g in J};
        end for;
        // TODO why do I work with this choice of m2 here?
        //m2:=m0+1+a; // m0+1+g_nu suffices.
        QOA,qOA,sigma_QOA:=SigmaOnQuotientOfOA(isog,p^m2*OA);
        for nu in rho_id do
            Hnu:=myHash(nu);
            g_nu:=GCD(Ilog(CharacteristicFiniteField(isog),FiniteField(isog)),InertiaDegree(nu));
            alpha,delta_inv:=AlphaDualAtConjStablePlaceRhoId(isog,nu,m2);
            //TODO explains the next 2 lines, why can I CRT with prec m3?
            //PPs_m2:=[PPs[Hmu]^m2:Hmu in Hnus];
            alpha:=CRT(PPs_m3,[Hmu eq Hnu select alpha else Zero(A):Hmu in Hnus]);
            delta_inv_nus[Hnu]:=delta_inv;
            images_gens_Qm0[Hnu]:=[alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA) : i in [1..Ngens(Qm0)]];
            images_gens_Qm0_1[Hnu]:=[alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA): i in [1..Ngens(Qm0_1)]];
            assert forall{g:g in images_gens_Qm0[Hnu]|g in J};
            assert forall{g:g in images_gens_Qm0_1[Hnu]|g in J};
        end for;
        // TODO why do I work with this choice of m2 here?
        m2:=m0+1;
        for nu in rho_notid do
            Hnu:=myHash(nu);
            alpha:=AlphaDualAtConjStablePlaceRhoNotId(isog,nu,m2);
            //alpha:=AlphaDualAtConjStablePlaceRhoNotId(isog,nu,m0+1);
            //TODO explains the next line. Do I want to work at prec m3 or m0+1?
            //alpha:=CRT([PPs_m0_1[Hmu]:Hmu in Hnus],[Hmu eq Hnu select alpha else Zero(A):Hmu in Hnus]);
            alpha:=CRT(PPs_m3,[Hmu eq Hnu select alpha else Zero(A):Hmu in Hnus]);
            delta_inv_nus[Hnu]:=One(A);
            images_gens_Qm0[Hnu]:=[alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA) : i in [1..Ngens(Qm0)]];
            images_gens_Qm0_1[Hnu]:=[alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA): i in [1..Ngens(Qm0_1)]];
            assert forall{g:g in images_gens_Qm0[Hnu]|g in J};
            assert forall{g:g in images_gens_Qm0_1[Hnu]|g in J};
        end for;
        delta_inv:=CRT([PPs_m0_1[Hmu]^a:Hmu in Hnus],[delta_inv_nus[Hmu]:Hmu in Hnus]);
        J_Jnus,Jnus_J:=ChineseRemainderTheoremFunctions(JOA,[PPs_m0[Hmu]:Hmu in Hnus]); // precision m0
        FQm0:=hom<Qm0->Qm0| [qm0(Jnus_J([images_gens_Qm0[Hmu][i]:Hmu in Hnus])) : i in [1..Ngens(Qm0)] ]>;
        J_Jnus,Jnus_J:=ChineseRemainderTheoremFunctions(JOA,[PPs_m0_1[Hmu]:Hmu in Hnus]); // precision m0+1
        FQm0_1:=hom<Qm0_1->Qm0_1| [qm0_1(Jnus_J([images_gens_Qm0_1[Hmu][i]:Hmu in Hnus])) : i in [1..Ngens(Qm0_1)] ]>;
        assert forall{ x : x in Generators(Qm0_1) | FQm0(pr(x)) eq pr(FQm0_1(x))};
        // in the next assert's, we check that FQm0^a and FQm0_1^a are equal to multiplication by pi_A
        assert forall{ x : x in Generators(Qm0) | (FQm0^a)(x) eq qm0(pi_A*(x@@qm0))};
        assert forall{ x : x in Generators(Qm0_1) | (FQm0_1^a)(x) eq qm0_1(pi_A*(x@@qm0_1))};

        mp:=hom<Qm0_1->Qm0_1 | [ p*(Qm0_1.j) : j in [1..Ngens(Qm0_1)] ]>;
        assert mp eq hom<Qm0_1->Qm0_1 | [ qm0_1(p*(Qm0_1.j)@@qm0_1) : j in [1..Ngens(Qm0_1)] ]>;
        assert Image(mp) subset Image(FQm0_1);

        z_gamma_s:=[];
        for i in [1..Ngens(Qm0)] do
            gamma:=Qm0.i;
            x_gamma:=gamma@@pr;
            z_gamma:=(mp(x_gamma))@@FQm0_1;
            Append(~z_gamma_s,z_gamma);
        end for;
        VQm0:=hom<Qm0->Qm0 | [ pr(z_gamma_s[i]) : i in [1..Ngens(Qm0)] ] >;
        assert forall{ g : g in Generators(Qm0) | FQm0(VQm0(g)) eq p*g };
        assert forall{ g : g in Generators(Qm0) | VQm0(FQm0(g)) eq p*g };

        // We check semilinearity for F, V: F*x = sigma(x)*F and x*V=V*sigma(x)  forall x in L?
        // It suffices to check if for powers of zz in OA.
        E:=DeligneAlgebra(isog);
        _,_,_,mAW_zbOE:=Explode(A_as_vector_space_over_L_data);
        W:=Codomain(mAW_zbOE);
        FOA,fOA,_:=Explode(OA_as_abelian_group_data);
        _,F,_,LL,LLtoL,imgs_zz:=Explode(A`sigma_fin_prec);
        // - We construct the embedding F=ZZ[zz] -> OA=FOA induced by zz:->sum_i zz*zi 
        //   where zi is the image of a ZBasis of OA in FOA
        FtoFOA:=map<F->FOA|x:->fOA((W![ LLtoL(LL!Eltseq(x)):i in [1..AbsoluteDimension(E)]])@@mAW_zbOE)>; 
        powers_zz_diagonally_inOA_via_zbOE:=[ (FtoFOA(z))@@fOA : z in imgs_zz ];
        for z in powers_zz_diagonally_inOA_via_zbOE do
            sigma_z:=z@qOA@sigma_QOA@@qOA;
            z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
            sigma_z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(sigma_z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
            assert forall{i:i in [1..Ngens(Qm0)]|FQm0(z_action_Qm0(Qm0.i)) eq sigma_z_action_Qm0(FQm0(Qm0.i))};
            assert forall{i:i in [1..Ngens(Qm0)]|z_action_Qm0(VQm0(Qm0.i)) eq VQm0(sigma_z_action_Qm0(Qm0.i))};
        end for;
        isog`delta_inv:=delta_inv;
        isog`SemilinearOperatorsDualComp:=<Qm0,qm0,FQm0,VQm0,den_ideal,m0,J>;
    end if;
    return Explode(isog`SemilinearOperatorsDualComp);
end intrinsic;

intrinsic SemilinearOperators(isog::IsogenyClassFq)->GrpAb,Map,Map,Map,AlgEtQIdl,RngIntElt,AlgEtQIdl,MonStgElt
{Returns the attribute SemilinearOperatorsWType of the isogeny class.}
    // TODO update with SemilinearOperatorsDualComp
    require assigned isog`SemilinearOperatorsWType : "Run first IsomorphismClassesDieudonneModules(isog)";
    return Explode(isog`SemilinearOperatorsWType);
end intrinsic;

/*
    // TEST Dual approach
    //////////////////////
    // large data set
    //////////////////////
    
    PP<x>:=PolynomialRing(Integers());
    SetAssertions(2);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    all:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/weil_poly_sq_not_prime-ord-almord.txt"));
    m0:=10;
    for s in all do
        try
            cc:=[StringToInteger(c):c in Split(s,"[,]")];
            g:=(#cc-1) div 2;
            q:=Round(cc[1]^(1/g));
            _,p,a:=IsPrimePower(q);
            if a lt 4 then
                h:=PP!cc;
                ccs:=StripWhiteSpace(Sprint(cc));
                isog:=IsogenyClass(h);
                conj_pairs,rho_id,rho_notid:=SortPlacesOfQFAbove_p(isog);
                printf "%o,%o,%o\ta=%o\t[OA:JOA]=",#conj_pairs,#rho_id,#rho_notid,a;
                for exps in ExponentsDual(isog) do
                    plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
                    plE:=plE0 cat plE01 cat plE1;
                    plA:=&cat[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE];
                    assert #plA eq #exps;
                    JOA:=&*[ plA[i]^exps[i] : i in [1..#exps] ]; 
                    _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
                    assert JOA subset OA;
                    ind:=Index(OA,JOA);
                    test,n:=IsPowerOf(ind,p);
                    assert test;
                    J:=WR!!JOA;
                    ZBasisLLL(J);
                    printf "%o^%o ",p,n;
                    _:=SemilinearOperatorsDualComp(isog,J,m0);
                end for;
                printf "%o OK\n",ccs;
            end if;
        catch e
            printf "%o %o ERROR\n",e`Position,ccs;
        end try;
    end for;

    //////////////////////
    // Selected ones, giving ERROR
    //////////////////////

    PP<x>:=PolynomialRing(Integers());
    SetAssertions(2);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    m0:=10;
    all:=[
          [81,0,-9,0,1],                       // 0,0,1 ERROR, 534 not always occurring
          [81,0,-9,0,1],                       // 0,0,1 ERROR, 534 not always occurring
          [81,0,-9,0,1],                       // 0,0,1 ERROR, 534 not always occurring
          [15625,-10000,3500,-825,140,-16,1],  // 1,0,1 ERROR, 534 not always occurring
          [15625,-10000,3500,-825,140,-16,1],  // 1,0,1 ERROR, 534 not always occurring
          [15625,-10000,3500,-825,140,-16,1],  // 1,0,1 ERROR, 534 not always occurring
          [15625,-10625,3750,-875,150,-17,1],  // 2,0,0 
          [15625,-8750,2500,-525,100,-14,1],   // 2,0,0 
          [15625,-9375,3125,-725,125,-15,1]    // 1,0,0 FIXED, 788 not always occurring
         ]; 
    for cc in all do
        try
            g:=(#cc-1) div 2;
            q:=Round(cc[1]^(1/g));
            _,p,a:=IsPrimePower(q);
            if a lt 4 then
                h:=PP!cc;
                ccs:=StripWhiteSpace(Sprint(cc));
                isog:=IsogenyClass(h);
                conj_pairs,rho_id,rho_notid:=SortPlacesOfQFAbove_p(isog);
                printf "%o,%o,%o\ta=%o\t[OA:JOA]=",#conj_pairs,#rho_id,#rho_notid,a;
                for exps in ExponentsDual(isog) do
                    plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
                    plE:=plE0 cat plE01 cat plE1;
                    plA:=&cat[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE];
                    assert #plA eq #exps;
                    JOA:=&*[ plA[i]^exps[i] : i in [1..#exps] ]; 
                    _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
                    assert JOA subset OA;
                    ind:=Index(OA,JOA);
                    test,n:=IsPowerOf(ind,p);
                    assert test;
                    J:=WR!!JOA;
                    ZBasisLLL(J);
                    printf "%o^%o ",p,n;
                    _:=SemilinearOperatorsDualComp(isog,J,m0);
                end for;
                printf "%o OK\n",ccs;
            end if;
        catch e
            printf "%o %o ERROR\n",e`Position,ccs;
        end try;
    end for;

*/

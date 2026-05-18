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

declare verbose alpha_at_precision,3;

declare attributes IsogenyClassFq : AlphaWType,
                                    SemilinearOperatorsWType;

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
        _,_,_,_,A,pi_A,_,Delta_map,_,sigma_OA_mod_I:=DieudonneAlgebraCommEndAlg(isog);
        p:=CharacteristicFiniteField(isog);
        a:=Ilog(p,FiniteField(isog));
        OA:=MaximalOrder(A);
        OA_mod_I,qOA_mod_I:=ResidueRing(OA,p^m*OA);
        sigma:=sigma_OA_mod_I(OA_mod_I,qOA_mod_I,A);
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
        assert2 forall{x:x in Generators(Q)|pr(x@@pr) eq x};

        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT(PPs_nu_m ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        sigma_U:=hom<U->U | [U.i@@U_pr@qOA_mod_I@sigma@@qOA_mod_I@U_pr : i in [1..Ngens(U)]]>; 
        assert2 forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};

        image_phi:=function(gamma)
            // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^m)^*
            // phi does the following two steps
            // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_{nu,i}^m
            // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
            beta:=&*[i lt g_nu select U_embs[i]((One(A))@@us_nu[i]) else U_embs[i](gamma):i in [1..g_nu]];
            // Action of the Frobenius on U
            img:=(&*[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
            vprintf alpha_at_precision,2 : "\timg = %o\n\tsigma(img) = %o\n",img,sigma_U(img);
            assert2 sigma_U(img) eq img;
            return img;
        end function;
        phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
        
        t_nu:=UniformizersInQFAt_p(isog,[nu])[1]; // in E
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        val_nu:=Valuation(pi,nu); // in E
        // We want to compute wU in U representing the unit pi/t_nu^val_nu.
        // By constuction, this quotient is an invertible element of the completion OA_nu,
        // but it might not be an element of OA, since t_nu is picked as an element which is a unit
        // at every place of E above p (of slope in (0,1) ). 
        // This is an issues since we can only take preimages to U from OA.
        // So, we use the following workaround:
        // w_nu is in OE and congrunent to t_nu^val_nu/pi at nu and 1 at every other place above p
        // The precision is chosen to be a majorative of RamificationIndex(pp)*m [to match the quotient we are using]
        // plus Valuation(PP,pi) leq Valuation(PP,q)=RamificationIndex(pp)*a.
        pE0,pE01,pE1:=PlacesOfQFAbove_p(isog);
        pE:=pE0 cat pE01 cat pE1;
        w_nu:=CRT([pp^(Dimension(E)*(m+a)):pp in pE],[pp eq nu select t_nu^val_nu else pi : pp in pE])/pi; // in OE
        assert w_nu in MaximalOrder(E);
        wU:=-U_pr(Delta_map(w_nu)); // in E->A->U

        gamma0:=wU@@phi; // in Us[g_nu], the last componenet of U
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
        assert2 forall{i:i in [1..g_nu-1]|alpha_nu-1 in PPs_nu_m[i]};
        assert2 forall{i:i in [1..g_nu]|X-pi_A in PPs_nu_m[i]} where X:=&*[alpha_nu@qOA_mod_I@(sigma^i)@@qOA_mod_I:i in [0..a-1]];
        isog`AlphaWType[nu_Hash]:=<alpha_nu,PPs_nu_m_prod>;
    end if;
    return Explode(isog`AlphaWType[nu_Hash]);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////SemilinearOperators/////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

// CRT APPROACH -- FIXME 4.4.ag_s_abk_cq fails
// In the next two intrinsic we attempt to copute F and V on Qm0 and Qm0_1 by splitting the computation over 
// the places of OE of slope in (0,1) and then taking a CRT-direct sum of the local homomorphisms.
// It is not clear to me yet why it fails. One possibility is that the action of sigma does not preserve the
// local components. I find this unlikely, but I will leave the investigation for a future attempt if needed.
//
//intrinsic SemilinearOperatorsWTypeAtPlace(isog::IsogenyClassFq,J::AlgEtQIdl,nu::AlgEtQIdl,m0::RngIntElt)->GrpAb,Map,Map,Map,AlgEtQIdl
//{Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of W-type, a place nu of the DeligneAlgebra and a precision m0, returns Q,q,FQ,VQ where Q is isomorphic to (J/p^m0*J)_nu, q:J->Q is the natural projection and FQ,VQ are the reductions of F,V to Q.}
//    if not assigned isog`SemilinearOperatorsWType then
//        isog`SemilinearOperatorsWTypeArray:=AssociativeArray();
//    end if;
//    nu_Hash:=myHash(nu);
//    if not IsDefined(isog`SemilinearOperatorsWTypeArray,nu_Hash) then
//        p:=CharacteristicFiniteField(isog);
//        a:=Ilog(p,FiniteField(isog));
//        _,_,_,_,A,pi_A,OA,_,WR,sigma_OA_mod_I:=DieudonneAlgebraCommEndAlg(isog);
//
//        PP:=PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu);
//        // Need M such that P^M*J c p^(m0+1)J, locally at P, for each P in PP.
//        // By looking at the composition series, one deduces that any 
//        // M \geq Truncate(Log(Index(OA,P),Index(J,p^(m0+1)J)) will do.
//        size:=(p^(m0+1))^AbsoluteDimension(Algebra(OA)); // size = #J/p^(m0+1)J = (p^(m0+1))^dim_Q(A)
//        M:=Max( [ Truncate(Log(Index(OA,P),size)) : P in PP] );
//        //M1:=M+10; "WARNING: M is forced now from ",M,"to",M1; M:=M1; //for debugging
//        PP_M:=WR!!(&*PP)^M;
//        PP_M_J:=J*PP_M;
//
//        Qm0_1,qm0_1:=Quotient(J,p^(m0+1)*J+PP_M_J);
//        den_ideal:=p^m0*J+PP_M_J;
//        Qm0,qm0:=Quotient(J,den_ideal);
//        // these quotients are isomorphic to the nu-part of J/p^(m0+1)J and J/p^m0J
//
//        pr:=hom< Qm0_1->Qm0 | [ qm0(Qm0_1.i@@qm0_1) : i in [1..Ngens(Qm0_1)]] >;
//        assert IsSurjective(pr);
//        assert2 forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
//        
//        JOA:=OA!!J;
//        assert JOA subset OA;
//        m1:=m0+1+Valuation(Index(OA,JOA),p);
//        //m2:=m1+10; "WARNING: m1 is forced now from ",m1,"to",m2; m1:=m2; //for debugging
//        // We have the following inclusions, locally at p: p^m1*OA c p^(m0+1)*J c I c J c OA.
//        // This means the approximation of sigma on OA/p^m1*OA will give a well defined sigma on Q=J/I
//        QOA,qOA:=ResidueRing(OA,p^m1*OA);
//        sigma_QOA,powers_zz_diagonally_inOA_via_zbOE:=sigma_OA_mod_I(QOA,qOA,A);
//
//        alpha:=AlphaWTypeAtPlace(isog,nu,m1);
//
//        FQm0:=hom<Qm0->Qm0 | [ qm0(alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0)]]>;
//        FQm0_1:=hom<Qm0_1->Qm0_1 | [ qm0_1(alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0_1)]]>;
//        assert2 forall{ x : x in Generators(Qm0_1) | FQm0(pr(x)) eq pr(FQm0_1(x))};
//        // in the next assert2's, we check that FQm0^a and FQm0_1^a are equal to multiplication by pi_A
//        assert2 forall{ x : x in Generators(Qm0) | (FQm0^a)(x) eq qm0(pi_A*(x@@qm0))};
//        assert2 forall{ x : x in Generators(Qm0_1) | (FQm0_1^a)(x) eq qm0_1(pi_A*(x@@qm0_1))};
//
//        mp:=hom<Qm0_1->Qm0_1 | [ p*(Qm0_1.j) : j in [1..Ngens(Qm0_1)] ]>;
//        assert2 mp eq hom<Qm0_1->Qm0_1 | [ qm0_1(p*(Qm0_1.j)@@qm0_1) : j in [1..Ngens(Qm0_1)] ]>;
//        assert Image(mp) subset Image(FQm0_1);
//
//        z_gamma_s:=[];
//        for i in [1..Ngens(Qm0)] do
//            gamma:=Qm0.i;
//            x_gamma:=gamma@@pr;
//            z_gamma:=(mp(x_gamma))@@FQm0_1;
//            Append(~z_gamma_s,z_gamma);
//        end for;
//        VQm0:=hom<Qm0->Qm0 | [ pr(z_gamma_s[i]) : i in [1..Ngens(Qm0)] ] >;
//        assert2 forall{ g : g in Generators(Qm0) | FQm0(VQm0(g)) eq p*g };
//        assert2 forall{ g : g in Generators(Qm0) | VQm0(FQm0(g)) eq p*g };
//
//        // We check semilinearity for F, V: F*x = sigma(x)*F and x*V=V*sigma(x)  forall x in L?
//        // It suffices to check if for powers of zz in OA.
//        if GetAssertions() ge 2 then
//            vprintf Algorithm_3,2 : "\tTesting semilinearity of F and V...";
//            for z in powers_zz_diagonally_inOA_via_zbOE do
//                sigma_z:=z@qOA@sigma_QOA@@qOA;
//                z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
//                sigma_z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(sigma_z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
//                assert2 forall{i:i in [1..Ngens(Qm0)]| FQm0(z_action_Qm0(Qm0.i)) eq sigma_z_action_Qm0(FQm0(Qm0.i))};
//                assert2 forall{i:i in [1..Ngens(Qm0)]| z_action_Qm0(VQm0(Qm0.i)) eq VQm0(sigma_z_action_Qm0(Qm0.i))};
//            end for;
//            vprintf Algorithm_3,2 : "all good.\n";
//        end if;
//        isog`SemilinearOperatorsWTypeArray[nu_Hash]:=<Qm0,qm0,FQm0,VQm0,PP_M,m0,J,M>;
//    end if;
//    Qm0,qm0,FQm0,VQm0,PP_M,m0,J,M:=Explode(isog`SemilinearOperatorsWTypeArray[nu_Hash]);
//    return Qm0,qm0,FQm0,VQm0,PP_M,m0,J,M;
//end intrinsic;
//
//intrinsic SemilinearOperatorsWType(isog::IsogenyClassFq,J::AlgEtQIdl,nus::SeqEnum[AlgEtQIdl],m0::RngIntElt)->GrpAb,Map,Map,Map
//{Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of W-type, a sequence of places nus of the DeligneAlgebra and a precision m0, returns Q,q,FQ,VQ where Q is isomorphic to direct sum of (J/p^m0*J)_nu for nu in nus, q:J->Q is the natural projection and FQ,VQ are the reductions of F,V to Q.}
//    if not assigned isog`SemilinearOperatorsWType then
//        p:=CharacteristicFiniteField(isog);
//        Qs:=[];
//        qs:=<>;
//        Fs:=<>;
//        Vs:=<>;
//        PP_Ms:=[];
//        for nu in nus do
//            Q,q,F,V,PP_M,_,_,M:=SemilinearOperatorsWTypeAtPlace(isog,J,nu,m0);
//            Append(~Qs,Q);
//            Append(~qs,q);
//            Append(~Fs,F);
//            Append(~Vs,V);
//            Append(~PP_Ms,PP_M);
//        end for;
//        den_ideal:=p^m0*J+(&*PP_Ms)*J;
//        // with DIRECT SUM
//        //Qm0,embs,projs:=DirectSum(Qs);
//        //qm0:=map<Algebra(J)->Qm0|x:->&+[x@qs[i]@embs[i]:i in [1..#nus]]>; //preimages would require an annoying CRT
//        //FQm0:=hom<Qm0->Qm0|[&+[Qm0.j@projs[i]@Fs[i]@embs[i]: i in [1..#nus]]: j in [1..Ngens(Qm0)]]>;
//        //VQm0:=hom<Qm0->Qm0|[&+[Qm0.j@projs[i]@Vs[i]@embs[i]: i in [1..#nus]]: j in [1..Ngens(Qm0)]]>;
//        //assert Index(J,den_ideal) eq #Qm0;
//        //assert2 forall{z:z in ZBasis(den_ideal)|qm0(z) eq Zero(Qm0)};
//        // end DIRECT SUM; with CRT
//        _,_,_,_,A,pi_A,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
//        J_toJs,Js_toJ:=ChineseRemainderTheoremFunctions(J,[(WR!!(p^m0*OA))+PP_M : PP_M in PP_Ms]);
//        Qm0,qm0:=Quotient(J,den_ideal);
//        FQm0:=hom<Qm0->Qm0|[<((Qm0.j@@qm0@J_toJs)[i])@qs[i]@Fs[i]@@qs[i]:i in [1..#nus]>@Js_toJ@qm0:j in [1..Ngens(Qm0)]]>;
//        VQm0:=hom<Qm0->Qm0|[<((Qm0.j@@qm0@J_toJs)[i])@qs[i]@Vs[i]@@qs[i]:i in [1..#nus]>@Js_toJ@qm0:j in [1..Ngens(Qm0)]]>;
//        // end CRT
//        if GetAssertions() ge 2 then
//            a:=Ilog(p,FiniteField(isog));
//            assert2 forall{ x : x in Generators(Qm0) | (FQm0^a)(x) eq qm0(pi_A*(x@@qm0))}; //need preimage
//            assert2 forall{ g : g in Generators(Qm0) | FQm0(VQm0(g)) eq p*g };
//            assert2 forall{ g : g in Generators(Qm0) | VQm0(FQm0(g)) eq p*g };
//        end if;
//        isog`SemilinearOperatorsWType:=<Qm0,qm0,FQm0,VQm0,den_ideal,m0,J>;
//    end if;
//    Qm0,qm0,FQm0,VQm0:=Explode(isog`SemilinearOperatorsWType);
//    return Qm0,qm0,FQm0,VQm0;
//end intrinsic;

intrinsic SemilinearOperatorsWType(isog::IsogenyClassFq,J::AlgEtQIdl,m0::RngIntElt,slopes::MonStgElt)->GrpAb,Map,Map,Map
{Given an isogeny class isog, an ideal J over the maximal order of the DieudonneAlgebra which is F-V-stable for F,V of W-type, and a precision m0, returns Q,q,FQ,VQ where Q is isomorphic to direct sum of (J/p^m0*J)_nu for nu of slope in (0,1) or any --depending whether the argument slope is "(0,1)" or "all"-- q:J->Q is the natural projection and FQ,VQ are the reductions of F,V to Q.}
    if not assigned isog`SemilinearOperatorsWType then
        p:=CharacteristicFiniteField(isog);
        a:=Ilog(p,FiniteField(isog));
        _,_,_,_,A,pi_A,OA,_,WR,sigma_OA_mod_I:=DieudonneAlgebraCommEndAlg(isog);

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

        // Need M such that P^M*J c p^(m0+1)J, locally at P, for each P in PP.
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
        assert2 forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
        
        JOA:=OA!!J;
        assert JOA subset OA;
        m1:=m0+1+Valuation(Index(OA,JOA),p);
        //m2:=m1+10; "WARNING: m1 is forced now from ",m1,"to",m2; m1:=m2; //for debugging
        // We have the following inclusions, locally at p: p^m1*OA c p^(m0+1)*J c I c J c OA.
        // This means the approximation of sigma on OA/p^m1*OA will give a well defined sigma on Q=J/I
        QOA,qOA:=ResidueRing(OA,p^m1*OA);
        sigma_QOA,powers_zz_diagonally_inOA_via_zbOE:=sigma_OA_mod_I(QOA,qOA,A);

        PPs:=[];
        alpha_s:=[];
        for nu in nus do
            alpha_nu,PPs_nu:=AlphaWTypeAtPlace(isog,nu,m1);
            Append(~PPs,PPs_nu);
            Append(~alpha_s,alpha_nu);
        end for;
        alpha:=CRT(PPs,alpha_s);

        FQm0:=hom<Qm0->Qm0 | [ qm0(alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0)]]>;
        FQm0_1:=hom<Qm0_1->Qm0_1 | [ qm0_1(alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0_1)]]>;
        assert2 forall{ x : x in Generators(Qm0_1) | FQm0(pr(x)) eq pr(FQm0_1(x))};
        // in the next assert2's, we check that FQm0^a and FQm0_1^a are equal to multiplication by pi_A
        assert2 forall{ x : x in Generators(Qm0) | (FQm0^a)(x) eq qm0(pi_A*(x@@qm0))};
        assert2 forall{ x : x in Generators(Qm0_1) | (FQm0_1^a)(x) eq qm0_1(pi_A*(x@@qm0_1))};

        mp:=hom<Qm0_1->Qm0_1 | [ p*(Qm0_1.j) : j in [1..Ngens(Qm0_1)] ]>;
        assert2 mp eq hom<Qm0_1->Qm0_1 | [ qm0_1(p*(Qm0_1.j)@@qm0_1) : j in [1..Ngens(Qm0_1)] ]>;
        assert Image(mp) subset Image(FQm0_1);

        z_gamma_s:=[];
        for i in [1..Ngens(Qm0)] do
            gamma:=Qm0.i;
            x_gamma:=gamma@@pr;
            z_gamma:=(mp(x_gamma))@@FQm0_1;
            Append(~z_gamma_s,z_gamma);
        end for;
        VQm0:=hom<Qm0->Qm0 | [ pr(z_gamma_s[i]) : i in [1..Ngens(Qm0)] ] >;
        assert2 forall{ g : g in Generators(Qm0) | FQm0(VQm0(g)) eq p*g };
        assert2 forall{ g : g in Generators(Qm0) | VQm0(FQm0(g)) eq p*g };

        // We check semilinearity for F, V: F*x = sigma(x)*F and x*V=V*sigma(x)  forall x in L?
        // It suffices to check if for powers of zz in OA.
        if GetAssertions() ge 2 then
            vprintf Algorithm_3,2 : "\tTesting semilinearity of F and V...";
            for z in powers_zz_diagonally_inOA_via_zbOE do
                sigma_z:=z@qOA@sigma_QOA@@qOA;
                z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
                sigma_z_action_Qm0:=hom<Qm0->Qm0 | [ qm0(sigma_z*(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
                assert2 forall{i:i in [1..Ngens(Qm0)]|FQm0(z_action_Qm0(Qm0.i)) eq sigma_z_action_Qm0(FQm0(Qm0.i))};
                assert2 forall{i:i in [1..Ngens(Qm0)]|z_action_Qm0(VQm0(Qm0.i)) eq VQm0(sigma_z_action_Qm0(Qm0.i))};
            end for;
            vprintf Algorithm_3,2 : "all good.\n";
        end if;
        isog`SemilinearOperatorsWType:=<Qm0,qm0,FQm0,VQm0,den_ideal,m0,J,slopes>;
    end if;
    Qm0,qm0,FQm0,VQm0:=Explode(isog`SemilinearOperatorsWType);
    return Qm0,qm0,FQm0,VQm0;
end intrinsic;

// OLD VERSION
//intrinsic SemilinearOperators(isog::IsogenyClassFq)->RngIntElt,AlgEtQIdl,AlgEtQIdl,GrpAb,Map,Map,Map
//{Returns the homonymous attribute of the isogeny class, which consists of the following informations: m0,J,den_ideal,Qm0,qm0,FQm0,VQm0, where (see DieudonneAlgebraCommEndAlg for the missing definitions):
//- m0 is a positive integer;
//- J is a WR-ideal with maximal endomorphism ring OA which is stable under the action of F and V=pF^-1, for some semilinear operator F with the Frobenius property of and of W-type;
//- den_ideal = p^m0*J+P01^M*J, where P01 is the product of the maximal ideals of WR which are above the unique local-local maximal ideal of R, and M is chosen so that P01^MJ c J locally at every such maximal ideal;
//- Qm0 is the abelian group J/den_ideal and qm0 is the quotient map J->Qm0;
//- FQm0 and Vm0 are additive maps induced by semilinear operators F and V as above. They represent the Frobenius and Verschiebung acting on Dieudonné modules.
//The attribute SemilinearOperators needs to be computed beforehand, during a run of IsomorphismClassesDieudonneModulesCommEndAlg. During this run, the integer m0 is automatically computed by the program to guarantee that every fractional W'R-ideal I' whose extension to OA is F and V stable such that I' c J and den_ideal c I'. These two conditions allow us to verify if I' is a W'R\{F,V\} ideal, that is, (the local-local-part) of a Dieudonne module of some abelian variety in isog.}
//    //TODO: in the future it would be nice to be able to increase the precision with a call of this intrinsic.
//    // This would require to choose a new alpha (as in alpha_at_precision) 'compatible' with the current choice.
//    // I might be a bit complicated to code, and it is outside of the current scope.
//    require assigned isog`SemilinearOperators : "Run first IsomorphismClassesDieudonneModules(isog)";
//    return Explode(isog`SemilinearOperators);
//end intrinsic;


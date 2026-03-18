/* vim: set syntax=magma : */

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

declare attributes IsogenyClassFq : alpha,
                                    delta_Hilbert90,
                                    SemilinearOperators;

declare attributes AlgEtQIdl :      finite_quotients;

intrinsic _AlphaAtPrecision(isog::IsogenyClassFq, m::RngIntElt : DualsCompatible:=false)->AlgEtQElt
{Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi], and m a non-negative integer. The intrinsic returns an approximation of an element alpha in the DieudonneAlgebra A of W-type, that is, the completion alpha_nu at a place nu of E of slope in (0,1) is of the form (1,...,1,u_nu) for u_nu satisfying N_(LE_nu/E_nu)(u_nu)=pi_nu. This is using the identification A_nu = oplus LE_nu. The output is guaranteed to be correct at precision m, meaning that the images of the approximation and of alpha coincide in OA/prod_nu prod_PP PP^(e_nu*m) where the double product is taken over all places nu of E of slope in (0,1) and PP runs over the primes of A above nu.
If the VarArg DualsCompatible is true (default false), then the attribute delta_Hilbert90 of isog is assigned with an approximation at precision m of an element delta satisfying p/alpha=delta/sigma(delta)*bar(alpha), where bar is the involution induced on A by the CM-involution of E.
// FIXME update this description
}
    require m ge 0: "m needs to be a non-negative integer";
    if not assigned isog`alpha then
        // DEBUG forcibly increase the precision
        // m+:=50;

        require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
        _,_,_,_,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,_,primes_of_A_above_place_of_E,_,_,bar_onA:=DieudonneAlgebraCommEndAlg(isog);
        q:=FiniteField(isog);
        _,p,a:=IsPrimePower(q);
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        plE_sl_0,plE_sl_in01,plE_sl_1:=PlacesOfQFAbove_p(isog);

        finite_quotients:=function(m,nu)
        // input:  - nu = a place of E
        //         - m = a positive integer
        // output: PPs_nu_m,PPs_nu_m_prod,Rs_nu,rs_nu,Q,pr,Us_nu,us_nu,U,U_pr
            if not assigned nu`finite_quotients then
                nu`finite_quotients:=AssociativeArray();
            end if;
            if not IsDefined(nu`finite_quotients,m) then
                PPs_nu:=primes_of_A_above_place_of_E(A,nu);
                f_nu:=InertiaDegree(nu);
                g_nu:=GCD(a,f_nu); //q=p^a
                assert #PPs_nu eq g_nu;
                Rs_nu:=[];
                rs_nu:=<>;
                Us_nu:=[];
                us_nu:=<>;
                PPs_nu_m:=[];
                e_nu:=RamificationIndex(PPs_nu[1]);
                for PP in PPs_nu do
                    assert RamificationIndex(PP) eq e_nu; // PPs is a single sigma-orbit
                    PP_m:=PP^(e_nu*(m));
                    Append(~PPs_nu_m,PP_m);
                    R,r:=ResidueRing(OA,PP_m);
                    vprintf alpha_at_precision,2 : "\n\tR,r computed\n";
                    U,u:=ResidueRingUnits(OA,PP_m);
                    vprintf alpha_at_precision,2 : "\tU,u computed\n";
                    Append(~Rs_nu,R);
                    Append(~rs_nu,r);
                    Append(~Us_nu,U);
                    Append(~us_nu,u);
                end for;
                PPs_nu_m_prod:=&*PPs_nu_m;

                Q,embs,projs:=DirectSum(Rs_nu);
                pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                           y:->CRT( PPs_nu_m ,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
                pi_Q:=pr(pi_A);
                assert2 forall{ x : x in Generators(Q) | pr(x@@pr) eq x};

                U,U_embs,U_projs:=DirectSum(Us_nu);
                U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                             y:->CRT( PPs_nu_m ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
                assert2 forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};
                vprintf alpha_at_precision,2 : "\tQ and U are computed\n";
                nu`finite_quotients[m]:=<PPs_nu_m,PPs_nu_m_prod,Rs_nu,rs_nu,Q,embs,projs,pr,Us_nu,us_nu,U,U_embs,U_projs,U_pr>;
            end if;
            return Explode(nu`finite_quotients[m]);
        end function;

        alpha_at_precision_W_type_at_place:=function(m,nu,g_nu,sigma,t_nu,qI)
        // input:  - nu is a place of E;
        //         - m is a positive integer 
        //         - t_nu is an element of E, which is a uniformizer at nu and a unit at every other place above p;
        //         - sigma is computed on qI:OA->OA/p^m'*OA, for some m' \geq m.
        // output: - an element alpha_nu of W-type computed at precision m, that is,
        //           in OA/PP where PP:=\prod P^(m*e) where P runs over the places of A
        //           above nu and e_nu is the ramification at nu (=ramification at each P)
        //         - PP is also returned.
            PPs_nu_m,PPs_nu_m_prod,Rs_nu,rs_nu,Q,embs,projs,pr,Us_nu,us_nu,U,U_embs,U_projs,U_pr:=finite_quotients(m,nu);
            sigma_U:=hom<U->U | [U.i@@U_pr@qI@sigma@@qI@U_pr : i in [1..Ngens(U)]]>; 
            image_phi:=function(gamma)
                // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^(e_nu*m))^*
                // phi does the following two steps
                // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_nu,i^(m)
                // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
                beta:=&*[i lt g_nu select U_embs[i]((One(A))@@us_nu[i]) else U_embs[i](gamma):i in [1..g_nu]];
                // Action of the Frobenius on U
                img:=(&*[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
                vprintf alpha_at_precision,2 : "\timg = %o\n\tsigma(img) = %o\n",img,sigma_U(img);
                assert2 sigma_U(img) eq img;
                return img;
            end function;
            phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
            val_nu:=Valuation(pi,nu); // in E
            pE:=PlacesAboveRationalPrime(E,p);
            // w_nu is in OE and congrunent to t_nu^val_nu/pi at nu and 1 at every other place above p
            // The precision is chosen to be a majorative of RamificationIndex(pp)*m [to match the quotient we are using]
            // plus Valuation(PP,pi) leq Valuation(PP,q)=RamificationIndex(pp)*a.
            w_nu:=CRT([pp^(Dimension(E)*(m+a)):pp in pE],[pp eq nu select t_nu^val_nu else pi : pp in pE])/pi; // in OE
            wU:=-U_pr(Delta_map(w_nu)); // in E->A->U
            gamma0:=wU@@phi; // in Us[g_nu], the last componenet of U
            gamma_A:=(&+[i lt g_nu select 
                                    U_embs[i](One(A)@@us_nu[i]) else 
                                    U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
            u0:=Delta_map(t_nu^(Integers()!(val_nu*g_nu/a)));
            beta_A:=(&+[i lt g_nu select 
                                    embs[i](rs_nu[i](One(A))) else 
                                    embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; // in A 
            alpha_nu:=gamma_A*beta_A; // in A
            
            // it is desirable that alpha_nu is not a zero divisor of A
            while IsZeroDivisor(alpha_nu) do
                alpha_nu+:=Random(PPs_nu_m_prod);
            end while;
            // Check that alpha_nu of W-type: 1 in all components but the last one, and with sigma-norm = pi_nu
            assert2 forall{i:i in [1..g_nu-1]|alpha_nu-1 in PPs_nu_m[i]}; 
            assert2 forall{i:i in [1..g_nu]|X - pi_A in PPs_nu_m[i]} where X:=&*[alpha_nu@qI@(sigma^i)@@qI:i in [0..a-1]];
            return alpha_nu,PPs_nu_m_prod;
        end function;

        alpha_W_type_q_alpha_at_precision_at_place:=function(m,m2,nu,g_nu,sigma,t_nu,qI)
        // input: - m2 \geq m integers giving the precision
        //        - nu is a place of E, 
        //        - t_nu a 'good' uniformizer at nu 
        //        - sigma is computed on qI:OA->OA/p^m2*OA.
        // output: - an element alpha_nu of W-type computed at precision m2;
        //         - the element representing q/alpha_nu at precision m; 
        //         - \prod P^(m*e) where P runs over the places of A above nu 
        //              and e is the ramification at nu (=ramification at P).
            PPs_nu:=primes_of_A_above_place_of_E(A,nu);
            assert #PPs_nu eq g_nu;

            Rs_nu:=[];
            rs_nu:=<>;
            Us_nu:=[];
            us_nu:=<>;
            PPs_nu_m:=[];
            PPs_nu_m2:=[];
            for PP in PPs_nu do
                PP_e:=PP^RamificationIndex(PP);
                PP_m:=PP_e^m;
                Append(~PPs_nu_m,PP_m);
                PP_m2:=PP_e^m2;
                Append(~PPs_nu_m2,PP_m2);
                R,r:=ResidueRing(OA,PP_m2);
                vprintf alpha_at_precision,2 : "\n\tR,r computed\n";
                U,u:=ResidueRingUnits(OA,PP_m2);
                vprintf alpha_at_precision,2 : "\tU,u computed\n";
                Append(~Rs_nu,R);
                Append(~rs_nu,r);
                Append(~Us_nu,U);
                Append(~us_nu,u);
            end for;
            PPs_nu_m2_prod:=&*PPs_nu_m2;
            PPs_nu_m_prod:=&*PPs_nu_m;

            Q,embs,projs:=DirectSum(Rs_nu);
            pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                       y:->CRT( PPs_nu_m2 ,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
            pi_Q:=pr(pi_A);
            assert2 forall{ x : x in Generators(Q) | pr(x@@pr) eq x};

            U,U_embs,U_projs:=DirectSum(Us_nu);
            U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                         y:->CRT( PPs_nu_m2 ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
            sigma_U:=hom<U->U | [U.i@@U_pr@qI@sigma@@qI@U_pr : i in [1..Ngens(U)]]>; 
            assert2 forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};

            vprintf alpha_at_precision,2 : "\tQ and U are computed\n";

            image_phi:=function(gamma)
                // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^(m))^*
                // phi does the following two steps
                // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_nu,i^(m)
                // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
                beta:=&*[i lt g_nu select U_embs[i]((One(A))@@us_nu[i]) else U_embs[i](gamma):i in [1..g_nu]];
                // Action of the Frobenius on U
                img:=(&*[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
                vprintf alpha_at_precision,2 : "\timg = %o\n\tsigma(img) = %o\n",img,sigma_U(img);
                assert2 sigma_U(img) eq img;
                return img;
            end function;
            phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
            
            val_nu:=Valuation(pi,nu); // in E
            w_nu:=pi/(t_nu^val_nu); // in E
            assert Valuation(w_nu,nu) eq 0;
            wU:=U_pr(Delta_map(w_nu)); // in E->A->U
            gamma0:=wU@@phi; // in Us[g_nu], the last componenet of U
            gamma_A:=(&+[i lt g_nu select 
                                    U_embs[i](One(A)@@us_nu[i]) else 
                                    U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A

            u0:=Delta_map(t_nu^(Integers()!(val_nu*g_nu/a)));
            mult:=hom<RR->RR|[((RR.i@@r)*u0)@r : i in [1..Ngens(RR)]]> where RR:=Rs_nu[g_nu] where r:=rs_nu[g_nu];
            q_u0:=(rs_nu[g_nu](A!q))@@mult;
            beta_A:=(&+[i lt g_nu select 
                                    embs[i](rs_nu[i](One(A))) else 
                                    embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; // in A 
            alpha_nu:=gamma_A*beta_A; // in OA, at precision m2
            // now we want to construct q/alpha_nu, which is also in OA, at precision m2:
            // - change the sign of gamma0, and
            // - q_beta_A = (q,...,q,q/u0)
            q_gamma_A:=(&+[i lt g_nu select 
                                    U_embs[i](One(A)@@us_nu[i]) else 
                                    -U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
            q_beta_A:=(&+[i lt g_nu select 
                                    embs[i](rs_nu[i](A!q)) else 
                                    embs[i](q_u0) : i in [1..g_nu]])@@pr; // in A 
            q_alpha_nu:=q_gamma_A*q_beta_A; // in OA, at precision m2
            assert alpha_nu*q_alpha_nu - q in PPs_nu_m_prod;
            return alpha_nu,q_alpha_nu,PPs_nu_m_prod;
        end function;

        output:=AssociativeArray();
        places_considered:=plE_sl_in01;
        uniformizers_at_nus:=Uniformizers(plE_sl_in01 cat plE_sl_0 cat plE_sl_1)[1..#places_considered];
        if not DualsCompatible then
            I:=p^m*OA;
            QI,qI:=ResidueRing(OA,I);
            sigma:=sigma_OA_mod_I(QI,qI,A);
            alphas:=[];
            prime_powers:=[];
            // Considering the action of COMPLEX CONJUGATION on the places above p could speed-up the computation here,
            // by deducing alpha_{nu_bar} from alpha_{nu} whenever nu\neq nu_bar.
            // Note that this consideration does not help with the places stabilized by the action of bar{}.
            for inu->nu in places_considered do
                vprintf alpha_at_precision,1 : "Computing alpha_Q for %oth place of %o...",inu,#places_considered;
                g_nu:=GCD(a,InertiaDegree(nu));
                alpha_nu,PPs_nu_m:=alpha_at_precision_W_type_at_place(m,nu,g_nu,sigma,uniformizers_at_nus[inu],qI);
                output[nu]:=<alpha_nu,PPs_nu_m>;
                vprintf alpha_at_precision,1 : "done\n";
            end for;
        else // with DualsCompatible
            if exists{nu:nu in plE_sl_in01|IsConjugateStable(nu)} then
                error "Currently this is implemented only for places which are NOT stable by complex conjugation";
            end if;
            // We identify the conjugate pairs in places_considered.
            conj_pairs_indices:=[];
            conj_stable_indices:=[];
            to_do:={ 1..#places_considered };
            repeat
                ExtractRep(~to_do,~i);
                nu:=places_considered[i];
                test,nu_bar:=IsConjugateStable(nu);
                if test then
                    Append(~conj_stable_indices,i);
                else
                    i_bar:=Index(places_considered,nu_bar);
                    assert i_bar ne 0;
                    Exclude(~to_do,i_bar);
                    Append(~conj_pairs_indices,<i,i_bar>);
                end if;
            until #to_do eq 0;
            delete to_do;
            // We determine the precision m2 at which delta needs, and consequently,
            // also alpha, needs to be computed. m2 needs to satisfy the inclusion:
            //    p^(m2-g_nu+1) in (W_{R,nu}:OA_nu)=:ff_nu
            // We can take m2=Max_nu(g_nu-1+val_P(ff) where P is any max ideal of OA above nu).
            ff_WR:=OA!!Conductor(WR);
            m2:=m+a-1;
            I:=p^m2*OA;
            QI,qI:=ResidueRing(OA,I);
            sigma_m2:=sigma_OA_mod_I(QI,qI,A);
            for inu in conj_stable_indices do
                vprintf alpha_at_precision,1 : "Computing alpha at precision %o for the %o-th place",m,inu;
                // FIXME need to figure out what to do here
                vprintf alpha_at_precision,1 : "done\n";
            end for;
            for pair in conj_pairs_indices do
                inu,inu_bar:=Explode(pair);
                if not IsOfWType(places_considered[inu]) then
                    assert IsOfWType(places_considered[inu_bar]);
                    temp:=inu; inu:=inu_bar; inu_bar:=temp;
                    unif:=uniformizers_at_nus[inu_bar];
                else
                    unif:=uniformizers_at_nus[inu];
                end if;
                nu:=places_considered[inu];
                nu_bar:=places_considered[inu_bar];
                g_nu:=GCD(a,InertiaDegree(nu));
                vprintf alpha_at_precision,1 : "Computing alpha_Q for the conjugate pair of places <%o,%o>e of %o ...",
                                                inu,inu_bar,#places_considered;
                alpha_nu,q_alpha_nu,PP_nu_m:=alpha_W_type_q_alpha_at_precision_at_place(m,m2,nu,g_nu,sigma_m2,unif,qI);
                alpha_nu_bar:=bar_onA(q_alpha_nu)/p^(a-1); // this element is in p^-(a-1)*O_A
                PP_nu_bar_m:=ComplexConjugate(PP_nu_m);
                output[nu]:=<alpha_nu,PP_nu_m>;
                output[nu_bar]:=<alpha_nu_bar,PP_nu_bar_m>;
                vprintf alpha_at_precision,1 : "done\n";
                vprintf alpha_at_precision,1 : "done\n";
            end for;
        end if;
        isog`alpha:=output;
    end if;
    return isog`alpha;
end intrinsic;

intrinsic _AlphaAtPrecision_delta(isog::IsogenyClassFq, m::RngIntElt : DualsCompatible:=false)->AlgEtQElt
{Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi], and m a non-negative integer. The intrinsic returns an approximation of an element alpha in the DieudonneAlgebra A of W-type, that is, the completion alpha_nu at a place nu of E of slope in (0,1) is of the form (1,...,1,u_nu) for u_nu satisfying N_(LE_nu/E_nu)(u_nu)=pi_nu. This is using the identification A_nu = oplus LE_nu. The output is guaranteed to be correct at precision m, meaning that the images of the approximation and of alpha coincide in OA/prod_nu prod_PP PP^(e_nu*m) where the double product is taken over all places nu of E of slope in (0,1) and PP runs over the primes of A above nu.
If the VarArg DualsCompatible is true (default false), then the attribute delta_Hilbert90 of isog is assigned with an approximation at precision m of an element delta satisfying p/alpha=delta/sigma(delta)*bar(alpha), where bar is the involution induced on A by the CM-involution of E.}
    require m ge 0: "m needs to be a non-negative integer";
    if not assigned isog`alpha then
        // DEBUG forcibly increase the precision
        // m+:=50;

        require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
        _,_,_,_,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,_,primes_of_A_above_place_of_E,_,_,bar_onA:=DieudonneAlgebraCommEndAlg(isog);
        q:=FiniteField(isog);
        _,p,a:=IsPrimePower(q);
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        plE_sl_0,plE_sl_in01,plE_sl_1:=PlacesOfQFAbove_p(isog);

        finite_quotients:=function(m,nu)
        // input:  - nu = a place of E
        //         - m = a positive integer
        // output: PPs_nu_m,PPs_nu_m_prod,Rs_nu,rs_nu,Q,pr,Us_nu,us_nu,U,U_pr
            if not assigned nu`finite_quotients then
                nu`finite_quotients:=AssociativeArray();
            end if;
            if not IsDefined(nu`finite_quotients,m) then
                PPs_nu:=primes_of_A_above_place_of_E(A,nu);
                f_nu:=InertiaDegree(nu);
                g_nu:=GCD(a,f_nu); //q=p^a
                assert #PPs_nu eq g_nu;
                Rs_nu:=[];
                rs_nu:=<>;
                Us_nu:=[];
                us_nu:=<>;
                PPs_nu_m:=[];
                e_nu:=RamificationIndex(PPs_nu[1]);
                for PP in PPs_nu do
                    assert RamificationIndex(PP) eq e_nu; // PPs is a single sigma-orbit
                    PP_m:=PP^(e_nu*(m));
                    Append(~PPs_nu_m,PP_m);
                    R,r:=ResidueRing(OA,PP_m);
                    vprintf alpha_at_precision,2 : "\n\tR,r computed\n";
                    U,u:=ResidueRingUnits(OA,PP_m);
                    vprintf alpha_at_precision,2 : "\tU,u computed\n";
                    Append(~Rs_nu,R);
                    Append(~rs_nu,r);
                    Append(~Us_nu,U);
                    Append(~us_nu,u);
                end for;
                PPs_nu_m_prod:=&*PPs_nu_m;

                Q,embs,projs:=DirectSum(Rs_nu);
                pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                           y:->CRT( PPs_nu_m ,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
                pi_Q:=pr(pi_A);
                assert2 forall{ x : x in Generators(Q) | pr(x@@pr) eq x};

                U,U_embs,U_projs:=DirectSum(Us_nu);
                U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                             y:->CRT( PPs_nu_m ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
                assert2 forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};
                vprintf alpha_at_precision,2 : "\tQ and U are computed\n";
                nu`finite_quotients[m]:=<PPs_nu_m,PPs_nu_m_prod,Rs_nu,rs_nu,Q,embs,projs,pr,Us_nu,us_nu,U,U_embs,U_projs,U_pr>;
            end if;
            return Explode(nu`finite_quotients[m]);
        end function;

        alpha_at_precision_W_type_at_place:=function(m,nu,g_nu,sigma,t_nu,qI)
        // input:  - nu is a place of E;
        //         - m is a positive integer 
        //         - t_nu is an element of E, which is a uniformizer at nu and a unit at every other place above p;
        //         - sigma is computed on qI:OA->OA/p^m'*OA, for some m' \geq m.
        // output: - an element alpha_nu of W-type computed at precision m, that is,
        //           in OA/PP where PP:=\prod P^(m*e) where P runs over the places of A
        //           above nu and e_nu is the ramification at nu (=ramification at each P)
        //         - PP is also returned.
            PPs_nu_m,PPs_nu_m_prod,Rs_nu,rs_nu,Q,embs,projs,pr,Us_nu,us_nu,U,U_embs,U_projs,U_pr:=finite_quotients(m,nu);
            sigma_U:=hom<U->U | [U.i@@U_pr@qI@sigma@@qI@U_pr : i in [1..Ngens(U)]]>; 
            image_phi:=function(gamma)
                // gamma in US_nu[gnu] = (OA/PP_{nu,gnu}^(e_nu*m))^*
                // phi does the following two steps
                // 1) gamma :-> beta = (1,...,1,gamma) in U = \prod_i US_nu[i] = OA/\prod_i PP_nu,i^(m)
                // 2) beta :-> beta*beta^sigma_Q*...*beta^(sigma_Q^(a-1)) in U
                beta:=&*[i lt g_nu select U_embs[i]((One(A))@@us_nu[i]) else U_embs[i](gamma):i in [1..g_nu]];
                // Action of the Frobenius on U
                img:=(&*[ i eq 1 select beta else sigma_U(Self(i-1)) : i in [1..a] ]); //in U
                vprintf alpha_at_precision,2 : "\timg = %o\n\tsigma(img) = %o\n",img,sigma_U(img);
                assert2 sigma_U(img) eq img;
                return img;
            end function;
            phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
            val_nu:=Valuation(pi,nu); // in E
            pE:=PlacesAboveRationalPrime(E,p);
            // w_nu is in OE and congrunent to t_nu^val_nu/pi at nu and 1 at every other place above p
            // The precision is chosen to be a majorative of RamificationIndex(pp)*m [to match the quotient we are using]
            // plus Valuation(PP,pi) leq Valuation(PP,q)=RamificationIndex(pp)*a.
            w_nu:=CRT([pp^(Dimension(E)*(m+a)):pp in pE],[pp eq nu select t_nu^val_nu else pi : pp in pE])/pi; // in OE
            wU:=-U_pr(Delta_map(w_nu)); // in E->A->U
            gamma0:=wU@@phi; // in Us[g_nu], the last componenet of U
            gamma_A:=(&+[i lt g_nu select 
                                    U_embs[i](One(A)@@us_nu[i]) else 
                                    U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
            u0:=Delta_map(t_nu^(Integers()!(val_nu*g_nu/a)));
            beta_A:=(&+[i lt g_nu select 
                                    embs[i](rs_nu[i](One(A))) else 
                                    embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; // in A 
            alpha_nu:=gamma_A*beta_A; // in A
            
            // it is desirable that alpha_nu is not a zero divisor of A
            while IsZeroDivisor(alpha_nu) do
                alpha_nu+:=Random(PPs_nu_m_prod);
            end while;
            // Check that alpha_nu of W-type: 1 in all components but the last one, and with sigma-norm = pi_nu
            assert2 forall{i:i in [1..g_nu-1]|alpha_nu-1 in PPs_nu_m[i]}; 
            assert2 forall{i:i in [1..g_nu]|X - pi_A in PPs_nu_m[i]} where X:=&*[alpha_nu@qI@(sigma^i)@@qI:i in [0..a-1]];
            return alpha_nu,PPs_nu_m_prod;
        end function;

        delta_nu_at_precision_conj_stable:=function(m,nu,g_nu,alpha_nu,sigma,qI)
        // input:  - m is a positive integer
        //         - nu is a place of E which is conjugate stable;
        //         - g_nu is the number of primes of A above nu;
        //         - alpha_nu is an element of W-type for pi_nu, computed at precision at least m+g_nu.
        //         - sigma is computed on qI:OA->OA/p^m'*OA, for some m' \geq m.
        // output: - an element delta_nu satisfying delta_nu/sigma(delta_nu)*bar(alpha_nu) = p/alpha_nu  
        //           computed at precision m, that is, in OA/PP where PP:=\prod P^(m*e) where 
        //           P runs over the places of A above nu and e_nu is the ramification at nu (=ramification at each P)
        //         - PP is also returned.
            pg_nu:=A!(p^g_nu);
            a_div_g_nu:=Integers()!(a/g_nu);
            U:=&*[alpha_nu@qI@(sigma^i)@@qI:i in [0..g_nu-1]]; // = (u_nu,...,u_nu) in A
            bU:=bar_onA(U);
            pA:=PlacesAboveRationalPrime(A,p);
            UbU:=U*bU;
            // The precision is chosen to match the one of the quotients we are using, plus the fact that we are dividing 
            // by p^g_nu
            UU:=CRT([PP^(Dimension(A)*(m+g_nu)):PP in pA],[PP in primes_of_A_above_place_of_E(A,nu) select UbU else pg_nu:PP in pA])/pg_nu;
            assert U in OA;
            assert bU in OA;
            assert UU in OA;
            assert Valuation(UU,P) eq 0 where P:=primes_of_A_above_place_of_E(A,nu)[g_nu];
            PPs_nu_m:=[PP^(RamificationIndex(PP)*m):PP in primes_of_A_above_place_of_E(A,nu)];
            PPs_nu_m_prod:=&*(PPs_nu_m);
            assert2 forall{k:k in [1..g_nu]|&*[ bU@qI@(sigma^(g_nu*i))@@qI : i in [0..a_div_g_nu-1] ] - (q/pi_A) in PPs_nu_m[k]};
            assert2 forall{k:k in [1..g_nu]|&*[ U@qI@(sigma^(g_nu*i))@@qI : i in [0..a_div_g_nu-1] ] - pi_A in PPs_nu_m[k]};
            assert2 forall{k:k in [1..g_nu]|&*[UU@qI@(sigma^(g_nu*i))@@qI:i in [0..a_div_g_nu-1]] - 1 in PPs_nu_m[k]};
            U_gnu,u_gnu:=ResidueRingUnits(OA,PPs_nu_m[g_nu]);
            UU:=UU@@u_gnu; // in U_gnu

            // tau = sigma^g_nu
            tau:=iso<U_gnu->U_gnu|[U_gnu.i@u_gnu@qI@(sigma^g_nu)@@qI@@u_gnu : i in [1..Ngens(U_gnu)]]>;
            assert forall{i:i in [1..Ngens(U_gnu)]|(tau^(a_div_g_nu))(U_gnu.i) eq U_gnu.i};
            tau_over_id:=hom<U_gnu->U_gnu|[ (U_gnu.i@tau)-U_gnu.i : i in [1..Ngens(U_gnu)]]>;
            assert &+[UU@(tau^i):i in [0..(a_div_g_nu)-1]] eq Zero(U_gnu); // N_{LE_nu/E_nu} = 1
            delta1:=UU@@tau_over_id@u_gnu; //in A
            
            rho_g_nu:=Index(PPs_nu_m,Ideal(OA,[bar_onA(z):z in ZBasis(PPs_nu_m[g_nu])]));
            assert rho_g_nu ne 0;
            delta_nu:=[delta1*p^-(i-1):i in [1..rho_g_nu]] cat [delta1*bU*p^-(i-1):i in [rho_g_nu+1..g_nu]];
            delta_nu:=[pg_nu*x:x in delta_nu]; // to make sure that it is in OA
            assert forall{x:x in delta_nu|x in OA};
            delta_nu:=pg_nu^-1 * CRT(PPs_nu_m,delta_nu); //in A

            // to make sure that the lift is not a zero divisor
            while IsZeroDivisor(delta_nu) do
                delta_nu+:=Random(PPs_nu_m_prod);
            end while;
            return delta_nu,PPs_nu_m_prod;
        end function;

        delta_nu_at_precision_conj_pair:=function(m,nu,onu,g_nu,alpha_nu,alpha_onu,sigma,qI)
        // input:  - m is a positive integer
        //         - nu is a place of E which is not conjugate stable;
        //         - g_nu is the number of primes of A above nu;
        //         - alpha_nu is an element of W-type for pi_nu, computed at precision at least m+g_nu.
        //         - alpha_onu is an element of W-type for pi_bar(nu), computed at precision at least m+g_nu.
        //         - sigma is computed on qI:OA->OA/p^m'*OA, for some m' \geq m.
        // output: - an element delta_nu satisfying delta_nu/sigma(delta_nu)*bar(alpha_nu) = p/alpha_nu  
        //           computed at precision m, that is, in OA/PP where PP:=\prod P^(m*e) where 
        //           P runs over the places of A above nu and e_nu is the ramification at nu (=ramification at each P)
        //         - PP is also returned.
            // sigma^g_nu = tau
            a_div_g_nu:=Integers()!(a/g_nu);
            pg_nu:=A!p^g_nu;
            U:=&*[alpha_nu@qI@(sigma^i)@@qI:i in [0..g_nu-1]]; // = (u_nu,...,u_nu) in A
            bU:=bar_onA(&*[alpha_onu@qI@(sigma^i)@@qI:i in [0..g_nu-1]]); // = (bar(u_onu),...,bar(u_onu)) in A
            pA:=PlacesAboveRationalPrime(A,p);
            pA_nu:=primes_of_A_above_place_of_E(A,nu);
            UbU:=U*bU;
            // The precision is chosen to match the one of the quotients we are using, plus the fact that we are dividing 
            // by p^g_nu
            UU:=CRT([PP^(Dimension(A)*(m+g_nu)):PP in pA],[PP in pA_nu select UbU else pg_nu:PP in pA])/pg_nu;
            assert U in OA;
            assert bU in OA;
            assert UU in OA;
            assert Valuation(UU,P) eq 0 where P:=primes_of_A_above_place_of_E(A,nu)[g_nu];
            PPs_nu_m:=[PP^(RamificationIndex(PP)*m):PP in primes_of_A_above_place_of_E(A,nu)];
            PPs_nu_m_prod:=&*(PPs_nu_m);
            assert2 forall{k:k in [1..g_nu]|&*[ bU@qI@(sigma^(g_nu*i))@@qI : i in [0..a_div_g_nu-1] ] - (q/pi_A) in PPs_nu_m[k]};
            assert2 forall{k:k in [1..g_nu]|&*[ U@qI@(sigma^(g_nu*i))@@qI : i in [0..a_div_g_nu-1] ] - pi_A in PPs_nu_m[k]};
            assert2 forall{k:k in [1..g_nu]|&*[UU@qI@(sigma^(g_nu*i))@@qI:i in [0..a_div_g_nu-1]] - 1 in PPs_nu_m[k]};
            U_gnu,u_gnu:=ResidueRingUnits(OA,PPs_nu_m[g_nu]);
            UU:=UU@@u_gnu; // in U_gnu
            // tau = sigma^g_nu
            tau:=iso<U_gnu->U_gnu|[U_gnu.i@u_gnu@qI@(sigma^g_nu)@@qI@@u_gnu : i in [1..Ngens(U_gnu)]]>;
            assert2 forall{i:i in [1..Ngens(U_gnu)]|(tau^(a_div_g_nu))(U_gnu.i) eq U_gnu.i};
            tau_over_id:=hom<U_gnu->U_gnu|[ (U_gnu.i@tau)-U_gnu.i : i in [1..Ngens(U_gnu)]]>;
            assert2 &+[UU@(tau^i):i in [0..(a_div_g_nu)-1]] eq Zero(U_gnu); // N_{LE_nu/E_nu} = 1
            delta1:=UU@@tau_over_id@u_gnu; //in A
            // We first multiply by p^g_nu to guarantee that the elements are in OA, apply CRT and then divide by p^g_nu.
            delta_nu:=p^-g_nu*CRT(PPs_nu_m,[delta1*p^(g_nu-(i-1)): i in [1..g_nu]]); //in A

            // to make sure that the lift is not a zero divisor
            while IsZeroDivisor(delta_nu) do
                delta_nu+:=Random(PPs_nu_m_prod);
            end while;
            return delta_nu,PPs_nu_m_prod;
        end function;
        
        if not DualsCompatible then
            places_considered:=plE_sl_in01;
            uniformizers_at_nus:=Uniformizers(plE_sl_in01 cat plE_sl_0 cat plE_sl_1)[1..#places_considered];
            g_nus:=[GCD(a,InertiaDegree(nu)):nu in places_considered];
            I:=p^m*OA;
            QI,qI:=ResidueRing(OA,I);
            sigma:=sigma_OA_mod_I(QI,qI,A);
            alphas:=[];
            prime_powers:=[];
            // Considering the action of COMPLEX CONJUGATION on the places above p could speed-up the computation here,
            // by deducing alpha_{nu_bar} from alpha_{nu} whenever nu\neq nu_bar.
            // Note that this consideration does not help with the places stabilized by the action of bar{}.
            for inu->nu in places_considered do
                vprintf alpha_at_precision,1 : "Computing alpha_Q for %oth place of %o...",inu,#places_considered;
                alpha_nu,PPs_nu_m:=alpha_at_precision_W_type_at_place(m,nu,g_nus[inu],sigma,uniformizers_at_nus[inu],qI);
                Append(~alphas,alpha_nu);
                Append(~prime_powers,PPs_nu_m);
                vprintf alpha_at_precision,1 : "done\n";
            end for;
            alpha:=CRT(prime_powers,alphas); // each alpha_nu is integral and of W-type
        else // with DualsCompatible
// delta needs to be computed correctyle at rational p. So we need to consider all places above p.
//places_considered:=plE_sl_0 cat plE_sl_in01 cat plE_sl_1;
//uniformizers_at_nus:=Uniformizers(places_considered);
// FIXME after some more thought, we think that due to the compatibility condition on I,M at p, we want delta = 1 at all places with slope not in (0,1). So we run the computation of delta only for the places with slope in (0,1) and then use CRT.
places_considered:=plE_sl_in01;
uniformizers_at_nus:=Uniformizers(plE_sl_in01 cat plE_sl_0 cat plE_sl_1)[1..#places_considered];
            g_nus:=[GCD(a,InertiaDegree(nu)):nu in places_considered];
            output:=AssociativeArray();
            // We identify the conjugate pairs in places_considered.
            conj_pairs_indices:=[];
            conj_stable_indices:=[];
            to_do:={ 1..#places_considered };
            repeat
                ExtractRep(~to_do,~i);
                nu:=places_considered[i];
                test,nu_bar:=IsConjugateStable(nu);
                if test then
                    Append(~conj_stable_indices,i);
                else
                    i_bar:=Index(places_considered,nu_bar);
                    assert i_bar ne 0;
                    Exclude(~to_do,i_bar);
                    Append(~conj_pairs_indices,<i,i_bar>);
                end if;
            until #to_do eq 0;
            delete to_do;
            // We determine the precision m2 at which delta needs, and consequently,
            // also alpha, needs to be computed. m2 needs to satisfy the inclusion:
            //    p^(m2-g_nu+1) in (W_{R,nu}:OA_nu)=:ff_nu
            // We can take m2=Max_nu(g_nu-1+val_P(ff) where P is any max ideal of OA above nu).
            ff_WR:=OA!!Conductor(WR);
            m2:=Max([GCD(a,InertiaDegree(nu))-1+Valuation(ff_WR,primes_of_A_above_place_of_E(A,nu)[1])
                    : nu in places_considered ]);
            m:=Max(m,m2);
            // In order to compute delta_nu at precision m, we need to compute alpha_nu at precision m+g_nu
            // ( we divide by p^g_nu at a certain point )
            // Since we compute sigma once for all nu's, we do it at precision m+Max(g_nu).
            QI,qI:=ResidueRing(OA,p^(m+Max(g_nus))*OA);
            sigma:=sigma_OA_mod_I(QI,qI,A);
            for inu in conj_stable_indices do
                vprintf alpha_at_precision,1 : "Computing alpha at precision %o for the %o-th place",m,inu;
                nu:=places_considered[inu];
                t_nu:=uniformizers_at_nus[inu];
                // note the precision increase here
                alpha_nu,prod_primes_alpha:=alpha_at_precision_W_type_at_place(m+g_nus[inu],nu,g_nus[inu],sigma,t_nu,qI);
                delta_nu,prod_primes_delta:=delta_nu_at_precision_conj_stable(m,nu,g_nus[inu],alpha_nu,sigma,qI);
                output[nu]:=<alpha_nu,prod_primes_alpha,delta_nu,prod_primes_delta>;
                vprintf alpha_at_precision,1 : "done\n";
            end for;
            for pair in conj_pairs_indices do
                inu,inu_bar:=Explode(pair);
                g_nu:=g_nus[inu];
                vprintf alpha_at_precision,1 : "Computing alpha at precision %o for the (%o,%o)-th places",m,inu,inu_bar;
                nu:=places_considered[inu];
                t_nu:=uniformizers_at_nus[inu];
                nu_bar:=places_considered[inu_bar];
                t_nu_bar:=uniformizers_at_nus[inu_bar];
                // note the precision increase in the next two lines
                alpha_nu,prod_primes_alpha:=alpha_at_precision_W_type_at_place(m+g_nu,nu,g_nu,sigma,t_nu,qI);
                alpha_nu_bar,prod_primes_alpha_bar:=alpha_at_precision_W_type_at_place(m+g_nu,nu_bar,g_nu,sigma,t_nu_bar,qI);
                // The places of A above nu and nu_Bar are sorted compatibly according to complex conjugation in the
                // calls of PlacesOfAAbove done in alpha_at_precision_W_type_at_place.
                // This is needed for the notion of Wtype at nu to be compatible with the notion of Wtype at nu_bar.
                assert prod_primes_alpha_bar eq Ideal(OA,[bar_onA(z):z in ZBasis(prod_primes_alpha)]);
                delta_nu,prod_primes_delta:=delta_nu_at_precision_conj_pair(m,nu,nu_bar,g_nu,alpha_nu,alpha_nu_bar,sigma,qI);
                delta_nu_bar,prod_primes_delta_bar:=delta_nu_at_precision_conj_pair(m,nu_bar,nu,g_nu,alpha_nu_bar,alpha_nu,sigma,qI);
                output[nu]:=<alpha_nu,prod_primes_alpha,delta_nu,prod_primes_delta>;
                output[nu_bar]:=<alpha_nu_bar,prod_primes_alpha_bar,delta_nu_bar,prod_primes_delta_bar>;
                vprintf alpha_at_precision,1 : "done\n";
            end for;
            alpha:=CRT([nu[2]:inu->nu in output],[nu[1]:inu->nu in output]);
            p_max_g_nu:=p^Max(g_nus); //p^N*delta_nu is integral, for every nu
            //delta:=p_max_g_nu^-1*CRT([nu[4]:inu->nu in output],[p_max_g_nu*nu[3]:inu->nu in output]);
delta:=CRT([nu[4]:inu->nu in output],[p_max_g_nu*nu[3]:inu->nu in output]);
plA_sl_0:=&cat[primes_of_A_above_place_of_E(A,nu):nu in plE_sl_0];
plA_sl_1:=&cat[primes_of_A_above_place_of_E(A,nu):nu in plE_sl_1];
plA_sl_in01:=&cat[primes_of_A_above_place_of_E(A,nu):nu in plE_sl_in01];
delta:=[p_max_g_nu*One(A):i in [1..#plA_sl_0+#plA_sl_1]] cat [delta:i in [1..#plA_sl_in01]];
delta:=p_max_g_nu^-1*CRT(plA_sl_0 cat plA_sl_1 cat plA_sl_in01,delta);
            isog`delta_Hilbert90:=delta;
        end if;
        isog`alpha:=alpha;
    end if;
    return isog`alpha;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////
///////////////////////////SemilinearOperators /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic SemilinearOperators(isog::IsogenyClassFq)->RngIntElt,AlgEtQIdl,AlgEtQIdl,GrpAb,Map,Map,Map
{Returns the homonymous attribute of the isogeny class, which consists of the following informations: m0,J,den_ideal,Qm0,qm0,FQm0,VQm0, where (see DieudonneAlgebraCommEndAlg for the missing definitions):
- m0 is a positive integer;
- J is a WR-ideal with maximal endomorphism ring OA which is stable under the action of F and V=pF^-1, for some semilinear operator F with the Frobenius property of and of W-type;
- den_ideal = p^m0*J+P01^M*J, where P01 is the product of the maximal ideals of WR which are above the unique local-local maximal ideal of R, and M is chosen so that P01^MJ c J locally at every such maximal ideal;
- Qm0 is the abelian group J/den_ideal and qm0 is the quotient map J->Qm0;
- FQm0 and Vm0 are additive maps induced by semilinear operators F and V as above. They represent the Frobenius and Verschiebung acting on Dieudonné modules.
The attribute SemilinearOperators needs to be computed beforehand, during a run of IsomorphismClassesDieudonneModulesCommEndAlg. During this run, the integer m0 is automatically computed by the program to guarantee that every fractional W'R-ideal I' whose extension to OA is F and V stable such that I' c J and den_ideal c I'. These two conditions allow us to verify if I' is a W'R\{F,V\} ideal, that is, (the local-local-part) of a Dieudonne module of some abelian variety in isog.}
    //TODO: in the future it would be nice to be able to increase the precision with a call of this intrinsic.
    // This would require to choose a new alpha (as in alpha_at_precision) 'compatible' with the current choice.
    // I might be a bit complicated to code, and it is outside of the current scope.
    require assigned isog`SemilinearOperators : "Run first IsomorphismClassesDieudonneModules(isog)";
    return Explode(isog`SemilinearOperators);
end intrinsic;


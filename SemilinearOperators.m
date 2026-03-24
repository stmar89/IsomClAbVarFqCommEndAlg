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

// FIXME: there are 2 versions of the function to compute alpha: _AlphaAtPrecision and _AlphaAtPrecision_delta.
// Their outputs are equivalent when DualsCompatible:=false, except that the first returns an array with local information,
// while the second glues them using CRT into an element of OA.
// When DualsCompatible:=true the two intrinsic take different approaches.
// The first, which currently 20260320 works only when all places are not conjugate stable, does not use duality 'corrected
// by' delta.
// The second instead uses the correction factors for delta. But this approach as of now, does not always give a correct
// output because of the criticality highlighted in the notes.
// We expect that at a conjugate stable place, we will need a correcting factor delta, whose construction will be a
// refinement of the one used in _AlphaAtPrecision_delta.

intrinsic _AlphaAtPrecision(isog::IsogenyClassFq, m::RngIntElt : DualsCompatible:=false)->AlgEtQElt
{Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi], and m a non-negative integer. The intrinsic returns an approximation of an element alpha in the DieudonneAlgebra A of W-type, that is, the completion alpha_nu at a place nu of E of slope in (0,1) is of the form (1,...,1,u_nu) for u_nu satisfying N_(LE_nu/E_nu)(u_nu)=pi_nu. This is using the identification A_nu = oplus LE_nu. The output is guaranteed to be correct at precision m, meaning that the images of the approximation and of alpha coincide in OA/prod_nu prod_PP PP^(e_nu*m) where the double product is taken over all places nu of E of slope in (0,1) and PP runs over the primes of A above nu.
If the VarArg DualsCompatible is true (default false), then 
// FIXME The description below is for the DualsCompatible:=true case. Needs to be written better 
only when all places are not conjugate stable
the output is an array indexed by places
for each pair nu,nu_bar, exactly one place would be of W-type.
Say it is nu. Then the array at nu contains an element of OA approximating alpha_nu of W-type.
At nu_bar, we put an approximation of q/alpha_nu, which is also in OA.
To contruct F_nu_bar, we will need to take p/bar(alpha_nu), that is, aplly bar and 'divide' the output by p^(a-1).
This cannot be done directly without breaking alpha_nu_bar at the other places above p.
In SemilinearOperator we compute a preimage via the multiplciation-by-p^(a-1) map.
The precision of the computation is internally increased to accomodate this preimage.
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
            PPs_nu_m2,PPs_nu_m2_prod,Rs_nu,rs_nu,Q,embs,projs,pr,Us_nu,us_nu,U,U_embs,U_projs,U_pr:=finite_quotients(m2,nu);
            PPs_nu_m_prod:=&*[PP^(RamificationIndex(PP)+m):PP in primes_of_A_above_place_of_E(A,nu)];

            sigma_U:=hom<U->U | [U.i@@U_pr@qI@sigma@@qI@U_pr : i in [1..Ngens(U)]]>; 
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
            assert alpha_nu*q_alpha_nu - q in PPs_nu_m2_prod;
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
                alpha_nu,PPs_nu_m_prod:=alpha_at_precision_W_type_at_place(m,nu,g_nu,sigma,uniformizers_at_nus[inu],qI);
                output[nu]:=<alpha_nu,PPs_nu_m_prod>;
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
            m2:=m+a-1;
            I:=p^m2*OA;
            QI,qI:=ResidueRing(OA,I);
            sigma_m2:=sigma_OA_mod_I(QI,qI,A);
            for inu in conj_stable_indices do
                vprintf alpha_at_precision,1 : "Computing alpha at precision %o for the %o-th place",m,inu;
                // TODO need to figure out what to do here
                vprintf alpha_at_precision,1 : "done\n";
            end for;
            for pair in conj_pairs_indices do
                inu,inu_bar:=Explode(pair);
                nu:=places_considered[inu];
                nu_bar:=places_considered[inu_bar];
                g_nu:=GCD(a,InertiaDegree(nu));
                assert g_nu eq GCD(a,InertiaDegree(nu_bar));
                vprintf alpha_at_precision,1 : "Computing alpha_Q for the conjugate pair of places <%o,%o>e of %o ...",
                                                    inu,inu_bar,#places_considered;
                if IsOfWType(nu) then
                    unif:=uniformizers_at_nus[inu];
                    alpha_nu,q_alpha_nu,PPs_nu_m_prod:=alpha_W_type_q_alpha_at_precision_at_place(m,m2,nu,g_nu,sigma_m2,unif,qI);
                    assert q_alpha_nu in OA;
                    // FIXME bar might induce a permutation of the places above nu (when g_nu>1) this should be takein into account when constructing alpha_nu_bar
                    alpha_nu_bar:=bar_onA(q_alpha_nu);
                else
                    assert IsOfWType(nu_bar);
                    unif:=uniformizers_at_nus[inu_bar];
                    alpha_nu_bar,q_alpha_nu_bar,PPs_nu_m_prod_bar:=alpha_W_type_q_alpha_at_precision_at_place(m,m2,nu_bar,g_nu,sigma_m2,unif,qI);
                    assert q_alpha_nu_bar in OA;
                    // FIXME bar might induce a permutation of the places above nu (when g_nu>1) this should be takein into account when constructing alpha_nu_bar
                    alpha_nu:=bar_onA(q_alpha_nu_bar); 
                end if;
                PPs_nu_bar_m_prod:=Ideal(OA,[bar_onA(z):z in ZBasis(PPs_nu_m_prod)]);
                output[nu]:=<alpha_nu,PPs_nu_m_prod>;
                output[nu_bar]:=<alpha_nu_bar,PPs_nu_bar_m_prod>;
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
        L,_,_,_,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,_,primes_of_A_above_place_of_E,_,_,bar_onA:=DieudonneAlgebraCommEndAlg(isog);
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

        delta_nu_tot_real_at_precision_conj_stable:=function(m,nu,g_nu,alpha_nu,sigma,qI)
        // input:  - m is a positive integer
        //         - nu is a place of E which is conjugate stable;
        //         - g_nu is the number of primes of A above nu;
        //         - alpha_nu is an element of W-type for pi_nu, computed at precision at least m+g_nu.
        //         - sigma is computed on qI:OA->OA/p^m'*OA, for some m' \geq m.
        // output: - an element delta_nu satisfying delta_nu/sigma(delta_nu)*bar(alpha_nu) = p/alpha_nu  
        //           computed at precision m, that is, in OA/PP where PP:=\prod P^(m*e) where 
        //           P runs over the places of A above nu and e_nu is the ramification at nu (=ramification at each P)
        //         - we pick delta_1 satisfying delta_1=bar(delta_1) 
                     //FIXME this implies delta=bar(delta) when rho is trivial. If this is not the case, then
                     // the output is probably non-sense.
        //         - PP is also returned.
            pg_nu:=A!(p^g_nu);
            a_div_g_nu:=Integers()!(a/g_nu);
            U:=&*[alpha_nu@qI@(sigma^i)@@qI:i in [0..g_nu-1]]; // = (u_nu,...,u_nu) in A
            bU:=bar_onA(U);
            pA:=PlacesAboveRationalPrime(A,p);
            UbU:=U*bU;
            // The precision is chosen to match the one of the quotients we are using, plus the fact that we are dividing 
            // by p^g_nu
            UU:=CRT([PP^(Dimension(A)*(m+g_nu)):PP in pA],
                    [PP in primes_of_A_above_place_of_E(A,nu) select UbU else pg_nu:PP in pA])/pg_nu;
            assert U in OA;
            assert bU in OA;
            assert UU in OA;
            assert Valuation(UU,P) eq 0 where P:=primes_of_A_above_place_of_E(A,nu)[g_nu];
            PPs_nu_m:=[PP^(RamificationIndex(PP)*m):PP in primes_of_A_above_place_of_E(A,nu)];
            PPs_nu_m_prod:=&*(PPs_nu_m);
            assert2 forall{k:k in [1..g_nu]|&*[bU@qI@(sigma^(g_nu*i))@@qI:i in [0..a_div_g_nu-1]]-(q/pi_A) in PPs_nu_m[k]};
            assert2 forall{k:k in [1..g_nu]|&*[ U@qI@(sigma^(g_nu*i))@@qI : i in [0..a_div_g_nu-1] ] - pi_A in PPs_nu_m[k]};
            assert2 forall{k:k in [1..g_nu]|&*[UU@qI@(sigma^(g_nu*i))@@qI:i in [0..a_div_g_nu-1]] - 1 in PPs_nu_m[k]};
            U_gnu,u_gnu:=ResidueRingUnits(OA,PPs_nu_m[g_nu]);
            UU:=UU@@u_gnu; // in U_gnu

            rho_g_nu:=Index(PPs_nu_m,Ideal(OA,[bar_onA(z):z in ZBasis(PPs_nu_m[g_nu])]));

            // FIXME new stuff to try to get delta = bar(delta)
if rho_g_nu ne g_nu then printf "WARNING rho_g_nu ne g_nu\n"; end if;
            // FIXME the next line should break exactly when rho_gnu ne rho_gnu
            bar_onU_gnu_over_id:=iso<U_gnu->U_gnu|[(U_gnu.i@u_gnu@bar_onA@@u_gnu)-U_gnu.i:i in [1..Ngens(U_gnu)]]>;
            U_gnu_TP:=Kernel(bar_onU_gnu_over_id);
            // tau = sigma^g_nu
            tau:=iso<U_gnu->U_gnu|[U_gnu.i@u_gnu@qI@(sigma^g_nu)@@qI@@u_gnu : i in [1..Ngens(U_gnu)]]>;
            assert forall{i:i in [1..Ngens(U_gnu)]|(tau^(a_div_g_nu))(U_gnu.i) eq U_gnu.i};
            // tau/id only on U_gnu_TP
            tau_over_id:=hom<U_gnu_TP->U_gnu_TP|[ U_gnu_TP!((U_gnu_TP.i@tau)-U_gnu_TP.i) : i in [1..Ngens(U_gnu_TP)]]>;
            assert &+[UU@(tau^i):i in [0..(a_div_g_nu)-1]] eq Zero(U_gnu); // N_{LE_nu/E_nu} = 1
            delta1:=((U_gnu_TP!UU)@@tau_over_id)@u_gnu; //in A
            
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
            UU:=CRT([PP^(Dimension(A)*(m+g_nu)):PP in pA],
                    [PP in primes_of_A_above_place_of_E(A,nu) select UbU else pg_nu:PP in pA])/pg_nu;
            assert U in OA;
            assert bU in OA;
            assert UU in OA;
            assert Valuation(UU,P) eq 0 where P:=primes_of_A_above_place_of_E(A,nu)[g_nu];
            PPs_nu_m:=[PP^(RamificationIndex(PP)*m):PP in primes_of_A_above_place_of_E(A,nu)];
            PPs_nu_m_prod:=&*(PPs_nu_m);
            assert2 forall{k:k in [1..g_nu]|&*[bU@qI@(sigma^(g_nu*i))@@qI:i in [0..a_div_g_nu-1]]-(q/pi_A) in PPs_nu_m[k]};
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
// TODO after some more thought, we think that due to the compatibility condition on I,M at p, we want delta = 1 at all places with slope not in (0,1). So we run the computation of delta only for the places with slope in (0,1) and then use CRT.
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
// FIXME TOT real
                delta_nu,prod_primes_delta:=delta_nu_tot_real_at_precision_conj_stable(m,nu,g_nus[inu],alpha_nu,sigma,qI);
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

intrinsic SemilinearOperators(isog::IsogenyClassFq,J::AlgEtQIdl,m0::RngIntElt : DualsCompatible:=false)->GrpAb,Map,Map,Map
{Given a fractional WR\{F,\}V-ideal J such that J*OA < OA and a positive integer m0, returns Qm0,qm0,FQm0,VQm0 where Qm0 is an abelian group isomorphic to the (0,1)-part of J/p^m0*J together with the projection map qm0:J->Qm0 and abelian group endomorphisms FQm0,VQm0:Qm0->Qm0 which approximate F,V having the Frobenius property.
// TODO the duality part is work-in-progress
The vararg DualsCompatible (default false) determines whether FQm0,VQm0 are compatible with duality.}

    //L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,Delta_inverse_ideal,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01:=DieudonneAlgebraCommEndAlg(isog);
    _,_,_,_,A,pi_A,OA,_,WR,sigma_OA_mod_I,_,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01:=DieudonneAlgebraCommEndAlg(isog);
    JOA:=OA!!J;
    require JOA subset OA : "The ideal J does not satisfy J*OA < OA";
    q:=FiniteField(isog);
    _,p,a:=IsPrimePower(q);

    // ###################################
    // The quotients Qm0, Qm0_1
    // ###################################
    vprintf Algorithm_3,1 : "Computing M...";
    primes_01_WR:=primes_of_S_of_slope_in_01(WR);
    // Need M such that P^M*J c p^(m0+1)J, locally at P, for each P in primes_01_WR.
    // By looking at the composition series, one deduces that any 
    // M \geq Truncate(Log(Index(WR,P),Index(J,p^(m0+1)J)) will do.
    size:=(p^(m0+1))^AbsoluteDimension(A); // size = #J/p^(m0+1)J = (p^(m0+1))^dim_Q(A)
    M:=Max( [ Truncate(Log(Index(WR,P),size)) : P in primes_01_WR] );
    vprintf Algorithm_3,1 : "done. Got M=%o\n",M;

    PP01:=(&*(primes_01_WR))^M;
    vprintf Algorithm_3,1 : "Computing Qm0_1...";
    Qm0_1,qm0_1:=Quotient(J,p^(m0+1)*J+PP01*J);
    vprintf Algorithm_3,1 : "done\n";
    vprintf Algorithm_3,1 : "Computing Qm0...";
    den_ideal:=p^(m0)*J+PP01*J;
    Qm0,qm0:=Quotient(J,den_ideal);
    vprintf Algorithm_3,1 : "done\n";
    // these quotients are isomorphic to the (0,1)-parts of J/p^(m0+1)J and J/p^m0J

    pr:=hom< Qm0_1->Qm0 | [ qm0(Qm0_1.i@@qm0_1) : i in [1..Ngens(Qm0_1)]] >;
    assert IsSurjective(pr);
    assert2 forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
    
    // ###################################
    // FQm0 on Qm0, Qm0_1
    // ###################################
    m1:=m0+1+Valuation(Index(OA,JOA),p);
    //m2:=m1+10; "WARNING: m1 is forced now from ",m1,"to",m2; m1:=m2; //for debugging

    vprintf Algorithm_3,1 : "Action of the semilinear Frobenius on Qm0,Qm0_1...\n";
    vprintf Algorithm_3,1 : "\talpha at precision %o...",m0;
    vprintf Algorithm_3,1 : "done\n";
    if not DualsCompatible then
        vprintf Algorithm_3,1 : "Computing sigma on OA/p^m1*OA for m1 = %o...",m1;
        // We have the following inclusions: p^m1*OA c p^(m0+1)*J c I c J c OA.
        // This means the approximation of sigma on OA/p^m1*OA will give a well defined sigma on J/I for each I
        QOA,qOA:=ResidueRing(OA,p^(m1)*OA);
        sigma_QOA,powers_zz_diagonally_inOA_via_zbOE:=sigma_OA_mod_I(QOA,qOA,A);
        vprintf Algorithm_3,1 : "done\n";
        // This procedure can also be done using a CRT on alpha_nu since they are all integral.
        alpha_arr:=_AlphaAtPrecision(isog,m1:DualsCompatible:=false);
        Ps_nus:=[nu[2]:nu in alpha_arr];
        a_nus:=[nu[1]:nu in alpha_arr];
        J_Jnus,Jnus_J:=ChineseRemainderTheoremFunctions(OA!!J,Ps_nus);
        FQm0_1:=hom<Qm0_1->Qm0_1|[qm0_1(Jnus_J([a_nus[inu]*((Qm0_1.i@@qm0_1@J_Jnus)[inu])@qOA@sigma_QOA@@qOA:inu in [1..#a_nus]])) : i in [1..Ngens(Qm0_1)] ]>;
        FQm0:=hom<Qm0->Qm0| [qm0(Jnus_J([a_nus[inu]*((Qm0.i@@qm0@J_Jnus)[inu])@qOA@sigma_QOA@@qOA : inu in [1..#a_nus] ])) : i in [1..Ngens(Qm0)] ]>;
    else
        m1:=2*m1; // in the computation of q_alpha_nu we divide by u_nu. 
                  // Since we want both elements at precision at least m1, we need to to double this value.
        m2:=m1+a-1;
        vprintf Algorithm_3,1 : "Computing sigma on OA/p^m1*OA for m1 = %o...",m1;
        // We have the following inclusions: p^m1*OA c p^(m0+1)*J c I c J c OA.
        // This means the approximation of sigma on OA/p^m1*OA will give a well defined sigma on J/I for each I
        QOA,qOA:=ResidueRing(OA,p^m2*OA);
        sigma_QOA,powers_zz_diagonally_inOA_via_zbOE:=sigma_OA_mod_I(QOA,qOA,A);
        vprintf Algorithm_3,1 : "done\n";

        // VERSION USING delta. to use this version, comment-out everything that follows
        // As of 20260320 there are mathematical issues with this version, discussed in Sec 17 of the notes.
        
        alpha:=_AlphaAtPrecision_delta(isog,m0+1:DualsCompatible:=DualsCompatible);
        FQm0:=hom<Qm0->Qm0 | [ qm0(alpha*(Qm0.i@@qm0@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0)]]>;
        FQm0_1:=hom<Qm0_1->Qm0_1 | [ qm0_1(alpha*(Qm0_1.i@@qm0_1@qOA@sigma_QOA@@qOA)) : i in [1..Ngens(Qm0_1)]]>;

//        // VERSION without delta, which on 20260320 works only when all places are NOT conjugate stable.
//        alpha_arr:=_AlphaAtPrecision(isog,m1:DualsCompatible:=true); // computed at precision m2=m1+a-1
//        nus:=Setseq(Keys(alpha_arr));
//        a_nus:=[nu[1]:nu in alpha_arr];
//        Ps_nus:=[(&*primes_of_A_above_place_of_E(A,nu))^RamificationIndex(nu):nu in nus];
//        J_Jnus,Jnus_J:=ChineseRemainderTheoremFunctions(JOA,[P^m2:P in Ps_nus]);
//        // multiplications by p^(a-1)
//        mults:=[* *];
//        for inu in [1..#nus] do
//            Pnu:=Ps_nus[inu];
//            S,s:=Quotient(Pnu^-(a-1),Pnu^m1);
//            T,t:=ResidueRing(OA,Pnu^m2);
//            Append(~mults,<iso<S->T|[((S.i@@s)*(p^(a-1)))@t:i in [1..Ngens(S)]]>,s,t>);
//        end for;
//        image_qq:=function(g,qq)
//            //qq can be either qm0 or qm0_1
//            out:=[];
//            gg:=g@@qq@qOA@sigma_QOA@@qOA@J_Jnus;
//            for inu in [1..#nus] do
//                if IsOfWType(nus[inu]) then
//                    Append(~out,a_nus[inu]*gg[inu]);
//                else
//                    mult,s,t:=Explode(mults[inu]);
//                    Append(~out,a_nus[inu]*gg[inu]@t@@mult@@s);
//                end if;
//            end for;
//            return out;
//        end function;
//        FQm0:=hom<Qm0->Qm0| [qm0(Jnus_J(image_qq(Qm0.i,qm0))) : i in [1..Ngens(Qm0)] ]>;
//        FQm0_1:=hom<Qm0_1->Qm0_1|[qm0_1(Jnus_J(image_qq(Qm0_1.i,qm0_1))) : i in [1..Ngens(Qm0_1)] ]>;
    end  if;
    assert2 forall{ x : x in Generators(Qm0_1) | FQm0(pr(x)) eq pr(FQm0_1(x))};
    // in the next assert2's, we check that FQm0^a and FQm0_1^a are equal to multiplication by pi_A
    assert2 forall{ x : x in Generators(Qm0) | (FQm0^a)(x) eq qm0(pi_A*(x@@qm0))};
    assert2 forall{ x : x in Generators(Qm0_1) | (FQm0_1^a)(x) eq qm0_1(pi_A*(x@@qm0_1))};
    vprintf Algorithm_3,2 : "\tFQ's are computed\n";

    // ###################################
    // VQm0 on Qm0, Qm0_1
    // ###################################
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
    return Qm0,qm0,FQm0,VQm0;
end intrinsic;

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



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

declare verbose DieudonneModules,3;
declare verbose DieudonneModules_L,3;
declare verbose Algorithm_2,3;
declare verbose Algorithm_3,3;
declare verbose sigma,3;
declare verbose alpha_at_precision,3;
declare verbose Delta_scaling,3;

declare attributes IsogenyClassFq : DiedudonneAlgebraCommEndAlg,
                                    SemilinearOperators;
                               
declare attributes AlgEtQ         : sigma_fin_prec,
                                    PlacesAboveRationalPrime;

declare attributes AlgEtQOrd      : units_quotient_fixed_sigma,
                                    PrimesOfSlopeIn01;

declare attributes AlgEtQIdl :      DeltaEndomorphismRing,
                                    DeltaInverse,
                                    PlacesOfAAbove;

////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////// DiedudonneAlgebraCommEndAlg /////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic DieudonneAlgebraCommEndAlg(isog::IsogenyClassFq)->FldNum,RngOrd,RngOrdIdl,RngIntElt,AlgEtQ,AlgEtQElt,AlgEtQOrd,Map,UserProgram,UserProgram,UserProgram
{Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi]. This intrisic populates the attribute DiedudonneAlgebraCommEndAlg of the isogeny class, which consists of the tuple 
<L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,Delta_inverse_ideal,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01,alpha_at_precision> where
- L is a number field such that L\otimes_Q Qp is an unramified field extension of Qp of degree a; OL is its maximal order and PL=p*OL; normPL is the size of OL/PL;
- A is an etale algebra isomorphic to E\otimes_Q L; OA is its maximal order;
- WR is an order in A, isomorphic to R\otimes_Z OA.
- sigma_OA_mod_I is a function that given an OA-ideal I such that the quotient OA/I is killed by a power of p, it returns a reduction of the map induced by the Frobenius automorphism of (L\otimes_Q Qp)/Qp;
- Delta_map is the natural embedding of E->A; pi_A is the image of pi, the Frobenius endomorphism of isog;
- Delta_inverse_ideal is a function that given a fractional WR-ideal returns its preimage via Delta_map;
- primes_of_A_above_place_of_E is a function that given A and a maximal ideal P of E returns the maximal ideals of OA above P;
- primes_of_S_of_slope_in_01 is a function that given an overorder S of WR returns its maximal ideals P with 'slope' in the open interval (0,1), that is, the P's that are below the maximal ideals of OA, which are above maximal ideals of OE of slope in (0,1); 
- alpha_at_precision is a function that given a positive integer m returns an element alpha of OA, as reqired by Algorithm 2 of the paper, to define the reductions of the semilinear operator F with the Frobenius property and of W-type; more precisely: alpha is congruent mod p^m*OA to an element alpha' whose image in A\otimes_Q Qp = \prod_nu \prod_(i=1)^gnu LE_nu has nu component alpha'_nu=(1,....,1,u) where N_(LE_nu/E_nu)(u)=pi_nu.}
    if not assigned isog`DiedudonneAlgebraCommEndAlg then
        require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
        R:=ZFVOrder(isog);
        E:=Algebra(R);
        pi:=PrimitiveElement(E);
        h:=DefiningPolynomial(E);
        g:=Dimension(isog);
        q:=FiniteField(isog);
        t,p,a:=IsPrimePower(q);
        assert t;
        _,plE_sl_in01,_:=PlacesOfQFAbove_p(isog);
        // ################### 
        // Global Representatives: L and sigma_L
        // ###################
        
        // the following gives a very small polynomial hL
        if a eq 1 then
            hFq:=[0,1]; // I force L to be Q[x]/(x) so that A = E
            hL:=Parent(h) ! hFq; 
        else
            Fp:=GF(p);
            Fpy<y>:=PolynomialRing(Fp);
            Fq:=GF(q);
            U,u:=MultiplicativeGroup(Fq);
            hL:=Parent(h)!MinimalPolynomial(u(U.1));
            assert Degree(hL) eq a;
        end if;
        L:=NumberField(hL : DoLinearExtension:=true);
        OL:=MaximalOrder(L);
        zb_OL:=Basis(OL);
        PL:=Factorization(p*OL);
        assert #PL eq 1 and PL[1,2] eq 1; // L has a unique prime above p, which is unramified.
        PL:=PL[1,1];
        normPL:=Index(OL,PL);
        
        // ################### 
        // Global Representatives: A
        // ###################

        fac_h_L:=Factorization( PolynomialRing(L) ! h );
        assert forall{ g : g in fac_h_L| g[2] eq 1 }; // h is assumed to be squarefree
        nfs_A:=[ NumberField(g[1] : DoLinearExtension:=true ) : g in fac_h_L ];
        nfs_A_abs:=[ AbsoluteField(nf) : nf in nfs_A ];

        // A: an etale algrebra over Q. isomorphic to L \otimes E
        A:=EtaleAlgebra(nfs_A_abs);
        OA:=MaximalOrder(A);
        vprintf DieudonneModules_L,2 : "A = %o\n",A;
        _,embs_A,proj_A:=Components(A);

        // inclusion L in A
        emb_L_inA:=map< L -> A | x:->&+[ embs_A[i](nfs_A_abs[i]!x) : i in [1..#nfs_A] ]>;
        zb_OL_inA:=[ emb_L_inA(x) : x in zb_OL ];

        // pi in A
        pi_A_comps:=<  >;
        for i in [1..#nfs_A] do
            pi_i:=PrimitiveElement(nfs_A[i]);
            pi_i:=nfs_A_abs[i]!pi_i;
            Append(~pi_A_comps,pi_i);
        end for;
        pi_A:=A!pi_A_comps;
        assert MinimalPolynomial(pi_A) eq h;
        assert forall{ i : i in [1..#nfs_A] | Evaluate(fac_h_L[i][1],pi_A_comps[i]) eq 0 };
        pows_pi_A:=[ pi_A^i : i in [0..Dimension(E)-1 ]];

        // #######################
        // Delta: E->A, the natural embedding
        // #######################

        OrderAsFreeAbelianGroup:=function(R)
        // Returns F,f where F is a free abelian group isomorphic to R and f is an isomorphism.
        // It depends on the stored ZBasis(R)
            n:=Dimension(Algebra(R));
            F:=FreeAbelianGroup(n);
            zb:=ZBasis(R);
            f:=map<R->F | x:->F!AbsoluteCoordinates([x],zb),
                          y:->SumOfProducts(Eltseq(y),zb) >;
            return F,f;
        end function;

        FOA,fOA:=OrderAsFreeAbelianGroup(OA);
        assert2 forall{ z : z in ZBasis(OA) | fOA(z)@@fOA eq z };

        Delta_image:=function(z)
            out:=SumOfProducts(AbsoluteCoordinates([z],PowerBasis(E))[1],pows_pi_A);
            assert2 MinimalPolynomial(out) eq MinimalPolynomial(z);
            return out;
        end function;

        imageDeltaOE_inFOA:=sub<FOA | [fOA(Delta_image(z)) : z in ZBasis(MaximalOrder(E)) ]>;

        mat_pows_pi_A:=Matrix([AbsoluteCoordinates(x) : x in pows_pi_A ]);
        Delta_preimage:=function(y)
            // Need to write y as a linear combination of pows_pi_A
            // Use Solution V to V*X =W
            W:=Matrix([AbsoluteCoordinates(y)]);
            return SumOfProducts(Eltseq(Solution(mat_pows_pi_A,W)),PowerBasis(E));
        end function;

        Delta_map:=map< E->A | z:->Delta_image(z),
                               y:->Delta_preimage(y) >;

        // TEST
        assert2 forall{ z : z in ZBasis(MaximalOrder(E)) | z eq (Delta_map(z))@@Delta_map }; 
        assert2 forall{ z : z in ZBasis(R) | z eq (Delta_map(z))@@Delta_map }; 
        assert2 forall{ i : i,j in ZBasis(MaximalOrder(E)) | Delta_map(i+j) eq Delta_map(i)+Delta_map(j) };
        assert2 forall{ i : i,j in ZBasis(MaximalOrder(E)) | Delta_map(i*j) eq Delta_map(i)*Delta_map(j) };

        // #######################
        // tilde W_R: order isomorphic to W \otimes R
        // #######################
      
        pi_A_bar:=q/pi_A;
        gens_WR:=&cat[[ z,z*pi_A,z*pi_A_bar ] : z in zb_OL_inA] cat [pi_A, pi_A_bar];
        WR:=Order(gens_WR);

        // test
        assert pi_A in WR;
        assert q/pi_A in WR;
        assert2 Index(OA,WR) ge Index(MaximalOrder(E),R);
        // end test

        // ####################
        // Delta_inverse_ideal
        // ####################

        Delta_inverse_ideal:=function(I)
        // given a fractional-WR ideal returns Delta^{-1}(I), which is a fractional R-ideal
            if not assigned I`DeltaInverse then
                assert Order(I) eq WR;
                dI,d:=MakeIntegral(I);
                ZBasisLLL(dI);
                dI_inFOA:=sub<FOA | [fOA(z) : z in ZBasis(dI) ]>;
                // the next line can be very memory consuming
                meet_id:=dI_inFOA meet imageDeltaOE_inFOA;
                gens_dI_meet_DeltaOE:=[ (g@@fOA)@@Delta_map : g in Generators(meet_id) ];
                J:=(1/d)*Ideal(R,gens_dI_meet_DeltaOE);
                assert2 forall{z : z in ZBasis(J) | Delta_map(z) in I};
                I`DeltaInverse:=J;
            end if;
            return I`DeltaInverse;
        end function;
   
        // #######################
        // tilde sigma (on A): acts as the L-Forbenius on L-coeffs when A is written as L+pi*L+...+pi^(deg(h)-1)L
        // #######################

        // We have defined A = prod_i L[x]/(h_i(x)).
        // In order to compute sigma, we need to understand the action of the Frobenius sigma_L of L.
        // To do so, we need to represent A as W:=L + pi*L + ... +pi^(deg(h)-1)L and compute L-isomorphism mAW:A->W.
        Vs:=[];
        vs:=<>;
        for i in [1..#nfs_A] do
            V,v:=VectorSpace(nfs_A[i],L); // v:nfs_A[i]->V
            Append(~Vs,V);
            Append(~vs,v);
        end for;
        D,embs,projs:=DirectSum(Vs); // mAD: A -> D isom
        mAD:=map<A->D |  x :-> &+[ embs[i](vs[i](nfs_A[i]!Components(x)[i])) : i in [1..#nfs_A] ] ,
                         y :-> A!< nfs_A_abs[i]!(projs[i](y))@@vs[i] : i in [1..#nfs_A] > >;
        // we compute the image of pows_pi_A in D 
        pows_pi_D:=[ mAD(x) : x in pows_pi_A ];
        W:=KSpace(L,Degree(h));
        mWD:=iso< W->D | pows_pi_D >;
        mAW:=map< A->W | x:->mAD(x)@@mWD, y:-> mWD(y)@@mAD >;

        // Note that OA \simeq OE \otimes ZZ[zz] locally at p.
        // We need to compute the images of a ZBasis of OE in Q.
        // Let b be an element of OE: write it as d1 + pi*d2 + ... + pi^(2g-1)*d_{2g} for integers d_i.
        // The the image of b in Q is mQ(W!(d1,...,d_{2g}))@@mAW).
        OE:=MaximalOrder(E);
        pb_OE:=[ pi^(i-1) : i in [1..AbsoluteDimension(E)] ];
        zbOE_in_OA:=[ (W!b)@@mAW : b in AbsoluteCoordinates(ZBasis(OE),pb_OE) ];
        assert2 forall{i:i in [1..#ZBasis(OE)]| MinimalPolynomial(zbOE_in_OA[i]) eq MinimalPolynomial(ZBasis(OE)[i])};
        // We now constuct an isomorphism A->L^2g using zbOE_inOA. 
        // This corresponds to write OA = OE \otimes OL (locally at p).
        // We need this description of OA to compute the action of sigma, which is trivial on the 'OE-part'.
        zbOE_in_D:=[ mAD(b) : b in zbOE_in_OA ];
        mWD_zbOE:=iso<W->D | zbOE_in_D >;
        mAW_zbOE:=map<A->W | x:->mAD(x)@@mWD_zbOE, y:->mWD_zbOE(y)@@mAD >;

        sigma_OA_mod_I:=function(Q,mQ,A)
        // Given mQ:OA->Q=OA/I, with I an OA-ideals and with Q being an OL/PL^m-module for some m, 
        // where PL is the only prime of OL,
        // returns a ring homomorphism Q->Q induced by Frobenius automorphism of L\otimes Qp.
            
            // m can be computed using the formula |OL/PL|^m = |OA/I|
            t,m:=IsPowerOf(#Q,normPL);
            assert t;
            //m:=30*m; printf "Warning increasing the precision\n";
            if m eq 0 then
                vprintf sigma,2 : "m=0 -> sigma is the identity on Q\n";
                return hom<Q->Q | [Q.i : i in [1..Ngens(Q)]] >;
            end if;

            // We compute the automorphism of the finite ring OL/PL^m induced 
            // by the Frobenius automorphism L\otimes Qp.
            // It is chached in an attribute of A.
            // This is done in the following way:
            // - in OL, find an element 'zeta' congruent mod PL^m to an inertial element (=uniformizer) of OLp
            //   by taking successive q-powers of the image 'frob' of a generator of (OL/PL)^*
            //   until the sequence stabilizes (this approximation method seems well known 
            //   TODO add references to Magma documentation).
            // - We create an auxiliary number field LL<zz>, isomorphic to L via zz:->zeta.
            // - We have an isomorphism OL/PL^m = ZZ[zz]/p^m*ZZ[zz].
            // - It follows that zz:->zz^p induces (a conjugate of) the Frobenius automorphism on the quotient
            if not assigned A`sigma_fin_prec or A`sigma_fin_prec[1] lt m then
                _,moL:=quo<OL | PL^m >;
                frob:=moL(L.1); // L.1 generates F_q = OL/pOL, by the way L is constructed above.
                repeat
                    old:=frob;
                    frob:=frob^q;
                until frob eq old;
                zeta:=frob@@moL; // zeta is congruent to an inertial element mod m
                LL<zz>:=NumberField(MinimalPolynomial(zeta) : DoLinearExtension:=true);
                assert Degree(LL) eq Degree(L);
                LLtoL:=iso<LL->L | [ zeta ] >;
                assert2 LLtoL(zz^2) eq zeta^2 and LLtoL(zz+2) eq zeta+2;

                // - We realize ZZ[zz] as a free abelian group F and zz:->zz^p as an additive map sigma_F:F->F.
                F:=FreeAbelianGroup(Degree(L)); // F = ZZ[zz] as abelian group
                imgs_zz:=[ F!ChangeUniverse(Eltseq(zz^(p*(i-1))),Integers()) : i in [1..Degree(L)] ];
                sigma_F:=hom<F->F | [ imgs_zz[i] : i in [1..Ngens(F)] ]>; 

                FtoFOA:=map<F->FOA|x:->fOA((W![ LLtoL(LL!Eltseq(x)):i in [1..AbsoluteDimension(E)]])@@mAW_zbOE)>; 
                powers_zz_diagonally_inOA_via_zbOE:=[ (FtoFOA(z))@@fOA : z in imgs_zz ];
                // F=ZZ[zz] -> OA=FOA induced by zz:->sum_i zz*zi where zi is the image of a ZBasis of OA in FOA
               
                A`sigma_fin_prec:=<m,F,sigma_F,LL,LLtoL,powers_zz_diagonally_inOA_via_zbOE>;
            end if;
            _,F,sigma_F,LL,LLtoL,powers_zz_diagonally_inOA_via_zbOE:=Explode(A`sigma_fin_prec);

            // - To do so, we need to find the ZZ[zz]-module structure of Q. 
            // - More precisely, we need a sigma-equivariant presentation ZZ[zz]^s->>Q.
            // - We need a set of generators of J over ZZ[zz] which are fixed by sigma, i.e. in Delta(E).
            // - If J = OA, since OA = OE \otimes Z[zz] (at p), we can use the images b1,...,b2g of the
            // ZBasis of OE in OA we computed before, together with the isomorphsm mAW_zbOE:A->L^2g.
            Fs,embs,projs:=DirectSum([F : i in [1..AbsoluteDimension(E)]]);
            sigma_Fs:=hom<Fs->Fs|[&+[ embs[i](sigma_F(projs[i](Fs.j))): i in [1..AbsoluteDimension(E)]]
                                  :j in [1..Ngens(Fs)]]>;
            // sigma_Fs is simply sigma_F on each component
            FstoOA:=map<Fs->A | x:-> (W![ LLtoL(LL!Eltseq(projs[i](x))) : i in [1..#projs] ])@@mAW_zbOE >; 
            // Fs->LL^2g->W->D->A where the last iso is given by mAW_zbO
            assert2 forall{ i : i in [1..Ngens(Fs)] | FstoOA(Fs.i) in OA };
            pres:=hom<Fs->Q | [ mQ(FstoOA(Fs.i)) : i in [1..Ngens(Fs)]] >;
            assert IsSurjective(pres);

            sigma_Q:=hom<Q->Q | [ Q.i@@pres@sigma_Fs@pres : i in [1..Ngens(Q)] ]>;
            assert2 forall{i : i,j in [1..Ngens(Q)] | sigma_Q(mQ(gQ[i]*gQ[j])) eq mQ(sigma_gQ[i]*sigma_gQ[j]) 
                            where gQ:=[ Q.k@@mQ : k in [1..Ngens(Q)]]
                            where sigma_gQ:=[ (sigma_Q(Q.k))@@mQ : k in [1..Ngens(Q)]]
                         };
            assert IsSurjective(sigma_Q);
            assert IsTrivial(Kernel(sigma_Q));
            return sigma_Q,powers_zz_diagonally_inOA_via_zbOE;
        end function;

        // #######################
        // primes of orders in A above places
        // #######################

        primes_of_A_above_place_of_E:=function(A,P)
        // see the description above
            if not assigned P`PlacesOfAAbove then
                OA:=MaximalOrder(A);
                P`PlacesOfAAbove:=PrimesAbove(Ideal(OA,[ Delta_map(z) : z in ZBasis(P)]));
            end if;
            return P`PlacesOfAAbove;
        end function;
       
        primes_of_S_of_slope_in_01:=function(S)
        // see the description above
            if not assigned S`PrimesOfSlopeIn01 then
                pp:=[];
                oneS:=OneIdeal(S);
                A:=Algebra(S);
                for P in plE_sl_in01 do
                    pp_P:=Setseq({ oneS meet (S!!Q) : Q in primes_of_A_above_place_of_E(A,P) });
                    pp cat:= pp_P;
                    assert2 forall{P : P in pp | IsPrime(P)};
                end for;
                S`PrimesOfSlopeIn01:=pp;
            end if;
            return S`PrimesOfSlopeIn01;
        end function;

        // #######################
        // alpha
        // #######################

        alpha_at_precision:=function(m)
        // see the description above
        // - alpha using the unit argument
            I:=p^m*OA;
            QI,qI:=ResidueRing(OA,I);
            sigma:=sigma_OA_mod_I(QI,qI,A);
            alpha_Q_inAs:=[];
            PPs_nus_prod_powers:=[];
            uniformizers_at_nus:=Uniformizers(plE_sl_in01);
            for inu->nu in plE_sl_in01 do
                vprintf alpha_at_precision,1 : "Computing alpha_Q for %oth place of %o...",inu,#plE_sl_in01;
                // Can add DUALITY here
                PPs_nu:=primes_of_A_above_place_of_E(A,nu);
                f_nu:=InertiaDegree(nu);
                g_nu:=GCD(a,f_nu); //q=p^a
                assert #PPs_nu eq g_nu;

                Rs_nu:=[];
                rs_nu:=<>;
                Us_nu:=[];
                us_nu:=<>;
                PPs_nu_m:=[];
                for PP in PPs_nu do
                    PP_m:=PP^(RamificationIndex(PP)*(m));
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
                Append(~PPs_nus_prod_powers,PPs_nu_m_prod);

                Q,embs,projs:=DirectSum(Rs_nu);
                pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                           y:->CRT( PPs_nu_m ,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
                pi_Q:=pr(pi_A);
                assert2 forall{ x : x in Generators(Q) | pr(x@@pr) eq x};

                U,U_embs,U_projs:=DirectSum(Us_nu);
                U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                             y:->CRT( PPs_nu_m ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
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
                
                u_nu:=uniformizers_at_nus[inu]; // in E
                val_nu:=Valuation(pi,nu); // in E
                w_nu:=pi/(u_nu^val_nu); // in E
                assert Valuation(w_nu,nu) eq 0;
                wU:=U_pr(Delta_map(w_nu)); // in E->A->U
                gamma0:=wU@@phi; // in Us[g_nu], the last componenet of U
                gamma_A:=(&+[i lt g_nu select 
                                        U_embs[i](One(A)@@us_nu[i]) else 
                                        U_embs[i](gamma0) : i in [1..g_nu]])@@U_pr; // in A
                u0:=Delta_map(u_nu^(Integers()!(val_nu*g_nu/a)));
                beta_A:=(&+[i lt g_nu select 
                                        embs[i](rs_nu[i](One(A))) else 
                                        embs[i](rs_nu[i](u0)) : i in [1..g_nu]])@@pr; 
                alpha_A:=gamma_A*beta_A;
                Append(~alpha_Q_inAs,alpha_A);
                vprintf alpha_at_precision,1 : "done\n";
            end for;
            // end of unit argument
            alpha:=CRT( PPs_nus_prod_powers, alpha_Q_inAs );
            vprintf alpha_at_precision,1 : "alpha = %o\n",PrintSeqAlgEtQElt([alpha])[1];
            return alpha;
        end function;

        isog`DiedudonneAlgebraCommEndAlg:=<L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,Delta_inverse_ideal,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01,alpha_at_precision>;
    end if;
    return Explode(isog`DiedudonneAlgebraCommEndAlg);
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
    L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,Delta_inverse_ideal,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01,alpha_at_precision:=DieudonneAlgebraCommEndAlg(isog);
    vprintf DieudonneModules,1 : "done\n";
    vprintf DieudonneModules,1 : "[OE:R] = %o\ndim_Q(L)=%o\ndim_Q(A)=%o\n",Index(MaximalOrder(E),R),Degree(L),Dimension(A);
    _,plE_sl_in01,_:=PlacesOfQFAbove_p(isog);
    _,pl_01_R,_:=PrimesOfZFVAbove_p(isog);
    pl_01_R:=Setseq({ OneIdeal(R) meet (R!!P) : P in plE_sl_in01 });
    if #plE_sl_in01 ne 0 then
        assert #pl_01_R eq 1;
        vprintf DieudonneModules,1 : "[OE':R'] = %o\n",Index(MaximalOrder(E),Order(ZBasis(R) cat ZBasis(MaximalOrder(E)!!pl_01_R[1])));
    end if;

    vprintf DieudonneModules,2 : "places of E w/ slope in (0,1) = %o\n",Sort([ Slope(P) : P in plE_sl_in01]);
    // Early exit if no places 
    if #plE_sl_in01 eq 0 then
        dm:=OneIdeal(R);
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
        primes_01_S:=primes_of_S_of_slope_in_01(S);
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
        Append(~pp_A_nus,primes_of_A_above_place_of_E(A,P));
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
    // given B c A, returns the vp(Exponent(Quotient(A,B))) without computing Quotient(A,B)
        vp_ind:=Valuation(Index(A,B),p);
        // now I only compute the quotient of the p-part.
        vp_exp:=Valuation(Exponent(Quotient(A,B+p^vp_ind*A)),p);
        return vp_exp;
    end function;

    Delta_scale_inside:=function(I,J)
    // given an OA-ideal WR!!J and a WR-ideal I, it find an element x in E^* such that Delta(x)I c J.
    // This element is chosen so that [J:xI] will have a small p-adic valuation.
        vprintf Delta_scaling,1 : "Computing: colon ideal...";
        cc:=OA!!ColonIdeal(J,I);
        exps:=[];
        vprintf Delta_scaling,1 : "M_nu's";
        for nu in nus do
            M_nu:=Max([Valuation(cc,P) : P in primes_of_A_above_place_of_E(A,nu)]);
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
        vprintf Delta_scaling,1 : "pExponent=";
        vpN:=pExponent(J,yxI);
        vprintf Delta_scaling,1 : "%o...",vpN;
        vprintf Delta_scaling,1 : "done";
        return yxI,vpN;
    end function;

    // We need to scale all I's by an element of Delta(E) inside J, so that the max value of vp(exp(J/I)) 
    // is as small as possible.
    m0:=0; 
    for i in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        I:=WR_01_idls_with_ext_i_to_OA_F_V_stable[i];
        ZBasisLLL(I);
        D_scale:=true;
        if I subset J then
            vpN:=pExponent(J,I);
            if vpN le m0 then
                D_scale:=false;
            end if;
        else
            // we first try to push I in J by multiplying by the pExponent 
            vp_x:=pExponent(I+J,J);
            if vp_x le m0 then
                vprintf Delta_scaling,1 : "\npExp-scaling the %o-th ideal into J...",i;
                x:=p^vp_x;
                xI:=x*I;
                y:=Index(xI+J,J);
                assert (y mod p) ne 0; // y coprime p
                yxI:=y*xI;
                assert yxI subset J;
                D_scale:=false;
                vprintf Delta_scaling,1 : "ZBasisLLL...";
                ZBasisLLL(yxI);
                vprintf Delta_scaling,1 : "done";
                WR_01_idls_with_ext_i_to_OA_F_V_stable[i]:=yxI;
            end if;
        end if;
        if D_scale then
            vprintf Delta_scaling,1 : "\nDelta-scaling the %o-th ideal into J...",i;
            I,vpN:=Delta_scale_inside(I,J);
            m0:=Max(m0,vpN);
            WR_01_idls_with_ext_i_to_OA_F_V_stable[i]:=I;
        end if;
    end for;
    vprintf Algorithm_3,1 : "done\n";

    if IncreaseMinimumPrecisionForSemilinearFVBy gt 0 then
        m0_old:=m0;
        m0+:=IncreaseMinimumPrecisionForSemilinearFVBy;
        vprintf Algorithm_3:"Incresing m0 from to %o, using IncreaseMinimumPrecisionForSemilinearFVBy\n",m0_old,m0;
    end if;

    vprintf Algorithm_3 : "m0 = %o\n",m0;
    vprintf Algorithm_3,2 : "v_nu(pi) for all nu's = %o\n",[ Valuation( pi, P ) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "e_nu for all nu's = %o\n",[ RamificationIndex(P) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "f_nu for all nu's = %o\n",[ InertiaDegree(P) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "g_nu for all nu's = %o\n",[ GCD(a,InertiaDegree(P)) : P in plE_sl_in01 ];

    //m1:=m0+10; "WARNING: m0 is forced now from ",m0,"to",m1; m0:=m1; //for debugging
    vprintf Algorithm_3,1 : "Computing alpha at precision %o...",m0;
    alpha:=alpha_at_precision(m0+1);
    vprintf Algorithm_3,1 : "done\n";
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
    // these quotients are isomorphic to the (0,1)-part of J/p^(m0+1)J and J/p^m0J

    pr:=hom< Qm0_1->Qm0 | [ qm0(Qm0_1.i@@qm0_1) : i in [1..Ngens(Qm0_1)]] >;
    assert IsSurjective(pr);
    assert2 forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
    
    // ###################################
    // Semilinear Frobenius on Qm0, Qm0_1
    // ###################################
    assert JOA subset OA;
    m1:=m0+1+Valuation(Index(OA,JOA),p);
    //m2:=m1+1000; "WARNING: m1 is forced now from ",m1,"to",m2; m1:=m2; //for debugging
    vprintf Algorithm_3,1 : "Computing sigma on OA/p^m1*OA for m1 = %o...",m1;
    // We have the following inclusions: p^m1*OA c p^(m0+1)*J c I c J c OA.
    // This means the approximation of sigma on OA/p^m1*OA will give a well defined sigma on Q=J/I
    QOA,qOA:=ResidueRing(OA,p^m1*OA);
    sigma_QOA,powers_zz_diagonally_inOA_via_zbOE:=sigma_OA_mod_I(QOA,qOA,A);
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
        I:=WR_01_idls_with_ext_i_to_OA_F_V_stable[iI];
        if is_F_V_stable(I) then
            vprintf Algorithm_3,2 : "y";
            assert Order(I) eq WR;
            mI:=MultiplicatorRing(I);
            t:=exists(S){pair[2]:pair in delta_inverses_mult_rings|pair[1] eq mI};
            if not t then
                Sid:=Delta_inverse_ideal(WR!!OneIdeal(mI));
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


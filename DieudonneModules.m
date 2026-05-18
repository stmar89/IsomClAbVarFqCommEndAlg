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
declare verbose sigma,3;

declare attributes IsogenyClassFq : DiedudonneAlgebraCommEndAlg;
                               
declare attributes AlgEtQ         : sigma_fin_prec;

declare attributes AlgEtQIdl      : DeltaEndomorphismRing;

///////////////
// Auxiliary //
///////////////

OrderAsFreeAbelianGroup:=function(R)
// Returns F,f where F is a free abelian group isomorphic to R and f is an isomorphism.
// It depends on the stored ZBasis(R)
    n:=Dimension(Algebra(R));
    F:=FreeAbelianGroup(n);
    zb:=ZBasis(R);
    f:=map<R->F | x:->F!AbsoluteCoordinates([x],zb),
                  y:->DotProduct(Eltseq(y),zb) >;
    return F,f;
end function;

////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////// DiedudonneAlgebraCommEndAlg /////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic DieudonneAlgebraCommEndAlg(isog::IsogenyClassFq)->FldNum,RngOrd,RngOrdIdl,RngIntElt,AlgEtQ,AlgEtQElt,AlgEtQOrd,Map,AlgEtQOrd,UserProgram,Tup,Tup
{Let isog be an isogeny class of abelian varieties over Fq, with q=p^a, with commutative endomorphism algebra E=Q[pi]. This intrisic populates the attribute DiedudonneAlgebraCommEndAlg of the isogeny class, which consists of the tuple 
<L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,A_as_vector_space_over_L_data,OA_as_abelian_group_data> where
- L is a number field such that L\otimes_Q Qp is an unramified field extension of Qp of degree a; OL is its maximal order and PL=p*OL; normPL is the size of OL/PL;
- A is an etale algebra isomorphic to E\otimes_Q L; OA is its maximal order;
- WR is an order in A, isomorphic to R\otimes_Z OA.
- sigma_OA_mod_I is a function that given an OA-ideal I such that the quotient OA/I is killed by a power of p, it returns a reduction of the map induced by the Frobenius automorphism of (L\otimes_Q Qp)/Qp;
- Delta_map is the natural embedding of E->A; pi_A is the image of pi, the Frobenius endomorphism of isog;
- A_as_vector_space_over_L_data is a tuple consistsing of three L-linear isomorphisms m1,m2,m3 allowing to represent A as an L-vector space. Let V1 be the direct sums of L[x]/(gi) where gi runs over the factors of the Weil polynomial over L[x] and where each extension of L is considered as an L-vector space using the power basis. Let V2 be L-vector space structure on A induced by the L-basis pi_A^i where i=0,..,dim_Q(E). Then m1:A->V1 and m2:V2->V1 are the natural isomorphisms and m3:A->V2 is the composition a:->m2^-1(m1(a)).
- OA_as_abelian_group_data is the tuple <FOA,fOA,imageDeltaOE_inFOA> where FOA is a free abelian group and fOA:=OA->FOA is an isomorphism, and imageDeltaOE_inFOA is the image of Delta(OE) in FOA. This tuple is used to compute Delta^-1 of orders and ideals in the DieudonneAlgebra.}
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

        Delta_image:=function(z)
            out:=DotProduct(AbsoluteCoordinates([z],PowerBasis(E))[1],pows_pi_A);
            assert2 MinimalPolynomial(out) eq MinimalPolynomial(z);
            return out;
        end function;

        mat_pows_pi_A:=Matrix([AbsoluteCoordinates(x) : x in pows_pi_A ]);
        Delta_preimage:=function(y)
            // Need to write y as a linear combination of pows_pi_A
            // Use Solution V to V*X =W
            W:=Matrix([AbsoluteCoordinates(y)]);
            return DotProduct(Eltseq(Solution(mat_pows_pi_A,W)),PowerBasis(E));
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
        A_as_vector_space_over_L_data:=<mAD,mWD,mAW>;

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

        FOA,fOA:=OrderAsFreeAbelianGroup(OA);
        assert2 forall{ z : z in ZBasis(OA) | fOA(z)@@fOA eq z };
        imageDeltaOE_inFOA:=sub<FOA | [fOA(Delta_image(z)) : z in ZBasis(MaximalOrder(E)) ]>;
        OA_as_abelian_group_data:=<FOA,fOA,imageDeltaOE_inFOA>;

        sigma_OA_mod_I:=function(Q,mQ,A)
        // Given mQ:OA->Q=OA/I, with I an OA-ideal and with Q an OL/PL^m-module for some m, 
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
            //   Reference: Magma Documentation, Example RngLoc_unram-ext (H49E13).
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

        isog`DiedudonneAlgebraCommEndAlg:=<L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,A_as_vector_space_over_L_data,OA_as_abelian_group_data>;
    end if;
    return Explode(isog`DiedudonneAlgebraCommEndAlg);
end intrinsic;



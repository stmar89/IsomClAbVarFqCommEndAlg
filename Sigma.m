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

declare verbose sigma,3;

declare attributes AlgEtQ : sigma_fin_prec;

intrinsic SigmaOnQuotientOfOA(isog::IsogenyClassFq,I::AlgEtQIdl)->GrpAb,Map,Map,SeqEnum[AlgEtQElt]
{ //TODO returns Q,q,sigma,powers_zz_diagonally_inOA_via_zbOE
//- sigma_OA_mod_I is a function that given an OA-ideal I such that the quotient OA/I is killed by a power of p, it returns a reduction of the map induced by the Frobenius automorphism of (L\otimes_Q Qp)/Qp;
    }
    L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,A_as_vector_space_over_L_data,OA_as_abelian_group_data:=DieudonneAlgebraCommEndAlg(isog); //TODO need everything?
    _,p:=IsPrimePower(normPL);
    E:=DeligneAlgebra(isog);
    mAD,mWD,mAW,mAW_zbOE:=Explode(A_as_vector_space_over_L_data);
    D:=Codomain(mAD); //TODO needed?
    W:=Codomain(mAW);
    FOA,fOA,imageDeltaOE_inFOA:=Explode(OA_as_abelian_group_data);

    Q,mQ:=ResidueRing(OA,I);
    // m can be computed using the formula |OL/PL|^m = |OA/I|
    t,m:=IsPowerOf(#Q,normPL);
    assert t;
    //m:=30*m; printf "Warning increasing the precision\n";
    if m eq 0 then
        vprintf sigma,2 : "m=0 -> sigma is the identity on Q\n";
        //TODO fix this return
        return Q,mQ,hom<Q->Q | [Q.i : i in [1..Ngens(Q)]] >;
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
            frob:=frob^normPL;
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
    // - We need a sigma-equivariant presentation ZZ[zz]^s->>Q.
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
    return Q,mQ,sigma_Q,powers_zz_diagonally_inOA_via_zbOE;

    // TODO finish
//    if not assigned ??? then
//        A`???:=;
//    end if;
//    return A`;
end intrinsic;


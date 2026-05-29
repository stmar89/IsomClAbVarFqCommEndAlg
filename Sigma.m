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
declare attributes IsogenyClassFq : SigmaOnQuotientOfOA;

intrinsic SigmaOnQuotientOfOA(isog::IsogenyClassFq,I::AlgEtQIdl)->GrpAb,Map,Map
{Given an isogeny class isog and a fractional OA-ideal I of the maximal order OA of the DieudonneAlgebra A=L otims Eof isog, returns Q,mQ,sigma_Q where Q=OA/I, mQ:OA->Q and sigma_Q is the homorphism induced by the Frobenius automorphism of L. The output is cached in an attribute populated on demand.}
    if not assigned isog`SigmaOnQuotientOfOA then
        isog`SigmaOnQuotientOfOA:=AssociativeArray();
    end if;    
    if not IsDefined(isog`SigmaOnQuotientOfOA,I) then
        L,OL,PL,normPL,A,_,OA,_,_,A_as_vector_space_over_L_data,OA_as_abelian_group_data:=DieudonneAlgebraCommEndAlg(isog);
        _,p:=IsPrimePower(normPL);
        E:=DeligneAlgebra(isog);
        _,_,_,mAW_zbOE:=Explode(A_as_vector_space_over_L_data);
        W:=Codomain(mAW_zbOE);
        FOA,fOA,_:=Explode(OA_as_abelian_group_data);

        Q,mQ:=ResidueRing(OA,I);
        // m can be computed using the formula |OL/PL|^m = |OA/I|
        t,m:=IsPowerOf(#Q,normPL);
        assert t;
        //m:=30*m; printf "Warning increasing the precision\n";
        if m eq 0 then
            vprintf sigma,2 : "m=0 -> sigma is the identity on Q\n";
            isog`SigmaOnQuotientOfOA[I]:=<Q,mQ,hom<Q->Q | [Q.i : i in [1..Ngens(Q)]] >>;
        else
            if not assigned A`sigma_fin_prec or A`sigma_fin_prec[1] lt m then
                // - We chached in an attribute of A the automorphism of the finite ring OL/PL^m induced 
                //   by the Frobenius automorphism L\otimes Qp, which is constructed as follows:
                // - In OL, find an element 'zeta' congruent mod PL^m to an inertial element (=uniformizer) of OLp
                //   by taking successive q-powers of the image 'frob' of a generator of (OL/PL)^*
                //   until the sequence stabilizes (this approximation method seems well known 
                //   Reference: Magma Documentation, Example RngLoc_unram-ext (H49E13).
                // - We create an auxiliary number field LL<zz>, isomorphic to L via zz:->zeta.
                // - This isomorphism induces an isomorphism of finite rings OL/PL^m = ZZ[zz]/p^m*ZZ[zz].
                // - By construction zz:->zz^p induces (a conjugate of) the Frobenius aut on ZZ[zz]/p^m*ZZ[zz].
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
                A`sigma_fin_prec:=<m,F,sigma_F,LL,LLtoL,imgs_zz>;
            end if;
            _,F,sigma_F,LL,LLtoL:=Explode(A`sigma_fin_prec);
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
            isog`SigmaOnQuotientOfOA[I]:=<Q,mQ,sigma_Q>;
            if GetAssertions() ge 2 then
                for J in [J:J in Keys(isog`SigmaOnQuotientOfOA)|J ne I and J subset I] do
                    QJ,mQJ,sigma_QJ:=Explode(isog`SigmaOnQuotientOfOA[J]);
                    assert forall{QJ.i:i in [1..Ngens(QJ)]|QJ.i@sigma_QJ@@mQJ@mQ eq QJ.i@@QJ@mQ@sigma_Q};
                end for;
            end if;
        end if;
    end if;
    return Explode(isog`SigmaOnQuotientOfOA[I]);
end intrinsic;


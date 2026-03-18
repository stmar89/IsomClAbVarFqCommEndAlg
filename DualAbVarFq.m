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
// Copyright 2026, S. Marseglia
/////////////////////////////////////////////////////

declare attributes AbelianVarietyFq : DualAbVarFq;

declare attributes IsogenyClassFq : glueing_gen_deligne_module_data_dual;

intrinsic DualAbelianVarietyCommEndAlg(AV::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl
{Given an abelian variety over Fq with commutative endomorphism algebra, returns the generalized deligne module of the dual abelian variety.}
    if not assigned AV`DualAbVarFq then
        // If M is a WR{F,V}-ideal representing the local-local part of the p-divisible group
        // of the abelian variety AV, then the local-local part of the p-divisible group of the
        // dual abelian variety AV^v is represented by the WR{F,V}-ideal M^v which is defined by
        //      M^v = 1/delta * bar(M)^t, where ^t denotes the dual with respect to the Trace(A/L).
        // The element delta is constructed from alpha in the intrinsic _AlphaAtPrecision, used to
        // compute the semilinear operator F and V, at finite precision.
        
        isog:=IsogenyClass(AV);
        if not assigned isog`glueing_gen_deligne_module_data_dual then
            isog`glueing_gen_deligne_module_data_dual:=AssociativeArray();
        end if;
        R:=ZFVOrder(isog);

        mult_part,locloc_part,inv_part,_:=IsomDataCommEndAlg(AV);
        if not IsDefined(isog`glueing_gen_deligne_module_data_dual,<mult_part,locloc_part>) then
            if not assigned isog`glueing_gen_deligne_module_data 
                or not IsDefined(isog`glueing_gen_deligne_module_data,<mult_part,locloc_part>) then
                _,_:=GeneralizedDeligneModule(AV);
            end if;
            I,M:=Explode(isog`glueing_gen_deligne_module_data[<mult_part,locloc_part>]);

            q:=FiniteField(AV);
            p:=CharacteristicFiniteField(AV);
            L,_,PL,_,A,pi_A,_,Delta_map,WR,_,Delta_inverse_ideal,_,_,A_as_vector_space_over_L_data,bar_onA:=DieudonneAlgebraCommEndAlg(isog);
            mAD,mLdD,mALd:=Explode(A_as_vector_space_over_L_data);
            Ld:=Codomain(mALd);
            // - Ld and D are both L-vector spaces of dimension d:=dim_L(A).
            // - mAD is the L-linear isomorphism  that represents A as \prod_i L[x]/g_i where h=\prod_i g_i in L[x], 
            // that is, the i-th component L[x]/g_i is seen as an L-vector space using the power basis.
            // - Ld is the KSpace L^d.
            // - mLdD is the isomorphism Ld->D where the image of the canonial basis is given by 
            //   the images of the powers of pi in D.
            // - mALd = is the composition of mAD with mLdD^-1

            // We convert M into a Lattice over W.
            // Once we compute the right Gram matrix, we can take the dual with respect to that.
            L_basis_ofA:=[ pi_A^i : i in [0..Dimension(Ld)-1] ];
            TrAL:=map<A->L|x:->Trace(Matrix([mALd(x*b):b in L_basis_ofA]))>;
            zbM:=ZBasis(M);
            zbM_inLd:=[mALd(z):z in zbM];
            M_lat:=NumberFieldLattice(zbM_inLd);
            bM_lat:=Basis(M_lat); //over W
            assert M eq Ideal(WR,&cat[[(bb[i]*c)@@mALd:c in Basis(cc[i])] : i in [1..#bb]]) 
                    where bb:=Basis(M_lat) where cc:=CoefficientIdeals(M_lat);
            bM_lat_inA:=[b@@mALd:b in bM_lat];
            Gram_M:=MatrixRing(L,Dimension(Ld))![TrAL(x*y):x,y in bM_lat_inA];
            M_lat:=NumberFieldLattice(bM_lat : Gram:=Gram_M);
            Mt_lat:=Dual(M_lat);
            assert forall{i:i,j in [1..#Basis(M_lat)]| TrAL(Basis(M_lat)[i]@@mALd*Basis(Mt_lat)[j]@@mALd) eq KroneckerDelta(i,j)};
            ci:=CoefficientIdeals(Mt_lat);
            bb:=Basis(Mt_lat);
            zb_Mt_lat_inLd:=[z*bb[i]:z in Basis(ci[i]),i in [1..#bb]]; 
            gens_Mt:=[ (Ld!g)@@mALd : g in zb_Mt_lat_inLd ];
            gens_Mv:=[ bar_onA(g) : g in gens_Mt ];

            if IsOrdinary(isog) then
                delta:=One(A);
            else
                if not assigned isog`delta_Hilbert90 then
                    error "Rerun the computation of the isomorphism classes with the DualsCompatible vararg set to true";
                end if;
                delta:=isog`delta_Hilbert90;
            end if;
            Mv:=bar_onA(delta^-1)*Ideal(WR,gens_Mv);

            // We compute Iv by glueing K:=Delta^-1(Mv) and J:=bar(I)^t everywhere else.
            J:=TraceDualIdeal(ComplexConjugate(I));
            K:=pPartDeltaInverseIdeal(isog,Mv);

// FIXME if J and K are locally isomorphic at p, we replace Mv and K
// This is very hack-y...if it gives good results, we should streamline the procedure.
cc:=ColonIdeal(J,K);
//pp:=PrimesAbove(p*Order(J));
//test:=forall{P:P in pp|1 in cc*ColonIdeal(K,J)+P};
PP:=PrimesAbove(p*MultiplicatorRing(J));
cc:=MultiplicatorRing(J)!!cc;
test:=forall{P:P in PP|Index(Order(P),P) eq Index(cc,cc*P)};
if test then
    gs:=LocalGenerators(cc,PP);
    assert #gs eq 1;
    K:=gs[1]*K;
    Mv:=Delta_map(gs[1])*Mv;
    // this leads to Iv eq J
end if;

            aa:=K+J;
            bb:=K meet J;
            ind:=Index(aa,bb);
            // There can be many primes in the support of (aa/bb).
            // For the ones coprime with p, we can just work with indices and rational primes.
            k:=Valuation(ind,p);
            pk:=p^k;
            ind_coprime_p:=ind div pk;
// FIXME OLD code
//            if k eq 0 then
//                Iv:=J;
//            else
//                ann:=ColonIdeal(bb+pk*aa,aa) meet OneIdeal(R); // ann of(aa/bb)_p=aa/(bb+p^k*aa)
//                supp:=PrimesAbove(ann);
//                _,P_ll,_:=PrimesOfZFVAbove_p(isog); // the unique local-local prime of R
//                assert #P_ll eq 1;
//                P_ll:=P_ll[1];
//                if P_ll notin supp then
//                    Iv_p:=J;
//                elif #supp eq 1 then // supp=[P_ll]
//                    Iv_p:=K;
//                else
//                    Exclude(~supp,P_ll);
//                    // For each P in supp we need k such that P^k*aa_P < bb_P.
//                    // k_ll is an integer satisfying P_ll^k_ll aa_(P_ll) < bb_(P_ll).
//                    // We do the same for all other Ps in supp.
//                    // 
//                    // This happens precisely when k_P geq l_P, where l_P is the length of aa/bb at P.
//                    // This can be bounded from the formula:
//                    // |aa/bb| = prod_(P in supp cup P_ll) |R/P|^l_P ,
//                    // which gives:
//                    // l_P leq (val_p(ind) / f_P) where p is the rational prime in P and f_P is the inertia degree of P.
//                    k_ll:=Ceiling(Valuation(ind,p)/f_P) where _,p,f_P:=IsPrimePower(Index(R,P_ll));
//                    ks_supp:=[Ceiling(Valuation(ind,p)/f_P) where _,p,f_P:=IsPrimePower(Index(R,P)):P in supp];
//                    Iv_p:=P_ll^k_ll * J + &*[supp[i]^ks_supp[i]:i in [1..#supp]]*K;
//                end if;
//                Iv:=pk*J+ind_coprime_p*Iv_p;
//            end if;
// FIXME The commented code above glues K at the local-local part and J everywhere else.
//       This is not the condition we impose on the GeneralizedDeligneModule, where the glueing is a p.A
//       The next line does exactly that.
            Iv:=pk*J+ind_coprime_p*K;
            isog`glueing_gen_deligne_module_data_dual[<mult_part,locloc_part>]:=<Iv,Mv>;
        end if;
        Iv,Mv:=Explode(isog`glueing_gen_deligne_module_data_dual[<mult_part,locloc_part>]);
        inv_part_v:=R!!ComplexConjugate(Inverse(inv_part));
        IIv:=Iv*inv_part_v;
        MMv:=Mv*DeltaIdeal(isog,inv_part_v);
        AV`DualAbVarFq:=<IIv,MMv>;
    end if;
    return Explode(AV`DualAbVarFq);
end intrinsic;

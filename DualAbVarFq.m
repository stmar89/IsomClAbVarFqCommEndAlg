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

intrinsic TraceAL(isog::IsogenyClassFq)->Map
{Given an isogeny class isog with commutative endomorphism algebra and DieuddonneAlgebra A=E\otimes L returns the Trace from A to L.}
    if not assigned isog`TraceAL then
        L,_,_,_,A,pi_A,_,_,_,A_as_vector_space_over_L_data:=DieudonneAlgebraCommEndAlg(isog);
        _,_,mALd:=Explode(A_as_vector_space_over_L_data);
        Ld:=Codomain(mALd);
        // - Ld and D are both L-vector spaces of dimension d:=dim_L(A).
        // - mAD is the L-linear isomorphism  that represents A as \prod_i L[x]/g_i where h=\prod_i g_i in L[x], 
        // that is, the i-th component L[x]/g_i is seen as an L-vector space using the power basis.
        // - Ld is the KSpace L^d.
        // - mLdD is the isomorphism Ld->D where the image of the canonial basis is given by 
        //   the images of the powers of pi in D.
        // - mALd = is the composition of mAD with mLdD^-1

        L_basis_ofA:=[ pi_A^i : i in [0..Dimension(Ld)-1] ];
        TrAL:=map<A->L|x:->Trace(Matrix([mALd(x*b):b in L_basis_ofA]))>;
        isog`TraceAL:=TrA;
    end if;
    return isog`TraceAL;
end intrinsic;

intrinsic TraceALDualIdeal(isog::IsogenyClassFq,M::AlgEtQIdl)->AlgEtQIdl
{Given an isogeny class isog with commutative endomorphism algebra and DieuddonneAlgebra A=E\otimes L, and a fractional ideal M in A, over the order S, returns the fractional S-ideal dual with respect to the Trace from A to L.}
    if not assigned M`TraceALDualIdeal then
        L,_,_,_,A,pi_A,_,_,_,A_as_vector_space_over_L_data:=DieudonneAlgebraCommEndAlg(isog);
        _,_,mALd:=Explode(A_as_vector_space_over_L_data);
        Ld:=Codomain(mALd);
        // We convert M into a Lattice over W.
        // Once we compute the right Gram matrix, we can take the dual with respect to that.
        S:=Order(M);
        zbM:=ZBasis(M);
        zbM_inLd:=[mALd(z):z in zbM];
        M_lat:=NumberFieldLattice(zbM_inLd);
        bM_lat:=Basis(M_lat); //over W
        assert M eq Ideal(S,&cat[[(bb[i]*c)@@mALd:c in Basis(cc[i])] : i in [1..#bb]]) 
                where bb:=Basis(M_lat) where cc:=CoefficientIdeals(M_lat);
        bM_lat_inA:=[b@@mALd:b in bM_lat];
        TrAL:=TraceAL(isog);
        Gram_M:=MatrixRing(L,Dimension(Ld))![TrAL(x*y):x,y in bM_lat_inA];
        M_lat:=NumberFieldLattice(bM_lat : Gram:=Gram_M);
        Mt_lat:=Dual(M_lat);
        assert forall{i:i,j in [1..#Basis(M_lat)]|
                      TrAL(Basis(M_lat)[i]@@mALd*Basis(Mt_lat)[j]@@mALd) eq KroneckerDelta(i,j)};
        ci:=CoefficientIdeals(Mt_lat);
        bb:=Basis(Mt_lat);
        zb_Mt_lat_inLd:=[z*bb[i]:z in Basis(ci[i]),i in [1..#bb]]; 
        gens_Mt:=[ (Ld!g)@@mALd : g in zb_Mt_lat_inLd ];
        Mt:=Ideal(S,gens_Mt);
        M`TraceADualIdeal:=Mt;
    end if;
    return M`TraceALDualIdeal;
end intrinsic;

intrinsic DualAbelianVarietyCommEndAlg(AV::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl
{Given an abelian variety over Fq with commutative endomorphism algebra, returns the generalized deligne module of the dual abelian variety.
//TODO
}
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

        away_from_p_part,at_p_part,inv_part,_:=IsomDataCommEndAlg(AV);
        if not IsDefined(isog`glueing_gen_deligne_module_data_dual,<away_from_p_part,at_p_part>) then
            p:=CharacteristicFiniteField(AV);
            if not assigned isog`glueing_gen_deligne_module_data 
                or not IsDefined(isog`glueing_gen_deligne_module_data,<away_from_p_part,at_p_part>) then
                _,_,slopes:=GeneralizedDeligneModule(AV);
                require slopes eq "all" : "rerun the computation using slopes:=\"all\"";
            end if;
            I,M,slopes:=Explode(isog`glueing_gen_deligne_module_data[<away_from_p_part,at_p_part>]);
            require slopes eq "all" : "rerun the computation using slopes:=\"all\"";
            Mt:=TraceALDualIdeal(isog,M);
            if IsOrdinary(isog) then
                delta_inv:=One(A);
            else
                if not assigned isog`delta_inv then
                    error "Rerun the computation of the isomorphism classes with the DualsCompatible vararg set to true"; //TODO update this error
                end if;
                delta_inv:=isog`delta_inv;
            end if;
            bar_onA:=BarOnDieudonneAlgebra(isog);
            Mv:=BarOnIdeal(isog,Mt);
            Mv:=bar_onA(delta_inv)*Ideal(WR,gens_Mv);

            // We compute Iv by glueing K:=Delta^-1(Mv) at p and J:=bar(I)^t everywhere else.
            J:=TraceDualIdeal(ComplexConjugate(I));
            K:=DeltaInverseIdealpPart(isog,Mv);

            aa:=K+J;
            bb:=K meet J;
            ind:=Index(aa,bb);
            // There can be many primes in the support of (aa/bb).
            // For the ones coprime with p, we can just work with indices and rational primes.
            k:=Valuation(ind,p);
            pk:=p^k;
            ind_coprime_p:=ind div pk;
            Iv:=pk*J+ind_coprime_p*K;
            isog`glueing_gen_deligne_module_data_dual[<away_from_p_part,at_p_part>]:=<Iv,Mv>;
        end if;
        Iv,Mv:=Explode(isog`glueing_gen_deligne_module_data_dual[<away_from_p_part,at_p_part>]);
        inv_part_v:=ZFVOrder(isog)!!ComplexConjugate(Inverse(inv_part));
        IIv:=Iv*inv_part_v;
        MMv:=Mv*DeltaIdeal(isog,inv_part_v);
        AV`DualAbVarFq:=<IIv,MMv>;
    end if;
    return Explode(AV`DualAbVarFq);
end intrinsic;

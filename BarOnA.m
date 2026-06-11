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

declare attributes IsogenyClassFq : BarOnDieudonneAlgebra;
declare attributes AlgEtQOrd      : Bar;
declare attributes AlgEtQIdl      : Bar;

/////////////////////////////////////////////////////
// Bar on Dieudonne Algebra
/////////////////////////////////////////////////////

intrinsic BarOnDieudonneAlgebra(isog::IsogenyClassFq)->Map
{Given an isogeny class isog, returns the étale algebra automorphism of the DieudonneAlgebra A=E \otimes L induced by the CM-conjugation of the DeligneAlgebra E of isog.}
    if not assigned isog`BarOnDieudonneAlgebra then
        q:=FiniteField(isog);
        L,_,_,_,A,pi_A,_,_,_,A_as_vector_space_over_L_data:=DieudonneAlgebraCommEndAlg(isog);
        _,_,mAW,_:=Explode(A_as_vector_space_over_L_data);
        W:=Codomain(mAW);
        // We need to apply the CM involution which is defined to be bar on E, and identity on L.
        assert2 forall{i: i in [1..Dimension(W)]| W.i@@mAW eq pi_A^(i-1)};
        L_basis_ofA_bar:=[ (q/pi_A)^i : i in [0..Dimension(W)-1] ];
        bar_onW:=iso<W->W|[mAW(b):b in L_basis_ofA_bar]>; //action of bar on L^2g
        bar_onA:=Hom(A,A,[b@mAW@bar_onW@@mAW:b in AbsoluteBasis(A)] : CheckMultiplicative:=true, CheckUnital:=true, ComputeInverse:=true); //bar:A->A
        assert2 forall{b:b in AbsoluteBasis(A) | bar_onA(bar_onA(b)) eq b }; // check that bar_onA is an involution
        assert2 forall{l:l in Basis(L) | bar_onA(x) eq x where x:=(W!([l] cat [L!0:i in [2..Dimension(W)]]))@@mAW}; // check that bar_onA is the identity on L; note the construction of simple tensors 1 \otimes l in E\otimes L=A.
        isog`BarOnDieudonneAlgebra:=bar_onA;
    end if;
    return isog`BarOnDieudonneAlgebra;
end intrinsic;

/////////////////////////////////////////////////////
// Bar on ideals and orders
/////////////////////////////////////////////////////

intrinsic BarOnOrder(isog::IsogenyClassFq,S::AlgEtQOrd)->AlgEtQOrd
{Given an order S in the DieudonneAlgebra of isog, returns the order bar(S).}
    if not assigned S`Bar then
        bar:=BarOnDieudonneAlgebra(isog);
        zbSb:=[bar(z):z in ZBasis(S)];
        if forall{z:z in zbSb|z in S} then
            S`Bar:=S;
        else
            Sb:=Order(zbSb);
            S`Bar:=Sb;
        end if;
    end if;
    return S`Bar;
end intrinsic;

intrinsic BarOnIdeal(isog::IsogenyClassFq,I::AlgEtQIdl)->AlgEtQIdl
{Given a fractional ideal I of some order S in the DieudonneAlgebra of isog, returns the fractional bar(S)-ideal bar(I).}
    if not assigned I`Bar then
        bar:=BarOnDieudonneAlgebra(isog);
        zbIb:=[bar(z):z in ZBasis(I)];
        if forall{z:z in zbIb|z in I} then
            I`Bar:=I;
        else
            Sb:=BarOnOrder(isog,Order(I));
            Ib:=Ideal(Sb,zbIb);
            I`Bar:=Ib;
        end if;
    end if;
    return I`Bar;
end intrinsic;

/*

    SetDebugOnError(true);
    SetAssertions(2);

    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    fld:="~/IsomClAbVarFqCommEndAlg/examples/";
    PP<x>:=PolynomialRing(Integers());
    check:=Split(Pipe("ls " cat fld,"r"));
    inputs:=[
    <(x^2-2*x+4)*(x^2+2*x+4),"2.4.a_e">,
    <x^6 + 11*x^5 + 60*x^4 + 208*x^3 + 480*x^2 + 704*x + 512,"3.8.l_ci_ia">,
    <x^8+x^7+x^6+4*x^5-4*x^4+16*x^3+16*x^2+64*x + 256,"4.4.b_b_e_ae">,
    <x^8 - 6*x^7 + 18*x^6 - 36*x^5 + 68*x^4 - 144*x^3 + 288*x^2 - 384*x + 256,"4.4.ag_s_abk_cq">,
    <x^6 - x^5 - 3*x^4 + 45*x^3 - 27*x^2 - 81*x + 729,"3.9.ab_ad_bt">
    ];

    for input in inputs do
        h,file:=Explode(input);
        printf "%o\n",file;
        assert IsSquarefree(h);
        isog:=IsogenyClass(h);
        bar:=BarOnDieudonneAlgebra(isog);
        _,_,_,_,_,_,_,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        oo:=OverOrders(WR);
        for S in oo do
            if BarOnOrder(isog,S) eq S then
                p0,p01,p1:=PrimesOfSAbove_p(isog,S);
                assert 
                forall{P:P in p0|#[Q:Q in p01|BarOnIdeal(isog,P) eq Q] eq 0 and #[Q:Q in p1|BarOnIdeal(isog,P) eq Q] eq 1}
                and
                forall{P:P in p1|#[Q:Q in p01|BarOnIdeal(isog,P) eq Q] eq 0 and #[Q:Q in p0|BarOnIdeal(isog,P) eq Q] eq 1}
                and
                forall{P:P in p01|#[Q:Q in p01|BarOnIdeal(isog,P) eq Q] eq 1 and #[Q:Q in p0|BarOnIdeal(isog,P) eq Q] eq 0
                                                                 and #[Q:Q in p1|BarOnIdeal(isog,P) eq Q] eq 0};
            else
                p0,p01,p1:=PrimesOfSAbove_p(isog,S);
                p0b,p01b,p1b:=PrimesOfSAbove_p(isog,BarOnOrder(isog,S));
                assert 
                forall{P:P in p0b|#[Q:Q in p01|BarOnIdeal(isog,P) eq Q] eq 0 and #[Q:Q in p1|BarOnIdeal(isog,P) eq Q] eq 1}
                and
                forall{P:P in p1b|#[Q:Q in p01|BarOnIdeal(isog,P) eq Q] eq 0 and #[Q:Q in p0|BarOnIdeal(isog,P) eq Q] eq 1}
                and
                forall{P:P in p01b|#[Q:Q in p01|BarOnIdeal(isog,P) eq Q] eq 1 and #[Q:Q in p0|BarOnIdeal(isog,P) eq Q] eq 0
                                                                 and #[Q:Q in p1|BarOnIdeal(isog,P) eq Q] eq 0};

            end if;
        end for;
    end for;

*/

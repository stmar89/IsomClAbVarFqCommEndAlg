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

declare verbose Delta_scaling,3;

declare attributes AlgEtQIdl : Delta_inverse_ideal,
                               Delta_inverse_ppart,
                               Delta_ideal;

intrinsic DeltaIdeal(isog::IsogenyClassFq, I::AlgEtQIdl)->AlgEtQIdl
{Given a fractional Z[pi,q/pi]-ideal I in the DeligneAlgebra of isog, returns the WR-ideal Delta(I) in the DiudonneAlgebra.}
    if not assigned I`Delta_ideal then
        _,_,_,_,_,_,_,Delta_map,WR:=DieudonneAlgebraCommEndAlg(isog);
        I`Delta_ideal:=Ideal(WR,[Delta_map(z):z in ZBasis(I)]);
    end if;
    return I`Delta_ideal;
end intrinsic;

intrinsic DeltaInverseIdeal(isog::IsogenyClassFq, I::AlgEtQIdl)->AlgEtQIdl
{Given a fractional WR-ideal I in the DieudonneAlgebra of isog, returns Delta^-1(I), which is a Z[pi,q/pi]-ideal in the DeligneAlgebra.}
        if not assigned I`Delta_inverse_ideal then
            R:=ZFVOrder(isog);
            _,_,_,_,_,_,_,Delta_map,WR,_,_,OA_as_abelian_group_data:=DieudonneAlgebraCommEndAlg(isog);
            FOA,fOA,imageDeltaOE_inFOA:=Explode(OA_as_abelian_group_data);
            require Order(I) cmpeq WR : "The input ideal is not defined over WR";

            dI,d:=MakeIntegral(I);
            ZBasisLLL(dI);
            dI_inFOA:=sub<FOA | [fOA(z) : z in ZBasis(dI) ]>;
            // the next line can be very memory consuming
            meet_id:=dI_inFOA meet imageDeltaOE_inFOA;
            gens_dI_meet_DeltaOE:=[ (g@@fOA)@@Delta_map : g in Generators(meet_id) ];
            J:=(1/d)*Ideal(R,gens_dI_meet_DeltaOE);
            assert2 forall{z : z in ZBasis(J) | Delta_map(z) in I};
            I`Delta_inverse_ideal:=J;
        end if;
        return I`Delta_inverse_ideal;
end intrinsic;

intrinsic DeltaInverseIdealpPart(isog::IsogenyClassFq, I::AlgEtQIdl)->AlgEtQIdl
{Given a fractional WR-ideal I in the DieudonneAlgebra of isog, returns a Z[pi,q/pi]-ideal J in the DeligneAlgebra such that J_p = Delta^-1(I_p).}
    if not assigned I`Delta_inverse_ppart then
        R:=ZFVOrder(isog);
        E:=Algebra(R);
        _,_,_,_,A,_,_,Delta_map,WR:=DieudonneAlgebraCommEndAlg(isog);
        OA:=MaximalOrder(A);
        p:=CharacteristicFiniteField(isog);
        nus0,nus01,nus1:=PlacesOfQFAbove_p(isog);
        nus:=nus0 cat nus01 cat nus1;
        unifs:=UniformizersInQFAt_p(isog,nus);
        oOA:=Order(I)!!OneIdeal(OA);
        cc:=OA!!ColonIdeal(oOA,I);
        exps:=[];
        for nu in nus do
            M_nu:=Max([Valuation(cc,P) : P in PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)]);
            Append(~exps,M_nu);
        end for;
        dp:=&*[unifs[i]^exps[i]:i in [1..#nus]];
        dpI:=Delta_map(dp)*I;
        d:=Index(oOA+dpI,oOA);
        assert IsCoprime(d,p);
        d:=dp*d;
        dI:=Delta_map(d)*I;
        assert dI subset WR!!OneIdeal(OA);

        vp_ind:=Valuation(Index(oOA,dI),p);
        dI_ppart:=dI+p^vp_ind*oOA;
        I`Delta_inverse_ppart:=(1/d)*DeltaInverseIdeal(isog,dI_ppart);
        //if GetAssertions() ge 3 then
        //    //This test can be VERY Expensive
        //    DinvI:=DeltaInverseIdeal(isog,I);
        //    assert3 Index(DinvI+I`Delta_inverse_ppart,DinvI meet I`Delta_inverse_ppart) mod p ne 0;
        //end if;
    end if;
    return I`Delta_inverse_ppart;
end intrinsic;

intrinsic DeltaScaleInside(isog::IsogenyClassFq,J::AlgEtQIdl,Is::SeqEnum[AlgEtQIdl])->SeqEnum[AlgEtQIdl],RngIntElt
{Given an isogeny class isog, a fractional ideal J and a sequence of fractional ideals Is of the DieudonneAlgebra it returns a sequence IIs and an integer m0 such that for each i Is[i] is Delta-isomorphic to IIs[i], each IIs[i] is inside J, and m0=Max(Valuation(p,Index(J,IIs[i])) is small.}
    IIs:=Is;
    _,_,_,_,A,_,OA,Delta_map:=DieudonneAlgebraCommEndAlg(isog);
    nus0,nus01,nus1:=PlacesOfQFAbove_p(isog);
    nus:=nus0 cat nus01 cat nus1;
    unifs:=UniformizersInQFAt_p(isog,nus);
    p:=CharacteristicFiniteField(isog);

    pExponent:=function(A,B)
    // Given B c A, returns the vp(Exponent(Quotient(A,B))) without computing Quotient(A,B),
    // but only a quotient isomorphic to its p-part.
        vp_ind:=Valuation(Index(A,B),p);
        // now I only compute the quotient of the p-part.
        vp_exp:=Valuation(Exponent(Quotient(A,B+p^vp_ind*A)),p);
        return vp_exp;
    end function;

    Delta_scale_inside:=function(I,J)
    // given an OA-ideal WR!!J and a WR-ideal I, it finds an element x in E^* such that Delta(x)I c J.
    // This element is chosen so that [J:xI] will have a small p-adic valuation.
        vprintf Delta_scaling,1 : "Computing: colon ideal...";
        cc:=OA!!ColonIdeal(J,I);
        exps:=[];
        vprintf Delta_scaling,1 : "M_nu's";
        for nu in nus do
            M_nu:=Max([Valuation(cc,P) : P in PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)]);
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
        vprintf Delta_scaling,1 : "done";
        return yxI;
    end function;

    // We need to replace each ideal I in IIs with a Delta(E)-equivalent 
    // ideal s*I such that s*I < J so that the maximal value m0 of vp(exp(J/s*I)) is as small as possible.
    // The optimal s can be obtained by the function Delta_scale_inside above, which requires to compute the 
    // colon ideal (J:I) and its valuations at the places of A above p. This can be expensive.
    // So we first try to take s=p^ss where ss=pExponent(I+J,J) which is faster.
    // If this scaling does not increase m0, ther are good. Otherwise we use Delta_scale_inside.
    m0:=0; 
    for i in [1..#IIs] do
        I:=IIs[i];
        ZBasisLLL(I);
        D_scale:=true;
        if I subset J then
            if pExponent(J,I) le m0 then
                D_scale:=false;
            end if;
        else
            vprintf Delta_scaling,1 : "\nAttempting to pExp-scaling the %o-th ideal into J...",i;
            ss:=pExponent(I+J,J);
            x:=p^ss;
            xI:=x*I;
            y:=Index(xI+J,J);
            assert (y mod p) ne 0; // y coprime p
            yxI:=y*xI;
            assert yxI subset J;
            if pExponent(J,yxI) le m0 then
                vprintf Delta_scaling,1 : "\nsuccess...",i;
                D_scale:=false;
                vprintf Delta_scaling,1 : "ZBasisLLL...";
                ZBasisLLL(yxI);
                vprintf Delta_scaling,1 : "done";
                IIs[i]:=yxI;
            end if;
        end if;
        if D_scale then
            vprintf Delta_scaling,1 : "\nDelta-scaling the %o-th ideal into J...",i;
            I:=Delta_scale_inside(I,J);
            vpN:=pExponent(J,I);
            m0:=Max(m0,vpN);
            IIs[i]:=I;
        end if;
    end for;
    assert2 forall{I:I in IIs|I subset J};
    // The next assert tests that p^m0*J < I locally at p. Since I < J, this is equivalent to m0 ge val_p(exp(J/I))
    assert2 forall{I:I in IIs|Valuation(Index((p^m0)*J+I,I),p) eq 0};
    return IIs,m0;
end intrinsic;

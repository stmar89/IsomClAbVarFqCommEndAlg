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
        unifs:=UniformizersInQFAt_p(nus);
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
    end if;
    return I`Delta_inverse_ppart;
end intrinsic;


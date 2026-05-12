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

declare attributes AlgEtQIdl : DeltaInverse;

intrinsic DeltaInverseIdeal(isog::IsogenyClassFq, I::AlgEtQIdl)->AlgEtQIdl
{Given a fractional WR-ideal I in the DieudonneAlgebra of isog, returns Delta^-1(I), which is a Z[F,V]-ideal in the DeligneAlgebra.}
        if not assigned I`DeltaInverse then
            R:=ZFVOrder(isog);
            _,_,_,_,_,_,_,Delta_map,WR,_,_,_,_,_,OA_as_abelian_group_data:=DieudonneAlgebraCommEndAlg(isog);
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
            I`DeltaInverse:=J;
        end if;
        return I`DeltaInverse;
end intrinsic;


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

declare attributes AbelianVarietyFq : IsomDataCommEndAlg;

/////////////////////////////////////////////////////
// Creation functions of AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic IsomDataCommEndAlg(A::AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl,AlgEtQIdl,AlgEtQOrd
{Given an abelian variety over Fq with commutative Fq-endomorphism algebra, returns the tuple <I,M,L,S> as defined in AbelianVarietyCommEndAlg.}
    return Explode(A`IsomDataCommEndAlg);
end intrinsic;

/////////////////////////////////////////////////////
// Creation functions of AbelianVarietyFq
/////////////////////////////////////////////////////

intrinsic AbelianVarietyCommEndAlg(isog::IsogenyClassFq,tup:Tup)->AbelianVarietyFq
{Given an isogeny class of abelian varieties over Fq with commutative Fq-endomorphism algebra, i.e. whose Weil polynomial is squarefree, and a tuple <I,M,L,S> where
- I is a fractional ideal over the ZFVOrder of isog;
- M is a WR\{F,V\}-ideal (see DieudonneAlgebraCommEndAlg for definitions);
- S in an overorder of the ZFVOrder;
- L is an invertible fractional S-ideal;
returns the unique abelian variety in isog with EndomorphismRing S whose l-Tate modules are isomorphic to I (for all l neq p), the étale-local and local-étale part of the Dieudonné module are determined by I, while the local-local part is determined by M, and L determines its position in the orbit of the class group of S acting on the local information just described.}
    require IsSquarefree(isog) : "The isogeny class needs to have squarefree Weil polynomial.";
    R:=ZFVOrder(isog);
    I,M,L,S:=Explode(tup);
    require R eq Order(I): "I is not a ZFV-ideal.";
    require R subset S : "S cannot be an endomorphism ring.";
    require Order(L) eq S and IsInvertible(L): "L needs to be an invertible ideal of S";
    if GetAssertions() ge 2 then
        _,_,_,_,_,_,_,Delta_map,WR:=DieudonneAlgebraCommEndAlg(isog);
        require Order(M) eq WR : "M needs to be a WR-ideal";
        if GetAssertions() ge 3 then
            //TEST consistency of S with the local data. Very time consuming
            E:=Algebra(R);
            places_0,places_01,places_1:=PrimesOfZFVAbove_p(isog);
            places_away_01:=SingPrimesOfZFVAwayFrom_p(isog) cat [P:P in places_0|not IsInvertible(P)] cat [P:P in places_0|not IsInvertible(P)];
            OE:=MaximalOrder(E);
            end_test:=[];
            for T in OverOrders(R) do
                mT:=R!!OneIdeal(T);
                if #places_away_01 gt 0 then
                    IT:=R!!(T!!I);
                    I_IT:=I+IT;
                    sendsItoI:=forall{P : P in places_away_01 | I_IT eq I + P*I_IT }; 
                else
                    sendsItoI:=true; 
                end if;
                if #places_01 gt 0 then
                    MT:=Ideal(WR,[ Delta_map(t)*m : t in ZBasis(T) , m in ZBasis(M) ]);
                    M_MT:=M+MT;
                    assert assigned WR`PrimesOfSlopeIn01;
                    sendsMtoM:=forall{ P : P in WR`PrimesOfSlopeIn01 | M_MT eq M + P*(M_MT) };
                    // M = MT at (0,1)
                else
                    sendsMtoM:=true;
                end if;
                if sendsItoI and sendsMtoM then
                    Append(~end_test,T);
                end if;
            end for;
            require S eq Order(&cat[ ZBasis(T) : T in end_test ]) : "The local info provided by I and M determine and order which is different from S.";
        end if;
    end if;
    AV:=New(AbelianVarietyFq);
    AV`IsogenyClass:=isog;
    AV`EndomorphismRing:=S;
    AV`IsomDataCommEndAlg:=tup;
    return AV;
end intrinsic;

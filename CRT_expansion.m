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

/////////////////////////////////////////////////////
// An expansion for ChineseRemainderTheoremFunctions
/////////////////////////////////////////////////////

/// Given a fractional $S$-ideal `J` and sequence `Is` of $N$ integral fractional $S$-ideals $I_1,\ldots,I_N$, pairwise coprime, returns a map $J \to J^N$ representing the natural isomorphism $J/I*J \to \frac{J}{I_1*J}\times \cdots \times \frac{J}{I_N*J}$, where $I=\prod_i I_i$, and a map $J^N \to J$ representing the inverse.  
intrinsic ChineseRemainderTheoremFunctions(J::AlgEtQIdl,Is::SeqEnum[AlgEtQIdl])-> Map,Map
{Given a fractional S-ideal J and sequence Is of N integral fractional S-ideals I_1,\ldots,I_N, pairwise coprime, returns a map J \to J^N representing the natural isomorphism J/I*J \to J/I_1*J x ... x J/I_N*J, where I=\prod_i I_i, and a map J^N \to J representing the inverse.}
    S:=Order(Is[1]);
    N:=#Is;
    require forall{i : i in [2..N] | Order(Is[i]) eq S} and Order(J) eq S:"the ideals must be of the same order";
    Q,q:=Quotient(J,&meet(Is)*J);
    quots:=[];
    maps:=<>;
    for I in Is do
        QI,qI:=Quotient(J,I*J);
        Append(~quots,QI);
        Append(~maps,qI);
    end for;
    D,embs,projs:=DirectSum(quots);
    assert IsIsomorphic(D,Q);
    isom:=iso<Q->D | [ &+[embs[j](maps[j](Q.i@@q)) : j in [1..#Is]] : i in [1..Ngens(Q)] ]>;
    // isom : J/&meet(Is)*J -> \prod_{I in Is} J/I*J
    // is the natural isomorphism of S modules.
    // The inverse (constructed by considering isom as an addive map) is automatically S-linear
    func1:=function(x)
        return [projs[j](isom(q(x)))@@maps[j] : j in [1..N] ];
    end function;
    func2:=function(as)
        assert forall{a:a in as|a in J};
        assert #as eq N;
        return (&+[embs[j](maps[j](as[j])) : j in [1..N] ])@@isom@@q;
    end function;
    II:=&meet(Is);
    assert forall{s : s in ZBasis(J) | func2(func1(s)) -s in J*II};
    return func1,func2;
end intrinsic;


/* TESTS

*/

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

// taken from AbVarFqIsogenies
declare attributes AlgEtQOrd:UnitsModTotPos,TotPosUnitsModUbarU;

// taken from AbVarFqIsogenies
intrinsic UnitsModTotPos(S::AlgEtQOrd)->SeqEnum[AlgEtQElt]
{Given an order S in a CM-etale algebra K returns a set of representative in K of the quotient S^*/S_+^*, where S_+^* is the subgroup of totally real totally positive units of S.}
    if not assigned S`UnitsModTotPos then
        U,u:=UnitGroup(S);
        Up:=TotallyRealPositiveUnitGroup(S);
        S`UnitsModTotPos:=[u(v):v in Transversal(U,Up)];
    end if;
    return S`UnitsModTotPos;
end intrinsic;

// taken from AbVarFqIsogenies
intrinsic TotPosUnitsModUbarU(S::AlgEtQOrd)->SeqEnum[AlgEtQElt]
{Given an order S in a CM-etale algebra K returns a set of representative in K of the quotient S_+^*/(S^* meet <u*\bar(u): u in S^*>, where S_+^* is the subgroup of totally real totally positive units of S.}
    if not assigned S`TotPosUnitsModUbarU then
        U,u:=UnitGroup(S);
        Up:=TotallyRealPositiveUnitGroup(S);
        if IsConjugateStable(S) then
            gens:=[Up!(U.i*ComplexConjugate(u(U.i))@@u): i in [1..Ngens(U)]];
            den:=sub<Up|gens>;
        else
            UK,uK:=UnitGroup(MaximalOrder(Algebra(S)));
            gens_inUK:=[(UK!(U.i)*(ComplexConjugate(u(U.i))@@uK)): i in [1..Ngens(U)]];
            den:=Up meet sub<UK|gens_inUK>;
        end if;
        trans:=Transversal(Up,den);
        S`TotPosUnitsModUbarU:=[u(t):t in trans];
    end if;
    return S`TotPosUnitsModUbarU;
end intrinsic;

intrinsic PrincipalPolarizationsUpToIsomorphism(AV::AbelianVarietyFq,PHI::AlgEtQCMType)->SeqEnum[AlgEtQElts]
{Given an abelian variety AV over a finite field Fq with commutative endomorphism algebra E and a CM-type PHI of E, it returns a sequence of totally imaginary elements of E representing the isomorphism classes of PHI-principal polarizations of AV, that is, we required them to be PHI-positive.}
    p:=CharacteristicFiniteField(AV);
    I,M:=GeneralizedDeligneModule(AV);
    Iv,Mv:=DualAbelianVarietyCommEndAlg(AV);
    
    S:=EndomorphismRing(AV);
    output:=[Algebra(S)|]; //empty list
    if not IsConjugateStable(S) then
        return output;
    end if;
    test,x0:=IsIsomorphic(Iv,I);
    if not test then
        return output;
    end if;
    assert x0*I eq Iv;

    _,_,_,_,_,_,_,Delta_map,WR,_,_,_,primes_of_S_of_slope_in_01,_,_:=DieudonneAlgebraCommEndAlg(IsogenyClass(AV));
    N:=Delta_map(x0)*M;
    A:=N+Mv;
    B:=N meet Mv;
    test:=forall{P:P in primes_of_S_of_slope_in_01(WR)| A eq P*A+B}; // are the local-local parts of A and B equal?
    if not test then
        return output;
    end if;

    homs:=Homs(PHI);
    trans:=UnitsModTotPos(S);
    for t in trans do
        lambda:=x0*t;
        if lambda eq -ComplexConjugate(lambda) and forall{phi:phi in homs| Im(phi(lambda)) gt 0} then
            output cat:=[lambda*u : u in TotPosUnitsModUbarU(S)];
            break t;
        end if;
    end for;
    return output;
end intrinsic;


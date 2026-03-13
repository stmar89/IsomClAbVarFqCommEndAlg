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

declare verbose Pols,3;

// the first 2 are taken from AbVarFqIsogenies
declare attributes AlgEtQOrd:UnitsModTotPos,TotPosUnitsModUbarU,TransversalQuotientUnitGroups;

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

intrinsic TransversalQuotientUnitGroups(T::AlgEtQOrd,S::AlgEtQOrd)->SeqEnum[AlgEtQElt]
{Returns a transversal of T^*/(S^* meet T^*). The ouput is stored in an attribute populated on demand.}
    hS:=myHash(S);
    if not assigned T`TransversalQuotientUnitGroups then
        T`TransversalQuotientUnitGroups:=AssociativeArray();
    end if;
    if not IsDefined(T`TransversalQuotientUnitGroups,hS) then
        if T subset S then
            T`TransversalQuotientUnitGroups[hS]:=[One(Algebra(T))];
        else
            UT,uT:=UnitGroup(T);
            US,uS:=UnitGroup(S);
            V:=UT meet US;
            assert V subset UT;
            T`TransversalQuotientUnitGroups[hS]:=[uT(x):x in Transversal(UT,V)];
        end if;
    end if;
    return T`TransversalQuotientUnitGroups[hS];
end intrinsic;

intrinsic PrincipalPolarizationsUpToIsomorphism(AV::AbelianVarietyFq,PHI::AlgEtQCMType)->SeqEnum[AlgEtQElts]
{Given an abelian variety AV over a finite field Fq with commutative endomorphism algebra E and a CM-type PHI of E, it returns a sequence of totally imaginary elements of E representing the isomorphism classes of PHI-principal polarizations of AV, that is, we required them to be PHI-positive.}
    p:=CharacteristicFiniteField(AV);
    I,M:=GeneralizedDeligneModule(AV);
    Iv,Mv:=DualAbelianVarietyCommEndAlg(AV);
    
    S:=EndomorphismRing(AV);
    output:=[Algebra(S)|]; //empty list
    if not IsConjugateStable(S) then
        vprintf Pols,1: "End is not conjugate stable.\n";
        return output;
    end if;

    test,x0:=IsIsomorphic(Iv,I);
    if not test then
        vprintf Pols,1: "Selfduality fails at the non-local-local part.\n";
        return output;
    end if;
    if test then
        assert x0*I eq Iv;
        T:=MultiplicatorRing(I);
        T_S:=TransversalQuotientUnitGroups(T,S);
        x0s:=[];
        _,_,_,_,_,_,_,Delta_map,WR,_,_,_,primes_of_S_of_slope_in_01,_,_:=DieudonneAlgebraCommEndAlg(IsogenyClass(AV));
        for v in T_S do
            x1:=x0*v;
            N:=Delta_map(x1)*M;
            B:=N meet Mv;
            test:=((Index(N,B) mod p ne 0) and (Index(Mv,B) mod p ne 0)); //faster then the next
            //FIXME the above test checks equality at p. If I want to check only the equality at (0,1), I should
            // uncomment the "if" below.
//            if not test then
//                A:=N+Mv;
//                test:=forall{P:P in primes_of_S_of_slope_in_01(WR)| A subset P*A+B}; // A=B at local-local parts?
//            end if;
            if test then
                Append(~x0s,x1);
            end if;
        end for;
    end if;
    if #x0s eq 0 then
        vprintf Pols,1: "Selfduality fails at the local-local part.\n";
        return output;
    end if;
    vprintf Pols,1: "We have %o selfduality.\n",#x0s;

    homs:=Homs(PHI);
    trans:=UnitsModTotPos(S);
    vprintf Pols,1 : "is there a symmetric selfduality?\t%o\n",exists{t:t in trans,x0 in x0s|lambda eq -ComplexConjugate(lambda) where lambda:=x0*t};
    vprintf Pols,1 : "is there a PHI-positive selfduality?\t%o\n",exists{t:t in trans,x0 in x0s|forall{phi:phi in homs| Im(phi(lambda)) gt 0 where lambda:=x0*t}};
    vprintf Pols,1 : "do we a principal polarization?\t\t%o\n",exists{t:t in trans,x0 in x0s|lambda eq -ComplexConjugate(lambda) and forall{phi:phi in homs| Im(phi(lambda)) gt 0} where lambda:=x0*t};
    for x0 in x0s do
        for t in trans do
            lambda:=x0*t;
            if lambda eq -ComplexConjugate(lambda) and forall{phi:phi in homs| Im(phi(lambda)) gt 0} then
                output cat:=[lambda*u : u in TotPosUnitsModUbarU(S)];
                break t;
            end if;
        end for;
    end for;

    return output;
end intrinsic;

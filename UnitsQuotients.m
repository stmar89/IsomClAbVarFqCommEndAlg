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

declare verbose UnitGroupQuotients,3;

declare attributes AlgEtQOrd      : UnitGroupQuotientAtSlope, 
                                    UnitGroupQuotientAtSlopeFixedBySigma;

declare attributes IsogenyClassFq : units_quotient_fixed_sigma_WR_gens;

intrinsic UnitGroupQuotientAtSlope(isog::IsogenyClassFq,S::AlgEtQOrd,slopes::MonStgElt)->GrpAb,Map,AlgEtQIdl
{Given an isogeny class isog, an order S in the DieudonneAlgebra and string variable slopes with values "0","(0,1)","1" or "all", returns the triple U,u,I where U=OA'^*/S'^*, where ' denotes the 0,(0,1),1 or p-part, the map u:U->OA 
together with an ideal I of OA such that OA'/S' = (OA/I)/(S/I).}
    require slopes in {"0","1","(0,1)","all"} : "Invalid parameter slopes";
    if not assigned S`UnitGroupQuotientAtSlope or S`UnitGroupQuotientAtSlope[4] ne slopes then
        primes_0_S,primes_01_S,primes_1_S:=PrimesOfSAbove_p(isog,S);
        if slopes eq "0" then
            primes_S:=primes_0_S;
        elif slopes eq "1" then
            primes_S:=primes_1_S;
        elif slopes eq "(0,1)" then
            primes_S:=primes_01_S;
        elif slopes eq "all" then
            primes_S:=primes_0_S cat primes_01_S cat primes_1_S;
        end if;
        _,_,_,_,_,_,OA:=DieudonneAlgebraCommEndAlg(isog);
        p:=CharacteristicFiniteField(isog);

        ff:=Conductor(S);
        primes_S_above_ff:=[ P : P in primes_S | ff subset P];
        if #primes_S_above_ff eq 0 then
            U:=FreeAbelianGroup(0);
            // with test
            trivial_preimage:=function(y)
                assert2 forall{ P : P in primes_S_above_ff | not y in P };
                return Zero(U);
            end function;
            u:=map<U->Algebra(S) | x:->One(S), y:->trivial_preimage(y)>;
            // without test
            //u:=map<U->Algebra(S) | x:->One(S), y:->Zero(U)>;
            return U,u,OneIdeal(OA);
        end if;
        indff:=Index(S,ff);
        assert2 forall{P : P in primes_S_above_ff | indff mod Index(S,P) eq 0 };
        ks:=[ 10 + (Valuation(indff,p) div Valuation(Index(S,P),p)) : P in primes_S_above_ff ];
        prod:=&*([ primes_S_above_ff[i]^ks[i] : i in [1..#primes_S_above_ff]]);
        ff_prod:=ff+prod;
        assert not 1 in ff_prod;
        assert2 OneIdeal(S) meet S!!(OA!!ff_prod) eq ff_prod;        
      
        I:=OA!!(ff_prod);
        R,r:=ResidueRingUnits(I); // R=(OA/I)^* , r:R->OA
        gens:=ResidueRingUnitsSubgroupGenerators(ff_prod); // gens of (S/ff_prod)^*
        U,u0:=quo<R | [ g@@r : g in gens]>;
        u:=map<U->Algebra(S) |  x:-> r(x@@u0), y:->u0(y@@r) >;
        if GetAssertions() ge 2 then
            gammas:=[u(g):g in U];
            assert2 forall{g:g in gammas|g in OA};
            assert2 #{g@@u:g in gammas} eq #U;
            nu0,nu01,nu1:=PlacesOfQFAbove_p(isog);
            if slopes eq "all" then
                plE:=nu0 cat nu01 cat nu1;
            elif slopes eq "(0,1)" then
                plE:=nu01;
            end if;
            plA:=&cat[PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu):nu in plE];
            plA:=[P:P in plA|I subset P];
            assert2 forall{g:g in gammas,P in plA|g notin P};
        end if;
        S`UnitGroupQuotientAtSlope:=<U,u,I,slopes>;
    end if;
    U,u,I:=Explode(S`UnitGroupQuotientAtSlope);
    return U,u,I;
end intrinsic;

intrinsic UnitGroupQuotientAtSlopeFixedBySigma(isog::IsogenyClassFq,S::AlgEtQOrd,slopes::MonStgElt)->GrpAb,Map,SeqEnum[AlgEtQElt]
{Given an isogeny class isog, an order S in the DieudonneAlgebra and string variable slopes with values "0","(0,1)","1" or "all", returns the triple U,u where U=OA'^*/S'^*Delta(OE'^*), where ' denotes the 0,(0,1),1 or p-part, the map u:U->OA together a list of representatives in OA of U.}
    if not assigned S`UnitGroupQuotientAtSlopeFixedBySigma or S`UnitGroupQuotientAtSlopeFixedBySigma[4] ne slopes then
        _,_,_,_,A,_,OA,_,WR,sigma_OA_mod_I:=DieudonneAlgebraCommEndAlg(isog);
        if not assigned isog`units_quotient_fixed_sigma_WR_gens then
            fixed_pts_sigma:=function(T)
            // Given an order T in A, representing an order T' in A', 
            // which is stable by the action of sigma (eg. WR),
            // returns U,u,F,m where
            // - U=OA'^*/T'^*,
            // - u is a map u:U->OA giving representatives 
            // - F is the subgroup of elements of U=OA'^*/T'^* fixed by sigma
                U,u,I:=UnitGroupQuotientAtSlope(isog,T,slopes); //u:U->A
                Q,q:=ResidueRing(OA,I);
                sigma:=sigma_OA_mod_I(Q,q,A); // sigma: Q->Q
                id_sigma:=hom< U->U | [ U.i-(U.i@u@q@sigma@@q@@u) : i in [1..Ngens(U)]]>; //additive notation
                F:=Kernel(id_sigma);
                return U,u,F;
            end function;

            // only for WR: F = Delta(OE')^*W'R^*/W'R^* inside OA'^*/W'R^*
            U,u,F:=fixed_pts_sigma(WR);
            isog`units_quotient_fixed_sigma_WR_gens:=[u(F.i) : i in [1..Ngens(F)]];
            delete U,u,F;
        end if;

        U,u,I:=UnitGroupQuotientAtSlope(isog,S,slopes); //u:U=OA'^*/S'^* -> A
        fixed_pts_gens:=[ g@@u : g in isog`units_quotient_fixed_sigma_WR_gens];
        Q,q0:=quo<U|fixed_pts_gens>; //q0: U->U/F=Q
// alternative method
Q,q:=ResidueRing(OA,I);
sigma:=sigma_OA_mod_I(Q,q,A); // sigma: Q->Q
id_sigma:=hom< U->U | [ U.i-(U.i@u@q@sigma@@q@@u) : i in [1..Ngens(U)]]>; //additive notation
F:=Kernel(id_sigma);
Q,q0:=quo<U|F>;
// end alternative method
        q:=map<Q->Algebra(S) |  x:->u(x@@q0), y:->q0(y@@u) >;
//FIXME the alternative method does not remove the error.
// Question: is the way we construct representatives correct?
        gammas:=[q(x):x in Q];

if #gammas gt 1 then
    Join([
    Sprintf("[OA:S]=%o",Index(OA,S)),
    StripWhiteSpace("S=" cat Sprint(PrintSeqAlgEtQElt(ZBasis(S)))),
    StripWhiteSpace("F=" cat Sprint(Generators(F))),
    StripWhiteSpace("gens_F_OA=" cat Sprint(PrintSeqAlgEtQElt([u(g):g in Generators(F)])))
    ],"\n");
end if;

        S`UnitGroupQuotientAtSlopeFixedBySigma:=<Q,q,gammas,slopes>;

        vprintf UnitGroupQuotients : "\n#US,#USfixed,gammas in Q = %o,%o,%o\n",
                            #U,#Q,StripWhiteSpace(Sprint([g@@q:g in gammas]));
        if GetAssertions() ge 2 then
            assert2 forall{g:g in gammas|g in OA};
            nu0,nu01,nu1:=PlacesOfQFAbove_p(isog);
            if slopes eq "all" then
                plE:=nu0 cat nu01 cat nu1;
            elif slopes eq "(0,1)" then
                plE:=nu01;
            end if;
            plA:=&cat[PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu):nu in plE];
            //FIXME I think there is something wrong here:
            // I get a failed assert2 below (the second one) for 3.4.a_ad_c.m and 3.4.a_ad_c.
            // It occurs only #gammas>1, but not always. With "(0,1)", we always have #gamma=1.
            // If the assert2 does not fail, the size of the output with "all" is the same as with "(0,1)".
            // Also, the assert in IsomClassesDieudon... marked with a fixme does not fail either.
            // This suggests that gammas are not a set of representative of what the quotient we want to compute.
            assert2 forall{g:g in gammas,P in [P:P in plA|I subset P]|g notin P};
            //assert2 forall{g:g in gammas,P in plA|g notin P};
        end if;
    end if;
    Q,q,gammas:=Explode(S`UnitGroupQuotientAtSlopeFixedBySigma);
    return Q,q,gammas;
end intrinsic;

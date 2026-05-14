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

declare attributes IsogenyClassFq : SingPrimesOfZFVAwayFrom_p,
                                    PlacesOfQFAbove_p,
                                    PrimesOfZFVAbove_p,
                                    PlacesOfDieudonneAlgebraAbove_p,
                                    PlacesOfDieudonneAlgebraSortedBySigmaAbove_p;

declare attributes AlgEtQOrd :      PrimesOfSAbove_p;

declare attributes AlgEtQIdl :      Slope;

/////////////////////////////////////////////////////////////////////////
/////////////////////// Primes in Deligna Algebra ///////////////////////
/////////////////////////////////////////////////////////////////////////

intrinsic SingPrimesOfZFVAwayFrom_p(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl]
{Returns the singular maximal ideals of the ZFVOrder of isog which do not contian p.}
    if not assigned isog`SingPrimesOfZFVAwayFrom_p then
        p:=CharacteristicFiniteField(isog);
        isog`SingPrimesOfZFVAwayFrom_p:=[ L : L in SingularPrimes(ZFVOrder(isog)) | not p in L ];
    end if;
    return isog`SingPrimesOfZFVAwayFrom_p;
end intrinsic;

intrinsic PrimesOfZFVAbove_p(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]
{Returns 3 sequences of maximal ideals of the ZFVOrder of isog consisting, respectively, of the maximal ideals of slope 0, slope in the open interval (0,1) and slope 1, where here with slope of P we mean the slope of any maximal ideal of the maximal order containing P.} 
    if not assigned isog`PrimesOfZFVAbove_p then
        ppOE_0,ppOE_01,ppOE_1:=PlacesOfQFAbove_p(isog);
        R:=ZFVOrder(isog);
        oR:=OneIdeal(R);
        ppR_0:=Setseq({ oR meet (R!!P) : P in ppOE_0 });
        ppR_01:=Setseq({ oR meet (R!!P) : P in ppOE_01 });
        ppR_1:=Setseq({ oR meet (R!!P) : P in ppOE_1 });
        assert #ppR_01 le 1 and ((#ppR_01 eq 0) eq (IsOrdinary(isog)));
        isog`PrimesOfZFVAbove_p:=<ppR_0,ppR_01,ppR_1>;
    end if;
    return Explode(isog`PrimesOfZFVAbove_p);
end intrinsic;

intrinsic PlacesOfQFAbove_p(isog:IsogenyClassFq)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]
{Returns a triple of sequences containing the maximal ideals with slope equal to 0, in (0,1), equal to 1, respectively} 
    if not assigned isog`PlacesOfQFAbove_p then
        p:=CharacteristicFiniteField(isog);
        places_E:=PlacesAboveRationalPrime(Algebra(ZFVOrder(isog)),p); //unsorted
        plE_sl0:=[];     //slope=0
        plE_sl_in01:=[]; //slope in (0,1)
        plE_sl1:=[];     //slope=1
        for P in places_E do
            sl:=Slope(P);
            if sl eq 0 then
                Append(~plE_sl0,P);
            elif sl eq 1 then
                Append(~plE_sl1,P);
            else
                Append(~plE_sl_in01,P);
            end if;
        end for;
        isog`PlacesOfQFAbove_p:=<plE_sl0,plE_sl_in01,plE_sl1>;
    end if;
    return Explode(isog`PlacesOfQFAbove_p);
end intrinsic;

///////////////////////////////////////////////////////////////////////////
/////////////////////// Places of Dieudonne Algebra ///////////////////////
///////////////////////////////////////////////////////////////////////////

intrinsic PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[AlgEtQIdl]
{Returns the places of the DieudonneAlgebra of isog above a the given place nu of the DeligneAlgebra.}
    if not assigned isog`PlacesOfDieudonneAlgebraAbove_p then
        isog`PlacesOfDieudonneAlgebraAbove_p:=AssociativeArray();
    end if;
    nu_Hash:=myHash(nu);
    if not IsDefined(isog`PlacesOfDieudonneAlgebraAbove_p,nu_Hash) then
        _,_,_,_,A,_,_,Delta_map:=DieudonneAlgebraCommEndAlg(isog);
        OA:=MaximalOrder(A);
        isog`PlacesOfDieudonneAlgebraAbove_p[nu_Hash]:=PrimesAbove(Ideal(OA,[Delta_map(z):z in ZBasis(nu)]));
    end if;
    return isog`PlacesOfDieudonneAlgebraAbove_p[nu_Hash];
end intrinsic;

intrinsic PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[AlgEtQIdl]
{Returns the places of the DieudonneAlgebra of isog above a the given place nu of the DeligneAlgebra, sorted by the action of the Frobenius automorphism sigma.}
    if not assigned isog`PlacesOfDieudonneAlgebraSortedBySigmaAbove_p then
        isog`PlacesOfDieudonneAlgebraSortedBySigmaAbove_p:=AssociativeArray();
    end if;
    nu_Hash:=myHash(nu);
    if not IsDefined(isog`PlacesOfDieudonneAlgebraSortedBySigmaAbove_p,nu_Hash) then
        _,_,_,_,A,_,_,Delta_map,_,sigma_OA_mod_I:=DieudonneAlgebraCommEndAlg(isog);
        // When we construct the WR{F,V}-ideals with maximal endomorphism ring,
        // we are assuming that the primes of A above each given place are sorted according to 
        // the action of sigma, as Waterhouse does. This does not make a difference if g_P is 1 or 2, 
        // like in all the examples in the paper.
        // More precisely, we will sort the ideal by [sigma^(g-1)(PP0),...,sigma(PP0),PP0],
        // where PP0 is an arbitrarily chosen ideal.
        pp:=PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu); //unsorted
        gP:=#pp;
        if gP gt 2 then
            // the following does nothing if gP is 1 or 2
            PP:=&*pp;
            Q,mQ:=ResidueRing(PP);
            PP0:=pp[1];
            gens:=[mQ(x):x in Generators(PP0)];
            ss:=sigma_OA_mod_I(Q,mQ,A);
            output:=[PP0];
            for i in [1..gP-1] do
                gens:=[ss(x):x in gens];
                assert exists(PP_next){id:id in pp|forall{x:x in gens|x@@mQ in id}};
                Append(~output,PP_next);
            end for;
            Reverse(~output);
            assert {myHash(id):id in pp} eq {myHash(id):id in output};
            assert #output eq gP;
        else
            output:=pp;
        end if;
        isog`PlacesOfDieudonneAlgebraSortedBySigmaAbove_p[nu_Hash]:=output;
    end if;
    return isog`PlacesOfDieudonneAlgebraSortedBySigmaAbove_p[nu_Hash];
end intrinsic;

intrinsic PrimesOfSAbove_p(isog::IsogenyClassFq,S::AlgEtQOrd)->SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl],SeqEnum[AlgEtQIdl]
{Given an order S in the DieudonneAlgebra of the isogeny class isog over a finite field of charateristic p returns three sequences consisting of the pries of S above p of slope equal to 0, in (0,1), equalt to 1, respetively.}
    if not assigned S`PrimesOfSAbove_p then
        oneS:=OneIdeal(S);
        pp0,pp01,pp1:=PlacesOfQFAbove_p(isog); 
        PP0:=Setseq(&join[{oneS meet (S!!Q):Q in PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)}:nu in pp0]);
        PP01:=Setseq(&join[{oneS meet (S!!Q):Q in PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)}:nu in pp01]);
        PP1:=Setseq(&join[{oneS meet (S!!Q):Q in PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)}:nu in pp1]);
        assert2 forall{P : P in PP0 | IsPrime(P)};
        assert2 forall{P : P in PP01 | IsPrime(P)};
        assert2 forall{P : P in PP1 | IsPrime(P)};
        S`PrimesOfSAbove_p:=<PP0,PP01,PP1>;
    end if;
    return Explode(S`PrimesOfSAbove_p);
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////// Slopes of Primes ///////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic Slope(P::AlgEtQIdl : CheckMaximal:=true)->FldRatElt
{Given a maximal ideal P of the maximal order of the commutative endomorphism algebra E=Q[pi] of abelian varieties over Fq, with q=p^a, it returns the slope of P, which is defined as val_P(pi)/(a*e_P) where val_P(pi) is the valuation of pi at P and e_P is the ramification index of P.
If the vararg CheckMaximal is set to false, the instrinsic will accept as input also a P is a maximal ideal of a non-maximal order and return val_PP(pi)/(a*e_PP) where PP is a maximal ideal of the maximal order above P. If the output is not 0 or 1, then it is not well defined: it will be a rational number in the open interval (0,1), but the exact value might depend on the choice of PP above P.}
    if not assigned P`Slope then
        require IsPrime(P) : "The ideal is not a maximal ideal.";
        S:=Order(P);
        if CheckMaximal then
            require IsMaximal(S) : "The ideal is not a maximal ideal of the maximal order. You might want to set the VarArg CheckMaximal to false.";
        end if;
        E:=Algebra(P);
        pi:=PrimitiveElement(E);
        h:=DefiningPolynomial(E);
        g:=Degree(h) div 2;
        q:=Truncate(ConstantCoefficient(h)^(1/g));
        t,p,a:=IsPrimePower(q);
        assert t;
        if not IsMaximal(S) then
            t:=exists(PP){ PP : PP in PlacesAboveRationalPrime(E,p) | OneIdeal(S) meet S!!PP eq P};
            assert t;
            P`Slope:=$$(PP);
        else
            val_pi:=Valuation(pi,P);
            eP:=RamificationIndex(P);
            P`Slope:=val_pi/(a*eP);
        end if;
    end if;
    return P`Slope;
end intrinsic;

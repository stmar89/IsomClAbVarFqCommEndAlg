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

declare attributes AbelianVarietyFq : GeneralizedDeligneModule;

declare attributes AlgEtQIdl : DeltaInverse_pPart;

Delta_inverse_ppart:=function(isog,DM)
// given an ideal DM in A, computes and ideal J such that J_p = Delta^-1(DM_p)
    if not assigned DM`DeltaInverse_pPart then
        R:=ZFVOrder(isog);
        E:=Algebra(R);
        _,_,_,_,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,Delta_inverse_ideal,primes_of_A_above_place_of_E:=DieudonneAlgebraCommEndAlg(isog);
        p:=CharacteristicFiniteField(isog);
        nus:=PlacesAboveRationalPrime(E,p);
        unifs:=Uniformizers(nus);
        oOA:=Order(DM)!!OneIdeal(OA);
        cc:=OA!!ColonIdeal(oOA,DM);
        exps:=[];
        for nu in nus do
            M_nu:=Max([Valuation(cc,P) : P in primes_of_A_above_place_of_E(A,nu)]);
            Append(~exps,M_nu);
        end for;
        dp:=&*[unifs[i]^exps[i]:i in [1..#nus]];
        dpDM:=Delta_map(dp)*DM;
        d:=Index(oOA+dpDM,oOA);
        assert IsCoprime(d,p);
        d:=dp*d;
        dDM:=Delta_map(d)*DM;

        vp_ind:=Valuation(Index(oOA,dDM),p);
        dDM_ppart:=dDM+p^vp_ind*oOA;
        // DOUBLE CHECK this
        DM`DeltaInverse_pPart:=(1/d)*Delta_inverse_ideal(dDM_ppart);
    end if;
    return DM`DeltaInverse_pPart;
end function;


intrinsic GeneralizedDeligneModule(AV:AbelianVarietyFq)->AlgEtQIdl,AlgEtQIdl
{Given an abelian variety AV, it return a pair (I,M) where I is a fractional ideal over R=ZFVOrder and M is a fractional ideal over WR (defined in DieudonneAlgebraCommEndAlg) such that I \otimes Zp = Delta_map^-1(M\otimes Zp). The ideal I encodes the local at l\neq p, the étale-local and local-étale information about AV, while M encodes the local-local part of the Dieudonne module.}
    if not assigned AV`GeneralizedDeligneModule then
        require assigned AV`IsomDataCommEndAlg : "The attribute IsomDataCommEndAlg is not assigned";
        isog:=IsogenyClass(AV);
        require IsSquarefree(isog) : "At the moment it is implemented only for abelian varieties with commutative Fq-endomorphism algebra.";
        J,DM,L,S:=IsomDataCommEndAlg(AV);
        _,_,_,_,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,Delta_inverse_ideal,primes_of_A_above_place_of_E:=DieudonneAlgebraCommEndAlg(isog);
        R:=ZFVOrder(isog);
        E:=Algebra(R);
        // denote by m the local-local ideal of R.
        // Let x be such that L_m = xS_m.
        // I and M need to satisfy: I_n = (JL)_n for every n different from m, 
        //                          I_m = (x*Delta^-1(DM))_m
        //                          M = Delta(x)*DM

        // We find x.
        mm:=Setseq({ OneIdeal(S) meet S!!P : P in pp where _,pp,_:=PlacesOfQFAbove_p(isog) });
        x_mm:=[];
        for m in mm do
            V,v:=QuotientVS(L,m*L,m);
            assert Dimension(V) eq 1;
            x_m:=V.1@@v;
            Append(~x_mm,x_m);
        end for;
        x:=ChineseRemainderTheorem(mm,x_mm);
        // We can now define M.
        Delta_x:=Delta_map(x);
        M:=Delta_x*DM;

        // We create I.
        Y:=Delta_inverse_ppart(isog,DM);
        _,m,_:=PrimesOfZFVAbove_p(isog);
        assert #m eq 1;
        m:=m[1];

        mm:=PrimesAbove(S!!m);
        X:=S!!J;
        Y:=S!!Y;
        _,y:=SmallRepresentative(X+Y);
        yX:=y*X; // c S
        yY:=y*Y; // c S
        nn:=PrimesAbove(yX meet yY); // this is Supp(S/yX) join Supp(S/yY)
        nn:=Setseq(Seqset(nn) diff Seqset(mm));
        idls:=[ yX : i in [1..#nn] ];
        idls cat:=[yY : j in [1..#mm]];
        nn cat:=mm;
        nn_pows:=[];
        for i in [1..#nn] do
            n:=nn[i];
            _,p:=IsPrimePower(Index(S,n));
            k:=Valuation(Index(S,idls[i]),p);
            Append(~nn_pows,n^k); // n^k c idls[i] locally at n.
        end for;
        nn_prods_j_ne_i:=[];
        for i in [1..#nn] do
            if #nn eq 1 then
                prod:=OneIdeal(S);
            else
                prod:=&*[nn_pows[j] : j in [1..#nn] | j ne i ];
            end if;
            Append(~nn_prods_j_ne_i,prod);
        end for;
        I0:=&+[(idls[i] + nn_pows[i])*nn_prods_j_ne_i[i] : i in [1..#idls]];
        I:=L*(1/y)*I0;
        AV`GeneralizedDeligneModule:=<I,M>;
    end if;
    return Explode(AV`GeneralizedDeligneModule);
end intrinsic;

/*
    Attach("~/IsomClAbVarFqCommEndAlg/GenDeligneModules.m");
    //X:=iso[1];
    //time I,M:=GeneralizedDeligneModule(X);

    //SetProfile(true);
    for iX->X in iso do
        iX;
        time I,M:=GeneralizedDeligneModule(X);
    end for;
    //SetProfile(false);
    //G:=ProfileGraph();
    //ProfilePrintByTotalTime(G);
*/

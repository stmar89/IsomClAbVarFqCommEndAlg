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

declare verbose Algorithm_2,3;
declare verbose Algorithm_3,3;

declare attributes IsogenyClassFq : DiedudonneAlgebraCommEndAlg,
                                    ExponentsWType;

////////////////////////////////////////////////////////////////////////////////////
//////////////////////// IsomorphismClassesDieudonneModules ////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic ExponentsWTypeAtPlace(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the nu-components the isomorphism classes of WR\{F,V\}-ideals with maximal endomorphism OE.}
    // The combinatorics is taken from Waterhouse's paper
    p:=CharacteristicFiniteField(isog);
    a:=Ilog(p,FiniteField(isog));
    f_nu:=InertiaDegree(nu);
    g_nu:=GCD(a,f_nu); //q=p^a
    e_nu:=RamificationIndex(nu);
    pi:=PrimitiveElement(DeligneAlgebra(isog));

    exps:=[];
    cp:=CartesianProduct([ [0..e_nu] : i in [1..g_nu]]);
    for tup0 in cp do
        tup:=[ tup0[i] : i in [1..g_nu] ];
        if &+tup eq Integers()!(g_nu*Valuation(pi,nu)/a) then
            exp:=[ i eq 1 select 0 else Self(i-1) + tup[i-1] : i in [1..g_nu]];
            Append(~exps,exp);
        end if;
    end for;
    return exps;
end intrinsic;

intrinsic ExponentsWType(isog::IsogenyClassFq,slopes::MonStgElt)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the isomorphism classes of WR\{F,V\}-ideals or WR'\{F',V'\}-ideals -- depending on whether slopes is "all" or "(0,1)" -- with maximal endomorphism OE.}
    require slopes in {"(0,1)","all"} : "Invalid parameter slopes";
    if not assigned isog`ExponentsWType or isog`ExponentsWType[2] ne slopes then
        plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
        if slopes eq "(0,1)" then
            plE:=plE01;;
        elif slopes eq "all" then
            plE:=plE0 cat plE01 cat plE1;
        end if;
        exps_nus:=[ExponentsWTypeAtPlace(isog,nu):nu in plE];
        exps_nus_cc:=CartesianProduct(exps_nus);
        exps_plE:=[];
        for cc in exps_nus_cc do
            Append(~exps_plE,&cat[ c : c in cc ]); 
        end for;
        isog`ExponentsWType:=<exps_plE,slopes>;
    end if;
    return isog`ExponentsWType[1];
end intrinsic;

intrinsic WRIdealsWithFVStableExtensionToOA(isog::IsogenyClassFq,slopes::MonStgElt)->SeqEnum[AlgEtQIld]
{Given an isogeny class isog, if slopes is "all" then returns a sequence of fraction WR-ideals I whose extension I*OA to the maximal order OA of the DieudonneAlgebra A is stable by the action of F and V, modulo Delta-isomorphisms; if slopes is "(0,1)" then on the local-local part of the previously described output is returned.}
    require slopes in {"(0,1)","all"} : "Invalid parameter slopes";
    _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
    p:=CharacteristicFiniteField(isog);

    plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
    if slopes eq "(0,1)" then
        plE:=plE01;;
        plA:=&cat[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE]; // sorted by sigma !!!
        vprintf Algorithm_2,1 : "Defining WR_plE...";
        // We compute the W'_R-isomorphim classes of W'_R-ideals.
        k:=Valuation(Index(OA,WR),p);
        WR_plE:=Order( ZBasis(WR) cat ZBasis(OA!!&*[ P^(k*RamificationIndex(P)) : P in plA ]));
        vprintf Algorithm_2,1 : "done\n";
        vprintf Algorithm_2,1 : "[OA:WR] = %o\n",Index(OA,WR);
        vprintf Algorithm_2,1 : "[OA:WR_plE] = %o\n",Index(OA,WR_plE);
        vprintf Algorithm_2,1 : "Computing WKICM(WR_plE)...";
    elif slopes eq "all" then
        plE:=plE0 cat plE01 cat plE1;
        plA:=[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE]; // here the places of A need
                                                                                       // to be sorted by sigma
        WR_plE:=WR;
    end if;
    // We need now uniformizers for all places of A above places nu of QF.
    // Note: we cannot use Delta(t) for t a uniformizer at nu, because it will have 
    // valuation 1 at ALL places of A above nu. So when taking a product, we are modifing all
    // places above nu at the same time.
    // Currently, we are calling Uniformizers for places of A only here. If this changes, we might
    // want to make an intrinsic that stores them in some smart way...
    nice_unifs:=Uniformizers(plA);
    exps_plE:=ExponentsWType(isog,slopes);
    vprintf Algorithm_2,2 : "F-V stable O_A' ideals = %o \n",exps_plE;
    vprintf Algorithm_2,2 : "nice_unifs = %o\n", PrintSeqAlgEtQElt(nice_unifs);

    // DUALITY could speed up the next computation. 
    // It would have to run for all plA of slope <1/2 and =1/2, and deduce the output for >1/2 from the first.
    wk:=[ WR!!I : I in WKICM(WR_plE)];
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "number of W_R'-isomorphism classes = %o\n",#wk;

    vprintf Algorithm_2,1 : "Computing output...";
    output:=[];
    for I in wk do
        S:=MultiplicatorRing(I);
        J:=OA!!I;
        valsJ:=[ Valuation(J,P) : P in plA ];
        deltas:=[];
        for exps in exps_plE do
            assert #exps eq #plA; 
            Append(~deltas,&*[nice_unifs[i]^(valsJ[i]-exps[i]) : i in [1..#plA]]);
        end for;
        QS,qS:=UnitGroupQuotientAtSlopeFixedBySigma(isog,S,"(0,1)");
        gammas:=[qS(x):x in QS];
        vprintf Algorithm_2,2 : "valsJ = %o\n", valsJ;
        vprintf Algorithm_2,2 : "deltas = %o\n", PrintSeqAlgEtQElt(deltas);
        vprintf Algorithm_2,2 : "gammas = %o\n", PrintSeqAlgEtQElt(gammas);
        assert2 forall{ d : d in deltas | not IsZeroDivisor(d) };
        assert2 forall{ g : g in gammas | not IsZeroDivisor(g) };
        II:=[ ((d^-1)*g)*I : d in deltas, g in gammas ];
        vprintf Algorithm_2,2 : "#II = %o\n",#II;
        vprintf Algorithm_2,3 : "valuations of the of extensions O_A' of the ideals in II = %o\n",[ [ Valuation(OA!!ii,P) : P in plA ] : ii in II ]; // computing this info might take a lot of time.
        output cat:=II;
    end for;
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "number of Delta'-isomorphism classes with FV-stable extension to O_A' = %o\n",#output;
    return output;
end intrinsic;

intrinsic IsomorphismClassesDieudonneModulesCommEndAlg(isog::IsogenyClassFq,slopes::MonStgElt : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AlgEtQIdl]
{Given an isogeny class of abelian varieties over Fq with commutative endomorphism algebra returns representatives of the isomorphism classes of the local-local parts of the Dieudonné modules of the varieties. These representatives are given as fractional WR-ideals, where WR is defined as in DiedudonneAlgebraCommEndAlg, which are stable under the action of semilinar operators F and V=pF^-1, where F has the Frobenius property and is of W-type. See the paper for the definitions. The action of F and V is computed on a quotient, whose size is determined by a precision parameter m. This m is calculated automatically to guarantee that the output of this function is correct. One can increase this parameter by setting the VarArg IncreaseMinimumPrecisionForSemilinearFVBy to a strinctly positive value. The operators can be recovered using SemilinearOperatorsWType. The second argument slopes can have values "(0,1)" or "all" and determined whether only the local-local part of the whole Dieudonne modules are computed.}
    require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
    plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
    _,_,_,_,_,_,OA,_,WR,_:=DieudonneAlgebraCommEndAlg(isog);
    if slopes eq "(0,1)" then
        plE:=plE01;;
        if #plE01 eq 0 then
            // Early exit if no places of slope in (0,1). This means that we are in the ordinary case.
            assert IsOrdinary(isog);
            dm:=OneIdeal(WR);
            dm`DeltaEndomorphismRing:=ZFVOrder(isog);
            return [dm]; 
        end if;
    elif slopes eq "all" then
        plE:=plE0 cat plE01 cat plE1;
    end if;

    candidates:=WRIdealsWithFVStableExtensionToOA(isog,slopes);

    // We construct the OA{F,V}-ideal J in whose quotient we will compute the approximations of the semilinear
    // operators to check the F-V-stability of the candidates.
    exps:=ExponentsWType(isog,slopes)[1];
    //"WARNING: changing J for test purposes";exps:=exps_01[2];
    plA:=&cat[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE]; // sorted by sigma !!!
    JOA:=&*[ plA[i]^exps[i] : i in [1..#exps] ]; 
    J:=WR!!JOA;
    ZBasisLLL(J);
    vprintf Algorithm_3,2 : "vals of the F-V stable OA-ideal J chosen for the container = %o\n",
                            [Valuation(OA!!J,P) : P in plA];

    vprintf Algorithm_3,1 : "Delta-scaling the ideals into J...";
    candidates,m0:=DeltaScaleInside(isog,J,candidates);
    vprintf Algorithm_3,1 : "done\n";

    if IncreaseMinimumPrecisionForSemilinearFVBy gt 0 then
        m0_old:=m0;
        m0+:=IncreaseMinimumPrecisionForSemilinearFVBy;
        vprintf Algorithm_3:"Incresing m0 from to %o, using IncreaseMinimumPrecisionForSemilinearFVBy\n",m0_old,m0;
    end if;
    //m1:=m0+10; "WARNING: m0 is forced now from ",m0,"to",m1; m0:=m1; //for debugging

    vprintf Algorithm_3 : "m0 = %o\n",m0;
    vprintf Algorithm_3,2 : "v_nu(pi) for all nu's = %o\n",[ Valuation( pi, P ) : P in plE ] where pi:=PrimitiveElement(DeligneAlgebra(isog));
    vprintf Algorithm_3,2 : "e_nu for all nu's = %o\n",[ RamificationIndex(P) : P in plE ];
    vprintf Algorithm_3,2 : "f_nu for all nu's = %o\n",[ InertiaDegree(P) : P in plE ];
    vprintf Algorithm_3,2 : "g_nu for all nu's = %o\n",[ GCD(Ilog(CharacteristicFiniteField(isog),FiniteField(isog)),InertiaDegree(P)) : P in plE ];

    vprintf Algorithm_3 : "Computing Qm0,qm0,FQm0,VQm0...";
    Qm0,qm0,FQm0,VQm0:=SemilinearOperatorsWType(isog,J,m0,slopes);
    vprintf Algorithm_3 : "done\n";

    is_F_V_stable:=function(I)
        assert2 I subset J;
        I_Qm0:=sub<Qm0 | [qm0(z) : z in ZBasis(I) ]>;
        IFV_Qm0:=I_Qm0 + 
                        sub<Qm0 | [FQm0(z) : z in Generators(I_Qm0)] > +
                        sub<Qm0 | [VQm0(z) : z in Generators(I_Qm0)] >;
        vprintf Algorithm_3,3 : "[I_Q+F_Q(I_Q)+V_Q(I_Q):I_Q] = %o\n",Index(IFV_Qm0,sub<IFV_Qm0|I_Qm0>);
        return I_Qm0 eq IFV_Qm0;
    end function;

    Delta_isom_classes_WR_F_V:=[ ];
    vprintf Algorithm_3,2 : "Started checking for F-V stability:";
    delta_inverses_mult_rings:=[];
    for iI in [1..#candidates] do
        vprintf Algorithm_3,3 : "\nfor the %oth ideal from candidates:",iI;
        I:=WR!!candidates[iI];
        if is_F_V_stable(I) then
            vprintf Algorithm_3,2 : "y";
            assert Order(I) eq WR;
            // For each WR{F,V}-ideal (or WR'{F',V'}-ideal) I we compute Delta^-1((I:I)).
            // This will be the p-part (or the (0,1)-part) of the endomorphism ring. Since
            // computing Delta^-1 of something is expensive, we store it in case more than one
            // I share the same multiplicator ring (I:I) in A.
            mI:=MultiplicatorRing(I);
            t:=exists(S){pair[2]:pair in delta_inverses_mult_rings|pair[1] eq mI};
            if not t then
                Sid:=DeltaInverseIdeal(isog,WR!!OneIdeal(mI));
                S:=Order(ZBasis(Sid));
                assert Sid eq Order(Sid)!!OneIdeal(S);
                Append(~delta_inverses_mult_rings,<mI,S>);
            end if;
            I`DeltaEndomorphismRing:=S;
            Append(~Delta_isom_classes_WR_F_V,I);
        else
            vprintf Algorithm_3,2 : "n";
        end if;
    end for;
    vprintf Algorithm_3,2 : "\n";

    return Delta_isom_classes_WR_F_V;
end intrinsic;

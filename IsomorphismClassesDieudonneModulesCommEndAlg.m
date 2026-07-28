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
                                    ExponentsWType,
                                    ExponentsDual;

////////////////////////////////////////////////////////////////////////////////////
//////////////////////// IsomorphismClassesDieudonneModules ////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic ExponentsWTypeAtPlace(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the nu-components the isomorphism classes of WR\{F,V\}-ideals with maximal endomorphism OE for nu such that F_nu=alpha_nu*sigma with alpha_nu of W-type.}
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

intrinsic ExponentsWTypeDualAtPlace(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the nu-components the isomorphism classes of WR\{F,V\}-ideals with maximal endomorphism OE for nu non-conjugate-stable such that F_bar(nu)=alpha_bar(nu)*sigma with alpha_bar(nu) of W-type.}
// NEW 20260728
    p:=CharacteristicFiniteField(isog);
    a:=Ilog(p,FiniteField(isog));
    f_nu:=InertiaDegree(P);
    g_nu:=GCD(a,f_nu); //q=p^a
    e_nu:=RamificationIndex(P);
    pi:=PrimitiveElement(DeligneAlgebra(isog));

    exps:=[];
    cp:=CartesianProduct([ [-e_nu..0] : i in [1..g_nu]]);
    for tup0 in cp do
        tup:=[ tup0[i] : i in [1..g_nu] ];
        if &+tup eq -Integers()!(g_nu*Valuation(pi,P)/a) then
            exp:=Reverse([ i eq g_nu select 0 else Self(g_nu-i) - tup[i] : i in Reverse([1..g_nu])]);
            Append(~exps,exp);
        end if;
    end for;
    return exps;
end intrinsic;

intrinsic ExponentsConjStabRhoNotIdAtPlace(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the nu-components the isomorphism classes of WR\{F,V\}-ideals with maximal endomorphism OE for nu conjugate-stable such that bar induces a permutation of order 2 on the places of A above nu. We asseume that F_nu=alpha_nu*sigma for alpha_nu=(1,...,1,bar(eps),p,...,p,p/eps) as describd in //TODO add ref to paper, or give details about eps
}
// NEW 20260728
    p:=CharacteristicFiniteField(isog);
    a:=Ilog(p,FiniteField(isog));
    f_nu:=InertiaDegree(nu);
    g:=GCD(a,f_nu); //q=p^a
    e_nu:=RamificationIndex(nu);
    pi:=PrimitiveElement(DeligneAlgebra(isog));
    assert IsEven(g); // If rho has order 2 then, g has to be even
    g2:=g div 2;

    exps:=[];
    // we get the following retrictions for n_i:
    // 0<=n_i<=e    for i=1,...,g2-1
    // 0=n_{g2}
    // -e<=n_i<=0   for i=g2+1,...,g-1
    // -e<=n_g<=e
    // sum_i n_i=0
    cp:=CartesianProduct([ [0..e_nu] : i in [1..g2-1]] cat [[0]] cat [[-e_nu..0] : i in [g2+1..g-1]] cat [[-e_nu..e_nu]]);
    for tup0 in cp do
        tup:=[ tup0[i] : i in [1..g] ];
        if &+tup eq 0 then // n_g = -sum_i n_i where n_i=exp[i+1]-exp[i]
            exp:=[ i eq 1 select 0 else Self(i-1) + tup[i-1] : i in [1..g]];
            Append(~exps,exp);
        end if;
    end for;
    return exps;
end intrinsic;

intrinsic ExponentsWType(isog::IsogenyClassFq,slopes::MonStgElt)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the isomorphism classes of WR\{F,V\}-ideals or WR'\{F',V'\}-ideals -- depending on whether slopes is "all" or "(0,1)" -- with maximal endomorphism ring OE.}
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

intrinsic ExponentsDual(isog::IsogenyClassFq)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing the isomorphism classes of WR\{F,V\}-ideals with maximal endomorphism ring OE. We assume that F and V are constructed to be compatible with duality. //TODO details about this compatibility
}
// NEW 20260728
    if not assigned isog`ExponentsDual then
        exps_nus:=AssociativeArray();
        conj_pairs,rho_id,rho_notid:=SortPlacesOfQFAbove_p(isog);
        for pair in conj_pairs do
            nu,nub:=Explode(pair);
            exps_nus[nu]:=ExponentsWTypeAtPlace(isog,nu);
            exps_nus[nub]:=ExponentsWTypeDualAtPlace(isog,nu);
        end for;
        for nu in rho_id do
            exps_nus[nu]:=ExponentsWTypeAtPlace(isog,nu);
        end for;
        for nu in rho_notid do
            exps_nus[nu]:=ExponentsConjStabRhoNotIdAtPlace(isog,nu);
        end for;

        plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
        plE:=plE0 cat plE01 cat plE1;
        exps_nus:=[exps_nus[nu]:nu in plE]; // now the entries are sorted in the usual way.

        exps_nus_cc:=CartesianProduct(exps_nus);
        exps_plE:=[];
        for cc in exps_nus_cc do
            Append(~exps_plE,&cat[ c : c in cc ]); 
        end for;
        isog`ExponentsDual:=<exps_plE,slopes>;
    end if;
    return isog`ExponentsDual;
end intrinsic;

intrinsic WRIdealsWithFVStableExtensionToOA(isog::IsogenyClassFq,slopes::MonStgElt : dual:=false)->SeqEnum[AlgEtQIld]
{Given an isogeny class isog, if slopes is "all" then returns a sequence of fractional WR-ideals I whose extension I*OA to the maximal order OA of the DieudonneAlgebra A is stable by the action of F and V, modulo Delta-isomorphisms; if slopes is "(0,1)" then on the local-local part of the previously described output is returned.
//TODO describe dual
}
    require slopes in {"(0,1)","all"} : "Invalid parameter slopes";
    if dual then
        require slopes eq "all" : "When dual is true, we need to use all slopes";
    end if;

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
    elif slopes eq "all" then
        plE:=plE0 cat plE01 cat plE1;
        plA:=&cat[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE]; // sorted by sigma !!!
        WR_plE:=WR;
    end if;
    // We need now uniformizers for all places of A above places nu of QF.
    // Note: we cannot use Delta(t) for t a uniformizer at nu, because it will have 
    // valuation 1 at ALL places of A above nu. So when taking a product, we are modifing all
    // places above nu at the same time.
    // Currently, we are calling Uniformizers for places of A only here. If this changes, we might
    // want to make an intrinsic that stores them in some smart way...
    nice_unifs:=Uniformizers(plA);
    if not dual then
        exps_plE:=ExponentsWType(isog,slopes);
    elif dual then
        exps_plE:=ExponentsDual(isog);
    end if;

    vprintf Algorithm_2,2 : "F-V stable O_A' ideals = %o \n",StripWhiteSpace(Sprint(exps_plE));
    vprintf Algorithm_2,2 : "nice_unifs = %o\n",StripWhiteSpace(Sprint(PrintSeqAlgEtQElt(nice_unifs)));

    if slopes eq "(0,1)" then
        wk:=[ WR!!I : I in WKICM(WR_plE)];
    else
        // we use duality and sigma
        wk:=WeakEquivalenceClassMonoidWR(isog);
    end if;
    vprintf Algorithm_2,1 : "number of W_R'-isomorphism classes = %o\n",#wk;

    vprintf Algorithm_2,1 : "Computing candidates...";
    output:=[];
    for iI->I in wk do
        S:=MultiplicatorRing(I);
        J:=OA!!I;
        valsJ:=[ Valuation(J,P) : P in plA ];
        deltas:=[];
        for exps in exps_plE do
            assert #exps eq #plA;
            delta:=&*[nice_unifs[i]^(valsJ[i]-exps[i]) : i in [1..#plA]];
            assert2 forall{i:i in [1..#plA]|Valuation(delta,plA[i]) eq valsJ[i]-exps[i]};
            Append(~deltas,delta);
        end for;
        _,_,gammas:=UnitGroupQuotientAtSlopeFixedBySigma(isog,S,slopes);
        II:=[ ((d^-1)*g)*I : d in deltas, g in gammas ];
        vprintf Algorithm_2,2 : "\n\tiI = %3o  #deltas = %3o #gammas = %3o valsJ = %o",
                                 iI,#deltas,#gammas,StripWhiteSpace(Sprint(valsJ));
        vprintf Algorithm_2,3 : "\n\tvaluations of the of extensions O_A' of the ideals in II = %o",
                                 StripWhiteSpace(Sprint([[Valuation(OA!!ii,P):P in plA]:ii in II])); 
                                 // computing this info might take a lot of time.
        assert2 forall{ d : d in deltas | not IsZeroDivisor(d) };
        assert2 forall{ g : g in gammas | not IsZeroDivisor(g) };
        // the next test is very useful, but expensive.
        assert3 forall{ i : i in II | [Valuation(OA!!i,P):P in plA] in exps_plE };
        output cat:=II;
    end for;
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "number of Delta'-isomorphism classes with FV-stable extension to O_A' = %o\n",#output;
    return output;
end intrinsic;

intrinsic IsomorphismClassesDieudonneModulesCommEndAlg(isog::IsogenyClassFq,slopes::MonStgElt : dual:=false , IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AlgEtQIdl]
{Given an isogeny class of abelian varieties over Fq with commutative endomorphism algebra returns representatives of the isomorphism classes of the local-local parts of the Dieudonné modules of the varieties. These representatives are given as fractional WR-ideals, where WR is defined as in DiedudonneAlgebraCommEndAlg, which are stable under the action of semilinar operators F and V=pF^-1, where F has the Frobenius property and is of W-type. See the paper for the definitions. The action of F and V is computed on a quotient, whose size is determined by a precision parameter m. This m is calculated automatically to guarantee that the output of this function is correct. One can increase this parameter by setting the VarArg IncreaseMinimumPrecisionForSemilinearFVBy to a strinctly positive value. The operators can be recovered using SemilinearOperatorsWType. The second argument slopes can have values "(0,1)" or "all" and determined whether only the local-local part of the whole Dieudonne modules are computed.
//TODO describe dual
}
    require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
    if dual then
        require slopes eq "all" : "When dual is true, we need to use all slopes";
    end if;

    plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
    _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
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
    if not dual then
        exps:=ExponentsWType(isog,slopes)[1];
    elif dual then
        exps_plE:=ExponentsDual(isog);
    end if;
    //"WARNING: changing J for test purposes";exps:=exps_01[2];
    // FIXME We want J to be integral and as close as possible to OA
    plA:=&cat[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE]; // sorted by sigma !!!
    assert #plA eq #exps;
    JOA:=&*[ plA[i]^exps[i] : i in [1..#exps] ]; 
    J:=WR!!JOA;
    ZBasisLLL(J);
    vprintf Algorithm_3,2 : "vals of the F-V stable OA-ideal J chosen for the container = %o\n",
                            [Valuation(OA!!J,P) : P in plA];

    vprintf Algorithm_3,1 : "Delta-scaling the %o candidates into J...",#candidates;
    candidates,m0:=DeltaScaleInside(isog,J,candidates);
    vprintf Algorithm_3,1 : "done\n";

    if IncreaseMinimumPrecisionForSemilinearFVBy gt 0 then
        m0_old:=m0;
        m0+:=IncreaseMinimumPrecisionForSemilinearFVBy;
        vprintf Algorithm_3:"Incresing m0 from to %o, using IncreaseMinimumPrecisionForSemilinearFVBy\n",m0_old,m0;
    end if;
    //m1:=m0+10; "WARNING: m0 is forced now from ",m0,"to",m1; m0:=m1; //for debugging

    vprintf Algorithm_3 : "m0 = %o\n",m0;

    vprintf Algorithm_3 : "Computing Qm0,qm0,FQm0,VQm0...";
    Qm0,qm0,FQm0,VQm0,den_ideal:=SemilinearOperatorsWType(isog,J,m0,slopes);
    assert IsPowerOf(#Qm0,CharacteristicFiniteField(isog));
    vprintf Algorithm_3 : "done\n";

    is_F_V_stable:=function(I)
        assert2 I subset J;
        I_Qm0:=sub<Qm0 | [qm0(z) : z in ZBasis(I) ]>;
        IFV_Qm0:=sub<Qm0 | &cat[[z,FQm0(z),VQm0(z)] : z in Generators(I_Qm0)] >;
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

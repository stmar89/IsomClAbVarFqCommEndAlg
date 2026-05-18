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


////////////////////////////////////////////////////////////////////////////////////
//////////////////////// IsomorphismClassesDieudonneModules ////////////////////////
////////////////////////////////////////////////////////////////////////////////////

intrinsic ExponentsWTypeAtPlace(isog::IsogenyClassFq,nu::AlgEtQIdl)->SeqEnum[SeqEnum[RngIntElt]]
{Given an isogeny class isog and a place nu of the Deligne Algebra, one can represent the isomorphism classes of Dieudonne Modules with maximal endomorphism rings as OA\{F,V\}-ideal in the DieudonneAlgebra A. These ideals can be efficiently described as vectors of powers of uniformizers. In particular, the property of being F-V-stable can be checked using the exponents of this power representation, assuming that the maximal ideal of A above nu are sorted according to the action of sigma. This intrinsic returns a sequence of the exponents, each one represented as a sequence of integers, describing all the isomorphism classes of WR\{F,V\}-ideals with maximal endomorphsm OE.}
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

intrinsic IsomorphismClassesDieudonneModulesCommEndAlg(isog::IsogenyClassFq : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AlgEtQIdl]
{Given an isogeny class of abelian varieties over Fq with commutative endomorphism algebra returns representatives of the isomorphism classes of the local-local parts of the Dieudonné modules of the varieties. These representatives are given as fractional WR-ideals, where WR is defined as in DiedudonneAlgebraCommEndAlg, which are stable under the action of semilinar operators F and V=pF^-1, where F has the Frobenius property and is of W-type. See the paper for the definitions. The action of F and V is computed on a quotient, whose size is determined by a precision parameter m. This m is calculated automatically to guarantee that the output of this function is correct. One can increase this parameter by setting the VarArg IncreaseMinimumPrecisionForSemilinearFVBy to a strinctly positive value. The operators can be recovered using SemilinearOperators.}
//FIXME deal with vararg
    require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
    vprintf DieudonneModules,1 : "Computing DiedudonneAlgebraCommEndAlg...";
    R:=ZFVOrder(isog);
    E:=Algebra(R);
    pi:=PrimitiveElement(E);
    //h:=DefiningPolynomial(E);
    g:=Dimension(isog);
    q:=FiniteField(isog);
    t,p,a:=IsPrimePower(q);
    assert t;
    L,_,_,_,A,pi_A,_,Delta_map,WR,sigma_OA_mod_I:=DieudonneAlgebraCommEndAlg(isog);
    OA:=MaximalOrder(A);
    vprintf DieudonneModules,1 : "done\n";
    vprintf DieudonneModules,1 : "sing primes of R = %o\n",[Index(R,PP):PP in SingularPrimes(R)];
    vprintf DieudonneModules,1 : "[OE:R] = %o\ndim_Q(L)=%o\ndim_Q(A)=%o\n",Index(MaximalOrder(E),R),Degree(L),Dimension(A);
    _,plE_sl_in01,_:=PlacesOfQFAbove_p(isog);
    _,pl_01_R,_:=PrimesOfZFVAbove_p(isog);
    pl_01_R:=Setseq({ OneIdeal(R) meet (R!!P) : P in plE_sl_in01 });
    if #plE_sl_in01 ne 0 then
        assert #pl_01_R eq 1;
    end if;

    vprintf DieudonneModules,2 : "places of E w/ slope in (0,1) = %o\n",Sort([ Slope(P) : P in plE_sl_in01]);
    // Early exit if no places 
    if #plE_sl_in01 eq 0 then
        dm:=OneIdeal(WR);
        dm`DeltaEndomorphismRing:=R;
        return [dm],plE_sl_in01; 
    end if;

    // ####################
    // Algorithm 2
    // ####################

    vprintf Algorithm_2,1 : "\n\n################\nAlgorithm 2\n################\n";

    exps_nus:=[];
    pp_A_01:=[];
    nice_unifs_01:=[];
    for nu in plE_sl_in01 do
        pp_A_nu:=PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu); // here the places of A need 
                                                                               // to be sorted by sigma
        Append(~exps_nus,ExponentsWTypeAtPlace(isog,nu));
        pp_A_01 cat:=pp_A_nu;
    end for;
    // We need now uniformizers for all places of A above places nu of QF.
    // Note: we cannot use Delta(t) for t a uniformizer at nu, because it will have 
    // valuation 1 at ALL places of A above nu. So when taking a product, we are modifing all
    // places above nu at the same time.
    // Currently, we are calling Uniformizers for places of A only here. If this changes, we might
    // want to make an intrinsic that stores them in some smart way...
    nice_unifs_01:=Uniformizers(pp_A_01);
    exps_nus_cc:=CartesianProduct(exps_nus);
    exps_01:=[];
    for cc in exps_nus_cc do
        Append(~exps_01,&cat[ c : c in cc ]); 
    end for;
    vprintf Algorithm_2,2 : "F-V stable O_A' ideals = %o \n",exps_01;
    vprintf Algorithm_2,2 : "nice_unifs_01 = %o\n", PrintSeqAlgEtQElt(nice_unifs_01);

    vprintf Algorithm_2,1 : "Defining WR_01...";
    // We compute the W'_R-isomorphim classes of W'_R-ideals.
    k:=Valuation(Index(OA,WR),p);
    WR_01:=Order( ZBasis(WR) cat ZBasis(OA!!&*[ P^(k*RamificationIndex(P)) : P in pp_A_01 ]));
    // WR_01 order is locally equal to WR' at every place of slope 01 and to OA everywhere else
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "[OA:WR] = %o\n",Index(OA,WR);
    vprintf Algorithm_2,1 : "[OA:WR_01] = %o\n",Index(OA,WR_01);
    vprintf Algorithm_2,1 : "Computing WKICM(WR_01)...";
    // DUALITY could speed up the next computation. 
    // It would have to run for all pp_A_01 of slope <1/2 and =1/2, and deduce the output for >1/2 from the first.
    wk_01:=[ WR!!I : I in WKICM(WR_01)];
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "number of W_R'-isomorphism classes = %o\n",#wk_01;

    vprintf Algorithm_2,1 : "Computing WR_01_idls_with_ext_i_to_OA_F_V_stable...";
    WR_01_idls_with_ext_i_to_OA_F_V_stable:=[];
    for I in wk_01 do
        S:=MultiplicatorRing(I);
        J:=OA!!I;
        valsJ:=[ Valuation(J,P) : P in pp_A_01 ];
        deltas:=[];
        for exps in exps_01 do
            assert #exps eq #pp_A_01; 
            Append(~deltas,&*[nice_unifs_01[i]^(valsJ[i]-exps[i]) : i in [1..#pp_A_01]]);
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
        vprintf Algorithm_2,3 : "valuations of the of extensions O_A' of the ideals in II = %o\n",[ [ Valuation(OA!!ii,P) : P in pp_A_01 ] : ii in II ]; // computing this info might take a lot of time.
        WR_01_idls_with_ext_i_to_OA_F_V_stable cat:=II;
    end for;
    vprintf Algorithm_2,1 : "done\n";
    vprintf Algorithm_2,1 : "number of Delta'-isomorphism classes with FV-stable extension to O_A' = %o\n",#WR_01_idls_with_ext_i_to_OA_F_V_stable;
   
    // ####################
    // Algorithm 3
    // ####################
    
    vprintf Algorithm_3,1 : "\n\n################\nAlgorithm 3\n################\n";
    exps:=exps_01[1];
    //"WARNING: changing J for test purposes";exps:=exps_01[2];
    JOA:=&*[ pp_A_01[i]^exps[i] : i in [1..#exps] ]; 
    assert MultiplicatorRing(J) eq OA;
    J:=WR !! JOA;
    ZBasisLLL(J);
    vprintf Algorithm_3,2 : "vals of the F-V stable OA-ideal J chosen for the container = %o\n",
                            [ Valuation(OA!!J,P) : P in pp_A_01 ];

    vprintf Algorithm_3,1 : "Delta-scaling the ideals into J...";
    WR_01_idls_with_ext_i_to_OA_F_V_stable,m0:=DeltaScaleInside(isog,J,WR_01_idls_with_ext_i_to_OA_F_V_stable);
    vprintf Algorithm_3,1 : "done\n";

    if IncreaseMinimumPrecisionForSemilinearFVBy gt 0 then
        m0_old:=m0;
        m0+:=IncreaseMinimumPrecisionForSemilinearFVBy;
        vprintf Algorithm_3:"Incresing m0 from to %o, using IncreaseMinimumPrecisionForSemilinearFVBy\n",m0_old,m0;
    end if;
    //m1:=m0+10; "WARNING: m0 is forced now from ",m0,"to",m1; m0:=m1; //for debugging

    vprintf Algorithm_3 : "m0 = %o\n",m0;
    vprintf Algorithm_3,2 : "v_nu(pi) for all nu's = %o\n",[ Valuation( pi, P ) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "e_nu for all nu's = %o\n",[ RamificationIndex(P) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "f_nu for all nu's = %o\n",[ InertiaDegree(P) : P in plE_sl_in01 ];
    vprintf Algorithm_3,2 : "g_nu for all nu's = %o\n",[ GCD(a,InertiaDegree(P)) : P in plE_sl_in01 ];

    vprintf Algorithm_3 : "Computing Qm0,qm0,FQm0,VQm0...";
    Qm0,qm0,FQm0,VQm0:=SemilinearOperatorsWType(isog,J,m0);
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
    for iI in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        vprintf Algorithm_3,3 : "\nfor the %oth ideal from WR_01_idls_with_ext_i_to_OA_F_V_stable:",iI;
        I:=WR!!WR_01_idls_with_ext_i_to_OA_F_V_stable[iI];
        if is_F_V_stable(I) then
            vprintf Algorithm_3,2 : "y";
            assert Order(I) eq WR;
            //TODO Describe what are we doing here
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

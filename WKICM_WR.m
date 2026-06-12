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

////////////////////////////////////////////////////////////////////////////////////
//////////////////////// IsomorphismClassesDieudonneModules ////////////////////////
////////////////////////////////////////////////////////////////////////////////////

local_order:=function(R,P,O,p)
// given an order R, the maximal order O and a maximal ideal P of R above p,
// returns the unique overorder S of R which is equal to R locally at P,
// and equal to O everywhere else.
   v:=Floor(Valuation(Index(O,R),p)/Valuation(Index(R,P),p)); // P^v*O < R
   S:=Order(ZBasis(R) cat ZBasis(P^v*R!!OneIdeal(O)));
   return S;
end function;

glue_local_wks:=function(E,wk_pp,p)
// Given an order E, an associative array wk_pp indexed by maximal ideals P of E so that wk_pp[P] = WKICM(E_P) 
// and a rational prime p contained in all P's, returns WKICM(E) by glueing the local info. 
// Attributes are populated.
// Almost copy pasted from WkClasses.m
    pp:=[];
    pp_pows:=[];
    wk_pp_idls:=[];
    for P->wk in wk_pp do
        //P is a maximal ideal of E, wk = WKICM(E_P)
        wk_exps:=[];
        wk_idls:=[];
        for i in [1..#wk] do
            I:=wk[i];
            if not IsIntegral(I) then
                I:=SmallRepresentative(I); // I c E with small norm
            end if;
            k:=Valuation(Index(E,I),p);
            Append(~wk_exps,k);
            Append(~wk_idls,I);
        end for;
        k_P:=Max(wk_exps);
        Pk:=P^k_P; // for every local representative I at P we have that Pk c I (locally)
        ZBasisLLL(Pk);
        Append(~pp,P);
        Append(~pp_pows,Pk);
        Append(~wk_pp_idls,wk_idls);
    end for;

    n:=#Keys(wk_pp);
    prod_j_ne_i:=[ ];
    for i in [1..n] do
        // coprime ideals, so we can use meet instead of *, which is faster
        prod:=&meet[ pp_pows[j] : j in [1..n] | j ne i ];
        ZBasisLLL(prod);
        Append(~prod_j_ne_i,prod);
    end for;

    for ip in [1..n] do
        for i in [1..#wk_pp_idls[ip]] do
            I:=(wk_pp_idls[ip][i]+pp_pows[ip])*prod_j_ne_i[ip];
            ZBasisLLL(I);
            wk_pp_idls[ip][i]:=I;
        end for;
    end for;

    tot:=&*[#x : x in wk_pp_idls]; perc_old:=0; iI:=0;
    wk_pp_idls:=CartesianProduct(wk_pp_idls);
    wk:=[];
    for I_Ps in wk_pp_idls do
        J:=&+[ I_Ps[ip] : ip in [1..n] ];
        // J satisfies: J = I_Ps[ip] locally at pp[ip] for every ip.
        assert2 forall{ ip : ip in [1..n] |
                                        (J+I_Ps[ip]) eq I_Ps[ip]+pp[ip]*(J+I_Ps[ip]) and
                                        (J+I_Ps[ip]) eq J+pp[ip]*(J+I_Ps[ip])};
        Append(~wk,J);
    end for;

    for I in wk do
        ZBasisLLL(I);
    end for;

    // asserts
    assert2 forall{ J : J in wk | Order(J) eq E };
    assert2 forall{ J : J in wk | not exists{I : I in wk | I ne J and IsWeakEquivalent(I,J) }  };

    E`WKICM:=wk;

    // We populate the attributes E`OverOrders and S`WKICM_bar for each overorder.
    // This is needed for the recursion step.
    // Note that some of the overorders have already the vararg WKICM_bar populated, because, for
    // example, they were coming from the recursive-1-single-singular-prime part of the code.
    // In this case, we don't want to add it a second time. Hence we need to keep track of this info.
    // We do it by using nested AssociativeArrays
    if not assigned E`OverOrders or exists{S:S in E`OverOrders|not assigned S`WKICM_bar} then
        oo:=AssociativeArray();
        for I in wk do
            S:=MultiplicatorRing(I);
            ind:=Index(S);
            if not IsDefined(oo,ind) then
                oo[ind]:=AssociativeArray();
                oo[ind][true]:={@ @};
                oo[ind][false]:=AssociativeArray();
                oo[ind][false]["orders"]:=[];
                oo[ind][false]["wkicm_bars"]:=[];
            end if;
            if assigned S`WKICM_bar then
                Include(~oo[ind][true],S);
            else
                indS:=Index(oo[ind][false]["orders"],S);
                if indS eq 0 then //this is the first time we see S.
                    Append(~oo[ind][false]["orders"],S);
                    Append(~oo[ind][false]["wkicm_bars"],[S!!I]);
                else
                    Append(~oo[ind][false]["wkicm_bars"][indS],S!!I);
                end if;
            end if;
        end for;
        oo_E:=[];
        for ind in Keys(oo) do
            oo_E cat:=Setseq(oo[ind][true]);
            for iS in [1..#oo[ind][false]["orders"]] do
                S:=oo[ind][false]["orders"][iS];
                S`WKICM_bar:=oo[ind][false]["wkicm_bars"][iS];
                Append(~oo_E,S);
            end for;
        end for;
        E`OverOrders:=oo_E;
    end if;
    assert2 &+[ #S`WKICM_bar : S in OverOrders(E) ] eq #wk;
    return wk;
end function;

intrinsic WeakEquivalenceClassMonoidWR(isog::IsogenyClassFq)->SeqEnum[AlgEtQIdl]
{We compute the weak equivalence class monoid of WR exploiting the fact that WR is stable the BarOnDieudonneAlgebra and SigmaOnDieudonneAlgebra.}
    _,_,_,_,A,_,OA,Delta_map,WR:=DieudonneAlgebraCommEndAlg(isog);
    if not assigned WR`WKICM then
        PPs0,PPs01,PPs1:=PrimesOfSAbove_p(isog,WR);
        p:=CharacteristicFiniteField(isog);
        assert #PPs01 le 1;
        assert2 {BarOnIdeal(isog,PP):PP in PPs0} eq Seqset(PPs1);
        local_wks:=AssociativeArray(); // to store the wkicm's above each prime
        if #PPs0 eq 0 then
            // Early exit, we cannot really optimize
            return WKICM(WR);
        end if;
        
        // Slope in (0,1), if any.
        if #PPs01 eq 1 then
            PP:=PPs01[1];
            WR_PP:=local_order(WR,PP,OA,p);
            local_wks[PP]:=[WR!!I : I in WKICM(WR_PP)];
        end if;

        // Slope 0
        q:=FiniteField(isog);
        _,a:=IsPowerOf(q,p);
        R:=ZFVOrder(isog);
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        pps:=PrimesAbove(p*R);
        pps0:=[P:P in pps|not pi in P and q/pi in P];
        if exists{P:P in pps0|GCD(a,Ilog(p,Index(R,P))) gt 1} then
            ff:=Conductor(WR);
            prod:=[PP:PP in PPs0|not ff subset PP] cat 
                 [PP:PP in PPs01|not ff subset PP] cat
                 [PP:PP in PPs0|not ff subset PP];
            if #prod gt 0 then
                ff*:=&*prod; // we want to use apply sigma also on max ideals which can be invertible
            end if;
            OAff,mOAff,sigma:=SigmaOnQuotientOfOA(isog,OA!!ff);
            apply_sigma:=func<I|Ideal(WR,[z@mOAff@sigma@@mOAff:z in ZBasis(I)] cat ZBasis(ff))>;
        end if;
        PPs0_copy:=PPs0;
        PPs0_arr:=AssociativeArray();
        for P in pps0 do
            above_P:=[PP:PP in PPs0_copy|forall{x:x in Generators(P)|Delta_map(x) in PP}];
            PPs0_arr[P]:=above_P;
            for Q in above_P do
                Exclude(~PPs0_copy,Q);
            end for;
            PP:=above_P[1];
            WR_PP:=local_order(WR,PP,OA,p);
            local_wks[PP]:=[WR!!I : I in WKICM(WR_PP)];
            above_P_sort:={PP};
            for i in [2..#above_P] do
                PP_old:=PP;
                PP:=apply_sigma(PP_old);
                Include(~above_P_sort,PP);
                assert forall{I:I in local_wks[PP_old]| ff subset I and I subset WR!!OneIdeal(OA)};
                local_wks[PP]:=[apply_sigma(I):I in local_wks[PP_old]];
            end for;
            assert2 Seqset(above_P) eq above_P_sort;
        end for;

        // Slope 1
        for PP in PPs1 do
            PPb:=BarOnIdeal(isog,PP);
            assert IsDefined(local_wks,PPb);
            local_wks[PP]:=[BarOnIdeal(isog,I): I in local_wks[PPb]];
        end for;

        // Glueing the local data
        output:=glue_local_wks(WR,local_wks,p);

        assert3 #output eq #wk_test and 
                forall{I:I in output|exists{J:J in wk_test|IsWeaklyEquivalent(I,J)}}
                where wk_test:=WKICM(WR);
        WR`WKICM:=output;
    end if;
    return WR`WKICM;
end intrinsic;

/*
    
    SetDebugOnError(true);
    SetAssertions(2);

    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    fld:="~/IsomClAbVarFqCommEndAlg/examples/";
    PP<x>:=PolynomialRing(Integers());
    check:=Split(Pipe("ls " cat fld,"r"));
    inputs:=[
    //<x^6-3*x^4+2*x^3-12*x^2+64,"3.4.a_ad_c">,
    //<x^6+2*x^5-x^4-6*x^3-4*x^2+32*x+64,"3.4.c_ab_ag">,
    //<(x^2-2*x+4)*(x^2+2*x+4),"2.4.a_e">,
    <x^8+x^7+x^6+4*x^5-4*x^4+16*x^3+16*x^2+64*x + 256,"4.4.b_b_e_ae">,
    <x^8 - 6*x^7 + 18*x^6 - 36*x^5 + 68*x^4 - 144*x^3 + 288*x^2 - 384*x + 256,"4.4.ag_s_abk_cq">,
    <x^6 + 11*x^5 + 60*x^4 + 208*x^3 + 480*x^2 + 704*x + 512,"3.8.l_ci_ia">,
    <x^6 - x^5 - 3*x^4 + 45*x^3 - 27*x^2 - 81*x + 729,"3.9.ab_ad_bt">
    ];

    for input in inputs do
        h,file:=Explode(input);
        assert IsSquarefree(h);

        isog:=IsogenyClass(h);
        _,_,_,_,_,_,_,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        t0:=Cputime();
        new:=#WeakEquivalenceClassMonoidWR(isog);
        t_new:=Cputime(t0);

        isog:=IsogenyClass(h);
        _,_,_,_,_,_,_,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        t0:=Cputime();
        old:=#WKICM(WR);
        t_old:=Cputime(t0);

        test:=new eq old select "OK " else "ERR";

        p:=CharacteristicFiniteField(isog);
        q:=FiniteField(isog);
        a:=Ilog(p,q);
        R:=ZFVOrder(isog);
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        pps:=PrimesAbove(p*R);
        pps0:=[P:P in pps|not pi in P and q/pi in P];
        gnus:=[GCD(a,Ilog(p,Index(R,P))):P in pps0];
        
        printf "%o\tt_old=%o\tt_new=%o\tgnus_0=%o\t%o\n",test,t_old,t_new,gnus,file;
    end for;
       
*/

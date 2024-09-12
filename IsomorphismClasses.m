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

declare verbose IsomClNotLocalLocal, 3;
declare verbose IsomAbVar, 3;

intrinsic IsomorphismClassesAwayFromLocalLocalCommEndAlg(isog::IsogenyClassFq)->SeqEnum[AlgEtQIdl]
{Returns a sequence of fractional ZFVOrder-ideals representing the local isomorphism classes for all primes different from the characteristic p, the local-étale part and the étale-local part of the ZFVOrder of isog.}
    // we compute the isomorphism classes of the part at ell\neq p, slope 0 and slope 1;
    // recall that these 3 parts can be done using R ideals: no need to extend;
    require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
    R:=ZFVOrder(isog);
    E:=Algebra(R);
    pi:=PrimitiveElement(E);
    //h:=DefiningPolynomial(E);
    g:=Dimension(isog);
    q:=FiniteField(isog);
    t,p,a:=IsPrimePower(q);
    assert t;
    O:=MaximalOrder(E);
    indOR:=Index(O,R);
    vp_indOR:=Valuation(indOR,p);

    ps:=[];
    sing:=SingularPrimes(R);
    sing_ell:=SingPrimesOfZFVAwayFrom_p(isog);
    ppR_0,_,ppR_1:=PrimesOfZFVAbove_p(isog);
    sing_0:=[P:P in ppR_0|P in sing];
    sing_1:=[P:P in ppR_1|P in sing];

    part_ell:=[];
    for ell in sing_ell do
        l:=MinimalInteger(ell);
        Append(~ps,l);
        assert IsPrime(l);
        vl:=Valuation(indOR,l);
        R_ell:=Order( ZBasis(R) cat ZBasis(O!!ell^vl) );
        Append(~part_ell, [ R!!I : I in WKICM(R_ell) ]);
    end for;

    // slope 0 and 1
    part_0:=[];
    part_1:=[];
    for P in sing_0 do
        Append(~ps,p);
        Append(~ps,p);
        R_P:=Order( ZBasis(R) cat ZBasis(O!!P^vp_indOR));
        Append(~part_0, [ R!!I : I in WKICM(R_P) ]);
        Append(~part_1, [ R!!ComplexConjugate(I) : I in WKICM(R_P) ]);
    end for;
    
    pp:=&cat[sing_ell,sing_0,sing_1];
    wk_pp:=&cat[part_ell,part_0,part_1];
    if #pp eq 0 then
    //early exit
        return [OneIdeal(R)],[];
    end if;

    wk_pp_idls:=[];
    pp_pows:=[];
    t1:=Cputime();
    vprintf IsomClNotLocalLocal,2 : "We make all the local parts integral\n";
    for ip->wk in wk_pp do
       wk_exps:=[];
       wk_idls:=[];
       for i in [1..#wk] do
           I:=wk[i];
           if not IsIntegral(I) then
               I:=SmallRepresentative(I); // I c E with small norm
           end if;
           k:=Valuation(Index(R,I),ps[ip]);
           Append(~wk_exps,k);
           Append(~wk_idls,I);
       end for;
       k_ip:=Max(wk_exps);
       Pk_ip:=pp[ip]^k_ip; // for every local representative I at pp[ip] we have that Pk_ip c I (locally)
       ZBasisLLL(Pk_ip);
       Append(~pp_pows,Pk_ip);
       Append(~wk_pp_idls,wk_idls);
    end for;
    vprintf IsomClNotLocalLocal,2 : "...Done in %o secs.\n",Cputime(t1);
       
    n:=#pp;
    t0:=Cputime();
    vprintf IsomClNotLocalLocal,2 : "We compute the \prod_{j \\ne i} P_j^k_j\n";
    prod_j_ne_i:=[ ];
    for i in [1..n] do
       if n eq 1 then
          prod:=OneIdeal(R);
       else
          prod:=&*[ pp_pows[j] : j in [1..n] | j ne i ];
       end if;
       ZBasisLLL(prod);
       Append(~prod_j_ne_i,prod);
    end for;
    vprintf IsomClNotLocalLocal,2 : "\t...Done in %o secs.\n",Cputime(t0);

    t0:=Cputime();
    vprintf IsomClNotLocalLocal,2 : "We modify each entry of the cartesian product\n";
    for ip in [1..n] do
       for i in [1..#wk_pp_idls[ip]] do
           I:=(wk_pp_idls[ip][i]+pp_pows[ip])*prod_j_ne_i[ip];
           ZBasisLLL(I);
           wk_pp_idls[ip][i]:=I;
       end for;
    end for;
    vprintf IsomClNotLocalLocal,2 : "\t...Done in %o secs.\n",Cputime(t0);

    t0:=Cputime();
    tot:=&*[#x : x in wk_pp_idls]; perc_old:=0; iI:=0;
    wk_pp_idls:=CartesianProduct(wk_pp_idls);
    vprintf IsomClNotLocalLocal,2 : "We start patching together the local parts\n";
    wk:=[];
    for I_Ps in wk_pp_idls do
       if GetVerbose("WKICM") ge 3 then
           iI +:=100; perc:=Truncate(iI/tot); 
           if perc gt perc_old then perc_old:=perc; printf "\t%o%% in %o secs\n",perc,Cputime(t0); end if;
       end if;
       J:=&+[ I_Ps[ip] : ip in [1..n] ];
       // J satisfies: J = I_Ps[ip] locally at pp[ip] for every ip.
       assert2 forall{ ip : ip in [1..n] | 
                                       (J+I_Ps[ip]) eq I_Ps[ip]+pp[ip]*(J+I_Ps[ip]) and 
                                       (J+I_Ps[ip]) eq J+pp[ip]*(J+I_Ps[ip])};
       Append(~wk,J);
    end for;
    vprintf IsomClNotLocalLocal,2 : "\t...Done in %o secs.\n",Cputime(t0);

    t0:=Cputime();
    vprintf IsomClNotLocalLocal,2 : "We LLL all the ZBasis\n";
    for I in wk do
       ZBasisLLL(I);
    end for;
    vprintf IsomClNotLocalLocal,2 : "\t...Done in %o secs\n",Cputime(t0);
    return wk;
end intrinsic;

glue_local_parts_orders:=function(primes,orders)
// given primes P1,...,Pn of an order R and overorders S1,...,Sn 
// returns an order S such that S_Pi = Si_Pi for every i and
// S_Q = O_Q for every other Q
    A:=Algebra(orders[1]);
    O:=MaximalOrder(A);
    R:=Order(primes[1]);
    assert forall{ P : P in primes[2..#primes] | Order(P) eq R };
    assert #primes eq #orders;
    S:=[];
    for i in [1..#primes] do
        Pi:=primes[i];
        p:=MinimalInteger(Pi);
        Si:=orders[i];
        k:=Valuation(Index(O,Si),p);    
        Append(~S,Order(ZBasis(Si) cat ZBasis(O!!Pi^k)));
    end for;
    S:=&meet(S);
    return S;
end function;

intrinsic IsomorphismClassesCommEndAlg(isog::IsogenyClassFq : IncreaseMinimumPrecisionForSemilinearFVBy:=0)->SeqEnum[AbVarFq]
{Given an isogeny class of abelian varieties over a finite field Fq, it returns representatives of the Fq-isomorphism classes in the isogeny class. The meaning of the VarArg IncreaseMinimumPrecisionForSemilinearFVBy is given in the description of IsomorphismClassesDieudonneModulesCommEndAlg.}
    require IsSquarefree(isog) : "The Weil polynomial of the isogeny class needs to be squarefree.";
    output:=[];
    places_0,places_01,places_1:=PrimesOfZFVAbove_p(isog);
    places_away_01:=SingPrimesOfZFVAwayFrom_p(isog) cat [P:P in places_0|not IsInvertible(P)] cat [P:P in places_0|not IsInvertible(P)];
    isom_away_01:=IsomorphismClassesAwayFromLocalLocalCommEndAlg(isog);
    isom_DM_01:=IsomorphismClassesDieudonneModulesCommEndAlg(isog);
    for dm in isom_DM_01 do
        dm_order:=dm`DeltaEndomorphismRing;
        dm_orders:=[ dm_order : P in places_01 ];
        for I in isom_away_01 do
            ell_01_orders:=[ MultiplicatorRing(I) : P in places_away_01 ];
            // note that if R is maximal 
            orders:=ell_01_orders cat dm_orders;
            primes:=places_away_01 cat places_01;
            assert #orders eq #primes;
            if #primes eq 0 then
                S:=ZFVOrder(I);
            else
                S:=glue_local_parts_orders(primes, ell_01_orders cat dm_orders);
            end if;
            PS,pS:=PicardGroup(S);
            for ll in PS do
                L:=pS(ll);
                X:=<I,dm,L,S>;
                Append(~output,X);
            end for;
        end for;
    end for;
    output:=[AbelianVarietyCommEndAlg(isog,tup) : tup in output ];
    return output;
end intrinsic;

















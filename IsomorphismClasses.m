/* vim: set syntax=magma : */

declare verbose IsomClTate, 3;

intrinsic IsomorphismClassesTateModules(R::AlgEtQOrd)->Any
{ TODO }
    // ################### 
    // we compute the isomorphism classes of the part at ell\neq p, slope 0 and slope 1;
    // recall that these 3 parts can be done using R ideals: no need to extend;
    
    // we separate the singular primes of R into 4 sets:
    // above ell\neq p; slope 0; slope in (0,1); slope 1.

    //TODO if there are no sing primes then the output is empty
   
    E:=Algebra(R);
    pi:=PrimitiveElement(E);
    O:=MaximalOrder(E);
    indOR:=Index(O,R);
    pi:=PrimitiveElement(E);
    h:=DefiningPolynomial(E);
    g:=Degree(h) div 2;
    q:=Truncate(ConstantCoefficient(h)^(1/g));
    t,p,a:=IsPrimePower(q);
    assert t;
    vp_indOR:=Valuation(indOR,p);

    ps:=[];
    sing:=SingularPrimes(R);
    sing_ell:=[];
    sing_0:=[];
    sing_1:=[];
    for P in sing do
        ind:=Index(R,P);
        if IsCoprime(ind,p) then
            Append(~sing_ell,P);
        else
            sP:=Slope(P);
            if sP eq 0 then
                Append(~sing_0,P);
                Append(~sing_1,ComplexConjugate(P));
            end if;
        end if;
    end for;

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
    vprintf IsomClTate,2 : "We make all the local parts integral\n";
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
    vprintf IsomClTate,2 : "...Done in %o secs.\n",Cputime(t1);
       
    n:=#pp;
    t0:=Cputime();
    vprintf IsomClTate,2 : "We compute the \prod_{j \\ne i} P_j^k_j\n";
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
    vprintf IsomClTate,2 : "\t...Done in %o secs.\n",Cputime(t0);

    t0:=Cputime();
    vprintf IsomClTate,2 : "We modify each entry of the cartesian product\n";
    for ip in [1..n] do
       for i in [1..#wk_pp_idls[ip]] do
           I:=(wk_pp_idls[ip][i]+pp_pows[ip])*prod_j_ne_i[ip];
           ZBasisLLL(I);
           wk_pp_idls[ip][i]:=I;
       end for;
    end for;
    vprintf IsomClTate,2 : "\t...Done in %o secs.\n",Cputime(t0);

    t0:=Cputime();
    tot:=&*[#x : x in wk_pp_idls]; perc_old:=0; iI:=0;
    wk_pp_idls:=CartesianProduct(wk_pp_idls);
    vprintf IsomClTate,2 : "We start patching together the local parts\n";
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
    vprintf IsomClTate,2 : "\t...Done in %o secs.\n",Cputime(t0);

    t0:=Cputime();
    vprintf IsomClTate,2 : "We LLL all the ZBasis\n";
    for I in wk do
       ZBasisLLL(I);
    end for;
    vprintf IsomClTate,2 : "\t...Done in %o secs\n",Cputime(t0);
    return wk,pp;
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

intrinsic IsomorphismClassesAbelianVarieties(R::AlgEtQOrd)->Any
{ TODO }
    output:=[];
    isom_away_01,places_away_01:=IsomorphismClassesTateModules(R);
    isom_DM_01,places_01:=IsomorphismClassesDieudonneModules(R);
    for dm in isom_DM_01 do
        dm_order:=dm`DeltaEndomorphismRing;
        dm_orders:=[ dm_order : P in places_01 ];
        for I in isom_away_01 do
            ell_01_orders:=[ MultiplicatorRing(I) : P in places_away_01 ];
            orders:=ell_01_orders cat dm_orders;
            primes:=places_away_01 cat places_01;
            assert #orders eq #primes;
            if #primes eq 0 then
                S:=R;
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

    //TODO add tests! see test_specific_ex.txt for some good tests

    return output;
end intrinsic;

















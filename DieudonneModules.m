/* vim: set syntax=magma : */
/*
    TODO
    - 'Duality', i.e. the induced complex conjugation on A, allow us to compute only for place with slope <= 1/2.
        Need to implement it.
*/

declare verbose DieudonneModules,3;
declare verbose DieudonneModules_L,3;
declare verbose Algorithm_3,3;

declare attributes AlgEtQIdl : DeltaEndomorphismRing;

slope_E:=function(P)
// given a prime of R returns the slope of P
// see beginning of 4.3.1, for the definition
// TODO we should store the slope of P, mm and all other primes above P
    E:=Algebra(P);
    O:=MaximalOrder(E);
    pp:=PrimesAbove(O!!P);
    mm:=pp[1];
    _,comp:=IsProductOfIdeals(mm);
    ind:=[ i : i in [1..#comp] | not NumberField(Order(comp[i]))!1 in comp[i] ];
    assert #ind eq 1;
    ind:=ind[1];
    mm:=comp[ind];
    pi:=PrimitiveElement(Algebra(P));
    h:=DefiningPolynomial(E);
    g:=Degree(h) div 2;
    q:=Truncate(ConstantCoefficient(h)^(1/g));
    t,p,a:=IsPrimePower(q);
    assert t;
    pi_ind:=Components(pi)[ind];
    val_pi:=Valuation(pi_ind,mm);
    e_mm:=RamificationIndex(mm);
    return val_pi/(a*e_mm);
end function;

intrinsic IsomorphismClassesDieudonneModules(R::AlgEtQOrd)->Any
{}
    E:=Algebra(R);
    pi:=PrimitiveElement(E);
    h:=DefiningPolynomial(E);
    g:=Degree(h) div 2;
    q:=Truncate(ConstantCoefficient(h)^(1/g));
    t,p,a:=IsPrimePower(q);
    assert t;

    places_01_E:=function(E)
    // returns the places of E_p of slope in (0,1)
        return [ P : P in PrimesAbove(p*MaximalOrder(E)) | 0 lt sp and sp lt 1 where sp:=slope_E(P) ]; 
    end function;

    pl_01_E:=places_01_E(E);
    pl_01_R:=Setseq({ OneIdeal(R) meet (R!!P) : P in pl_01_E });
    if #pl_01_E ne 0 then
        assert #pl_01_R eq 1;
    end if;

    vprintf DieudonneModules,2 : "number of places nu of E with s(nu) in (0,1) = %o\n",#pl_01_E;
    // Early exit if no places 
    if #pl_01_E eq 0 then
        dm:=OneIdeal(R);
        dm`DeltaEndomorphismRing:=R;
        return [dm],pl_01_E; 
    end if;

    // ################### 
    // Global Representatives: tilde A, tilde W_R, etc . 
    // I dropped the tilde from the notation...I don't hate my life enough.
    // ###################
    prec:=30; //TODO this precision parameter should kept in place
    hL:=Parent(h)!DefiningPolynomial(CyclotomicUnramifiedExtension(pAdicField(p,prec),a));
    vprintf DieudonneModules_L,2 : "Degree of hL = %o,%o\n",Degree(hL),hL;
    L<zeta>:=NumberField(hL : DoLinearExtension:=true);
    vprintf DieudonneModules_L,2 : "L = %o\n",L;
    sigma_L:=hom< L->L | [ zeta^p ] >; //does not have inverse
    OL:=MaximalOrder(L);
    zb_OL:=Basis(OL);
    // tests
        assert sigma_L(2) eq 2;
        test:=[ i eq 1 select zeta else sigma_L(Self(i-1)) : i in [1..a+1] ];
        assert test[#test] eq zeta;
        for z in zb_OL do
            zz:=[ i eq 1 select z else sigma_L(Self(i-1)) : i in [1..a+1] ];
            assert zz[#zz] eq z;
        end for;
    // end tests

    fac_h_L:=Factorization( PolynomialRing(L) ! h );
    assert forall{ g : g in fac_h_L| g[2] eq 1 };
    nfs_A:=[ NumberField(g[1]) : g in fac_h_L ];
    nfs_A_abs:=[ AbsoluteField(nf) : nf in nfs_A ];

    // A: an etale algrebra over Q. isomorphic to L \otimes E
    A:=EtaleAlgebra(nfs_A_abs);
    OA:=MaximalOrder(A);
    vprintf DieudonneModules_L,2 : "A = %o\n",A;
    _,embs_A,proj_A:=Components(A);

    // inclusion L in A
    emb_L_inA:=map< L -> A | x:->&+[ embs_A[i](nfs_A_abs[i]!x) : i in [1..#nfs_A] ]>;
    zb_OL_inA:=[ emb_L_inA(x) : x in zb_OL ];

    // pi in A
    pi_A_comps:=<  >;
    for i in [1..#nfs_A] do
        test,pi_i:=HasRoot(fac_h_L[i][1],nfs_A[i]);
        assert test;
        pi_i:=nfs_A_abs[i]!pi_i;
        Append(~pi_A_comps,pi_i);
    end for;
    pi_A:=A!pi_A_comps;
    assert MinimalPolynomial(pi_A) eq h;
    pows_pi_A:=[ pi_A^i : i in [0..Dimension(E)-1 ]];

    // #######################
    // Delta: E->A, the natural embedding
    // #######################

    OrderAsFreeAbelianGroup:=function(R)
    // Returns F,f where F is a free abelian group isomorphic to R and f is an isomorphism.
    // It depends on the stored ZBasis(R)
        n:=Dimension(Algebra(R));
        F:=FreeAbelianGroup(n);
        zb:=ZBasis(R);
        f:=map<R->F | x:->F!AbsoluteCoordinates([x],zb),
                      y:->SumOfProducts(Eltseq(y),zb) >;
        return F,f;
    end function;

    FOA,fOA:=OrderAsFreeAbelianGroup(OA);

    assert forall{ z : z in ZBasis(OA) | fOA(z)@@fOA eq z };

    Delta_image:=function(z)
        out:=SumOfProducts(AbsoluteCoordinates([z],PowerBasis(E))[1],pows_pi_A);
        assert MinimalPolynomial(out) eq MinimalPolynomial(z);
        return out;
    end function;

    imageDeltaOE_inFOA:=sub<FOA | [fOA(Delta_image(z)) : z in ZBasis(MaximalOrder(E)) ]>;

    mat_pows_pi_A:=Matrix([AbsoluteCoordinates(x) : x in pows_pi_A ]);
    Delta_preimage:=function(y)
        // Need to write y as a linear combination of pows_pi_A
        // Use Solution V to V*X =W
        W:=Matrix([AbsoluteCoordinates(y)]);
        return SumOfProducts(Eltseq(Solution(mat_pows_pi_A,W)),PowerBasis(E));
    end function;

    Delta_map:=map< E->A | z:->Delta_image(z),
                           y:->Delta_preimage(y) >;

    // TEST
    assert forall{ z : z in ZBasis(MaximalOrder(E)) | z eq (Delta_map(z))@@Delta_map }; 
    assert forall{ z : z in ZBasis(R) | z eq (Delta_map(z))@@Delta_map }; 

    // #######################
    // tilde W_R: order isomorphic to W \otimes R
    // #######################
  
    pi_A_bar:=q/pi_A;
    gens_WR:=&cat[[ z,z*pi_A,z*pi_A_bar ] : z in zb_OL_inA] cat [pi_A, pi_A_bar];

    // gens_WR:=&cat[ [ embs_A[i](nfs_A_abs[i]!z*pi_A_comps[i]) , //z*pi
    //                 embs_A[i](nfs_A_abs[i]!z*q/pi_A_comps[i]) ] : i in [1..#nfs_A], //z*q/pi
    //                 z in zb_OL ]; //OL=W
    
    WR:=Order(gens_WR);

    // test
    assert pi_A in WR;
    assert q/pi_A in WR;
    assert Index(OA,WR) ge Index(MaximalOrder(E),R);
    // end test

    // #######################
    // tilde sigma: acts as zeta:->zeta^q on L-coefficients on each compoenent of A
    // #######################

    sigma_image:=function(x)
        x_comp:=Components(x);
        N:=#x_comp;
//        img:=<>;
//        for i in [1..N] do
//            BL:=nfs_A[i]; // nf over L
//            BQ:=nfs_A_abs[i]; // nf over Q
//            assert x_comp[i] eq BQ!(BL!Eltseq(BL!x_comp[i]));
//            img_i:=BQ!(BL![ sigma_L(c) : c in Eltseq(BL!x_comp[i])]);
//            Append(~img,img_i);
//        end for;
//        //the next line deos the same.
        img:=< nfs_A_abs[i]!nfs_A[i]![sigma_L(c) : c in Eltseq(nfs_A[i]!x_comp[i])] : i in [1..N] > ;
        return A!img;
    end function;
    sigma:=map< A-> A | x:->sigma_image(x) >; //does not have inverse
    assert forall{ x : x in [ Delta_map(y) : y in ZBasis(MaximalOrder(E))] | x eq sigma(x) };

    // #######################
    // primes of orders in A above places
    // #######################
    // TODO I should make a new type Place_E, or an array or record for each place of E in which I store 
    // the slope, the primes of OA above E, and maybe? the primes of each overorder S above E
    // Then there should be a record of Places_R which points to Places_E

    primes_of_A_above_place_of_E:=function(A,P)
    // given a maximal ideal P of OE returns the maximal ideals of OA above P
        OA:=MaximalOrder(A);
        return PrimesAbove(Ideal(OA,[ Delta_map(z) : z in ZBasis(P)]));
    end function;
    
    primes_of_S_above_place_of_E:=function(S,P)
    // given a maximal ideal P of OE and an order S of A returns the maximal ideals of S above P
        oneS:=OneIdeal(S);
        A:=Algebra(S);
        pp:=primes_of_A_above_place_of_E(A,P);
        pp:=[ oneS meet (S!!P) : P in pp ];
        return Setseq(Seqset(&cat[PrimesAbove(P) : P in pp ]));
    end function;

    //////////////////
    // Units quotient
    //////////////////
    // Let S be an order in A', containing R'. We want to compute OA'^*/S^*\Delta'(O_E'^*)

// OLD version. Commented out on 20240314
//    units_quotient_P:=function(S,P)
//    // Given an order S in A and a prime P of S, it computes U:=O_{A,P}^*/S_P^*,
//    // where OA is the maximal order of A, together with map u:U->OA
//    // This is based on Lemma ADDREF
//        assert Order(P) eq S;
//        if IsInvertible(P) then
//            // early exit: in this case S is P-maximal, that is, O_{A,P} = S_P.
//            U:=AbelianGroup([1]); //trivial groups
//            A:=Algebra(S);
//            u:=map<U->A | x:->One(A), y:->Zero(U) >; //trivial map
//            return U,u;
//        end if;
//
//
//        q:=Index(S,P);
//        t,p:=IsPrimePower(q);
//        assert t; delete t; delete q;
//        OA:=MaximalOrder(Algebra(S));
//        ff:=Conductor(S);
//        ffOA:=OA!!ff;
//
//        pp_OA:=PrimesAbove(OA!!P);
//        Us:=[];
//        us:=<>;
//        for PP in pp_OA do
//        //TODO FIXME is M big enough?
//            M:=Valuation(Index(OA,ffOA),p); // PP^M c ff locally at PP
//            U,u:=ResidueRingUnits(OA,ffOA+PP^M); // u: U=(OA/ff+PP^M)^* -> OA
//            assert forall{ g : g in Generators(U) | (u(g))@@u eq g};
//            Append(~Us,U);
//            Append(~us,u);
//        end for;
//        n:=#pp_OA;
//        vprintf DieudonneModules,2 : "#pp_AO = %o\n",n;
//        D_OA,embs,projs:=DirectSum(Us);
//        //TODO FIXME the image of x, should be + or * ???
//        d_OA:=map< D_OA->Algebra(OA) |  x:->&*[ us[i](projs[i](x)) : i in [1..n] ],
//                                        y:->&+[ embs[i](y@@us[i]) : i in [1..n] ] >;
//        assert forall{ g : g in Generators(D_OA) | (d_OA(g))@@d_OA eq g};
//
//        //TODO FIXME is m big enough?
//        m:=Valuation(Index(S,ff),p); // P^m c ff locally at P
//        ffPm:=ff+P^m;
//        assert not 1 in ffPm;
//        gens:=ResidueRingUnitsSubgroupGenerators(ffPm);
//            // gens is a set of generators of (S/ff+P^m)^* = (S_P/ff_P)^* in A.
//        U,u0:=quo<D_OA | [ g@@d_OA : g in gens ]>; // u0:D_OA->U
//        u:=map<U->Algebra(OA) | x:->d_OA(x@@u0), y:->u0(y@@d_OA) >;
//        assert forall{ g : g in Generators(U) | (u(g))@@u eq g};
//        return U,u;
//    end function;
//
//    units_quotient_01:=function(S)
//    //TODO ADD duality here
//    // Given an order S in A, representing an order S' in A' returns U=OA'^*/S'^* and a map u:U->OA
//        primes_01_S:=&cat[ primes_of_S_above_place_of_E(S,P) : P in pl_01_E];
//        Us:=[];
//        us:=<>;
//        for P in primes_01_S do
//            U,u:=units_quotient_P(S,P);
//            Append(~Us,U);
//            Append(~us,u);
//        end for;
//        n:=#primes_01_S;
//        vprintf DieudonneModules,2 : "number of Us = %o\n",#Us;
//        U,embs,projs:=DirectSum(Us);
//        u:=map<U->Algebra(S) |  x:->&*[ us[i](projs[i](x)) : i in [1..n] ],
//                                y:->&+[ embs[i](y@@us[i]) : i in [1..n] ] >;
//        assert forall{ g : g in Generators(U) | (u(g))@@u eq g};
//        return U,u;
//    end function;

    units_quotient_01:=function(S)
    //TODO ADD duality here ??? [not necessary anymore]
    // Given an order S in A, representing an order S' in A' returns U=OA'^*/S'^* and a map u:U->OA
        primes_01_S:=&cat[ primes_of_S_above_place_of_E(S,P) : P in pl_01_E];
        ff:=Conductor(S);
        primes_01_S_above_ff:=[ P : P in primes_01_S | ff subset P];
        assert forall{P : P in primes_01_S_above_ff | p in P};
        if #primes_01_S_above_ff eq 0 then
            U:=FreeAbelianGroup(0);
            // with test
            trivial_preimage:=function(y)
                assert forall{ P : P in primes_01_S_above_ff | not y in P };
                return Zero(U);
            end function;
            u:=map<U->Algebra(S) | x:->One(S), y:->trivial_preimage(y)>;
            // without test
            //u:=map<U->Algebra(S) | x:->One(S), y:->Zero(U)>;
            return U,u;
        end if;
        indff:=Index(S,ff);
        assert forall{P : P in primes_01_S_above_ff | indff mod Index(S,P) eq 0 };
        ks:=[ Valuation(indff,p) div Valuation(Index(S,P),p) : P in primes_01_S_above_ff ];
        prod:=&*([ primes_01_S_above_ff[i]^ks[i] : i in [1..#primes_01_S_above_ff]]);
        ff_prod:=ff+prod;
        assert not 1 in ff_prod;
        R,r:=ResidueRingUnits(OA!!(ff_prod));
        gens:=ResidueRingUnitsSubgroupGenerators(ff_prod);
        U,u0:=quo<R | [ g@@r : g in gens]>;
        u:=map<U->Algebra(S) |  x:-> r(x@@u0), y:->u0(y@@r) >;
        assert forall{ g : g in Generators(U) | (u(g))@@u eq g};
        return U,u;
    end function;

    fixed_pts_sigma:=function(S,sigma)
    // Given an order S in A, representing an order S' in A', 
    // which is stable by the action of sigma (eg. WR),
    // returns U,u,F where
    // U=OA'^*/S'^*,
    // u is a map u:U->OA giving representatives 
    // F is the subgroup of elements of U=OA'^*/S'^* fixed by sigma
        U,u:=units_quotient_01(S); //u:U->A
        Ugens_inA:=[ u(U.i) : i in [1..Ngens(U)] ];
        id_sigma:=hom< U->U | [ (x/sigma(x))@@u : x in Ugens_inA ]>;
        F:=Kernel(id_sigma);
        return U,u,F;
    end function;

    // only for WR: F = Delta(OE')^*W'R^*/W'R^* inside OA'^*/W'R^*
    U,u,F:=fixed_pts_sigma(WR,sigma);
    units_quotient_fixed_sigma_WR_gens:=[u(F.i) : i in [1..Ngens(F)]];
    delete U,u,F;

    units_quotient_fixed_sigma:=function(S,sigma)
    // Given an order S in A, representing an order S' in A', returns Q,q where
    // Q = OA'^*/S'^*Delta(OE'^*) 
    // q is a map Q->OA giving representatives
        U,u:=units_quotient_01(S); //u:U=OA'^*/S'^* -> A
        fixed_pts_gens:=[ g@@u : g in units_quotient_fixed_sigma_WR_gens];
        Q,q0:=quo<U|fixed_pts_gens>; //q0: U->U/F=Q
        q:=map<Q->Algebra(S) |  x:->u(x@@q0), y:->q0(y@@u) >;
        return Q,q;
    end function;

    // TEST : FIXME this test is time consuming and I am computing stuff for orders that 
    // might not be useful later
    oo:=OverOrders(WR);
    for iS->S in oo do
        U,u:=units_quotient_fixed_sigma(S,sigma);
        UE,uE:=UnitGroup(MaximalOrder(E));
        assert forall{ x : x in [ Delta_map(uE(y)) : y in Generators(UE)] | x eq sigma(x) };
    end for;


    //TODO 
    // - the following 3 functions should be intrinsics. 
    // - using the build it intrinsics for number fields is probably faster 
    // (maybe they use p-adics factorizations); 
    // - everything should be cached as attributs.
    inertia_degree:=function(P)
        q:=Index(Order(P),P);
        t,p,f:=IsPrimePower(q);
        assert t;
        return f;
    end function;

    valuation_elt:=function(x,P)
    // only for x in Order(P) = Maximal
        fac:=Factorization(x*Order(P));
        pps:=[ g[1] : g in fac ];
        ind:=Index(pps,P);
        assert (ind ne 0) eq (x in P);
        if ind eq 0 then
            return 0;
        else
            return fac[ind][2];
        end if;
    end function;
    
    valuation_idl:=function(J,P)
    // Order(J) = Order(P) = Maximal
        assert J subset Order(J);
        if One(Algebra(J)) in J then 
            return 0;
        end if;
        fac:=Factorization(J);
        pps:=[ g[1] : g in fac ];
        ind:=Index(pps,P);
        assert (ind ne 0) eq (J subset P);
        if ind eq 0 then
            return 0;
        else
            return fac[ind][2];
        end if;
    end function;

    ramification_index:=function(P)
        q:=Index(Order(P),P);
        t,p:=IsPrimePower(q);
        assert t;
        return valuation_elt(p,P);
    end function;

    exponents_from_Waterhouse:=function(P)
        f_nu:=inertia_degree(P);
        g_nu:=GCD(a,f_nu); //q=p^a
        e_nu:=ramification_index(P);
        exps:=[];
        // this is naive.
        cp:=CartesianProduct([ [0..e_nu] : i in [1..g_nu]]);
        for tup0 in cp do
            tup:=[ tup0[i] : i in [1..g_nu] ];
            if &+tup eq Integers()!(g_nu*valuation_elt(pi,P)/a) then
                exp:=[ i eq 1 select 0 else Self(i-1) + tup[i-1] : i in [1..g_nu]];
                Append(~exps,exp);
            end if;
        end for;
        return exps;
    end function;
    
    // ####################
    // Algorithm 2
    // ####################

    nice_uniformizers:=function(PPAs)
    // given the list of maximal ideals of A, it returns a seqence of elements t_P in A such that 
    // t_P is a uniformizer of P and a unit at every Q\neq P
        A:=Algebra(PPAs[1]);
        PPAs:=[ P^2 : P in PPAs ];
        one:=One(A);
        nice_unifs:=[];
        for iP->P in PPAs do
            P2:=P^2;
            Q,q:=Quotient(P,P2);
            repeat
                t:=Random(Q);
            until t ne Zero(Q);
            tP:=t@@q;
            while IsZeroDivisor(tP) do
                tP +:=Random(P2);
            end while;
            if #PPAs gt 1 then
                elts:=[ i eq iP select tP else one : i in [1..#PPAs] ];
                tP:=CRT(PPAs,elts);
            end if;
            assert not IsZeroDivisor(tP);
            Append(~nice_unifs,tP);
        end for;
        return nice_unifs;
    end function;

    // TODO add duality here!
    exps_nus:=[];
    pp_A_nus:=[];
    for P in pl_01_E do
        Append(~exps_nus,exponents_from_Waterhouse(P));
        Append(~pp_A_nus,primes_of_A_above_place_of_E(A,P));
    end for;
    exps_nus_cc:=CartesianProduct(exps_nus);
    exps_01:=[];
    for cc in exps_nus_cc do
        Append(~exps_01,&cat[ c : c in cc ]); 
    end for;
    pp_A_01:=&cat(pp_A_nus);
    nice_unifs_01:=nice_uniformizers(pp_A_01);

    // We compute the W'_R-isomorpshim classes of W'_R-ideals.
    k:=Valuation(Index(OA,WR),p);
    WR_01:=Order( ZBasis(WR) cat ZBasis(OA!!&*[ P^k : P in pp_A_01 ]));
    // TODO CHECKME this order is locally isomorphic to WR' at every place of slope 01
    wk_01:=[ SmallRepresentative(WR!!I) : I in WKICM(WR_01)];

    WR_01_idls_with_ext_i_to_OA_F_V_stable:=[];
    for I in wk_01 do
        S:=MultiplicatorRing(I);
        J:=OA!!I;
        valsJ:=[ valuation_idl(J,P) : P in pp_A_01 ];
        deltas:=[];
        for exps in exps_01 do
            vprintf DieudonneModules,2 : "#exps = %o #pp_A_01 =%o\n",#exps,#pp_A_01;
            assert #exps eq #pp_A_01; 
            Append(~deltas,&*[nice_unifs_01[i]^(valsJ[i]-exps[i]) : i in [1..#pp_A_01]]);
        end for;
        // the following two lines should be cached
        QS,qS:=units_quotient_fixed_sigma(S,sigma);
        gammas:=[ qS(x) : x in QS ];

        assert forall{ d : d in deltas | not IsZeroDivisor(d) };
        assert forall{ g : g in gammas | not IsZeroDivisor(g) };
        II:=[ d*g*I : d in deltas, g in gammas ];
        WR_01_idls_with_ext_i_to_OA_F_V_stable cat:=II;
    end for;

    //printf "number of WR'-isomorphism classes %o\n",#WR_01_idls_with_ext_i_to_OA_F_V_stable;
   
    // ####################
    // Delta_inverse_ideal
    // ####################

    Delta_inverse_ideal:=function(I)
    // given a fractional-WR ideal returns Delta^{-1}(I), which is a fractional R-ideal
        assert Order(I) eq WR;
        dI,d:=MakeIntegral(I);
        dI_inFOA:=sub<FOA | [fOA(z) : z in ZBasis(dI) ]>;
        gens_dI_meet_DeltaOE:=[ (g@@fOA)@@Delta_map : g in Generators(dI_inFOA meet imageDeltaOE_inFOA) ];
        J:=(1/d)*Ideal(R,gens_dI_meet_DeltaOE);
        assert forall{z : z in ZBasis(J) | Delta_map(z) in I};
        return J;
    end function;

    //TEST Delta_inverse_ideal
    for I in WR_01_idls_with_ext_i_to_OA_F_V_stable do
        _:=Delta_inverse_ideal(I);
    end for;

    // ####################
    // Algorithm 3
    // ####################
 
    exps:=exps_01[1];
    J:=WR !! Ideal(OA,&*[nice_unifs_01[i]^exps[i] : i in [1..#pp_A_01]]);

    // We scale the ideals I by elements of E so that they are in J
    // We want to keep J/xI small
    for i in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        I:=WR_01_idls_with_ext_i_to_OA_F_V_stable[i];
        x:=ShortElement(Delta_inverse_ideal(ColonIdeal(J,I)));
        WR_01_idls_with_ext_i_to_OA_F_V_stable[i]:=Delta_map(x)*I;
    end for;

    // FIXME the next lines seem to give the wrong answers
    //m0:=Maximum([ Valuation(Exponent(Quotient(J,I)),p) : I in WR_01_idls_with_ext_i_to_OA_F_V_stable ] cat
    //            [ valuation_elt( pi, P ) : P in pl_01_E ]);
    
    m0:=Maximum([ ramification_index(P)*Valuation(Exponent(Quotient(J,I)),p) : 
                    I in WR_01_idls_with_ext_i_to_OA_F_V_stable , P in pl_01_E ] cat
                [ valuation_elt( pi, P ) : P in pl_01_E ]);
    
    //"WARNING: m0 is forced now"; m0:=10; //to force it bigger
    
    vprintf Algorithm_3 : "vp(Nk)'s = %o\n",[ Valuation(Exponent(Quotient(J,I)),p) : I in WR_01_idls_with_ext_i_to_OA_F_V_stable ];
    vprintf Algorithm_3 : "v_nu(pi) for all nu's = %o\n",[ valuation_elt( pi, P ) : P in pl_01_E ];
    vprintf Algorithm_3 : "e_nu for all nu's = %o\n",[ ramification_index(P) : P in pl_01_E ];
    vprintf Algorithm_3 : "f_nu for all nu's = %o\n",[ inertia_degree(P) : P in pl_01_E ];
    vprintf Algorithm_3 : "g_nu for all nu's = %o\n",[ GCD(a,inertia_degree(P)) : P in pl_01_E ];
    vprintf Algorithm_3 : "m0 = %o\n",m0;

    QQs:=[];
    qqs:=<>;
    alpha_Q_inAs:=[];
    PPs_nus_prod_powers:=[];
    for inu->nu in pl_01_E do
        vprintf Algorithm_3,2 : "computing alpha_Q for %oth place of %o\n",inu,#pl_01_E;
        //TODO Add duality here
        PPs_nu:=primes_of_A_above_place_of_E(A,nu);
        f_nu:=inertia_degree(nu);
        g_nu:=GCD(a,f_nu); //q=p^a
        assert #PPs_nu eq g_nu;
      
        Rs_nu:=[];
        rs_nu:=<>;
        PPs_nu_m0_1:=[];
        for PP in PPs_nu do
            PP_m0_1:=PP^(m0+1);
            Append(~PPs_nu_m0_1,PP_m0_1);
            R,r:=ResidueRing(OA,PP_m0_1);
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
        end for;
        Append(~PPs_nus_prod_powers,&*PPs_nu_m0_1);

        Q,embs,projs:=DirectSum(Rs_nu);
        preimage_pr:=function(y)
            if g_nu eq 1 then
                return projs[1](y)@@rs_nu[1];
            else
                return CRT( PPs_nu_m0_1 ,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]]);    
            end if;
        end function;
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   //y:->&+[ projs[i](y)@@rs_nu[i] : i in [1..g_nu] ]>; //this is wrong
                                   y:->preimage_pr(y)>;
        assert forall{ x : x in Generators(Q) | pr(x@@pr) eq x};
        pi_Q:=pr(pi_A);
        vprintf Algorithm_3,2 : "looping over a set of size = %o\n",#Rs_nu[g_nu];

        tot:=#Rs_nu[g_nu];
        counter:=0; perc:=0;
        for u in Rs_nu[g_nu] do
            counter+:=1; if Truncate(100*counter/tot) gt perc then perc+:=1; vprintf Algorithm_3,2 : "%o%%, ",perc; end if; 
            alpha_Q:=&+[i lt g_nu select embs[i](rs_nu[i](One(A))) else embs[i](u) : i in [1..g_nu]]; 
            alpha_Q_inA:=alpha_Q@@pr;    
            norm:=alpha_Q_inA;
            sigma_alpha_Q:=alpha_Q_inA;
            for i in [1..a-1] do
                sigma_alpha_Q:=sigma(sigma_alpha_Q);
                norm *:= sigma_alpha_Q;
            end for;
            if pr(norm) eq pi_Q then
                break u;
            end if;
        end for;
        Append(~QQs,Q);
        Append(~qqs,pr);
        Append(~alpha_Q_inAs,alpha_Q_inA);
    end for;
    vprintf Algorithm_3,2 : "all alpha_Q's are computed\n";

    // FIXME Qm0_1 = does not have 0 and 1 components!, while Qm0 below does
    Qm0_1,embs,projs:=DirectSum(QQs);
    preimage_qm0_1:=function(y)
        if #QQs eq 1 then
            return projs[1](y)@@qqs[1];
        else
            return CRT(PPs_nus_prod_powers,[projs[i](y)@@qqs[i] : i in [1..#pl_01_E]]);
        end if;
    end function;

    qm0_1:=map<Algebra(J)->Qm0_1 |   x:->&+[ embs[i](qqs[i](x)) : i in [1..#pl_01_E] ],
                                     //y:->&+[ (projs[i](y))@@qqs[i] : i in [1..#pl_01_E] ]>; //need to use CRT
                                     y:->preimage_qm0_1(y)>;

    assert forall{ x : x in Generators(Qm0_1) | qm0_1(x@@qm0_1) eq x};
    // qm0_1: J->J/p^(m0_1)*J = Qm0_1 
    
    //FQm0_1:=hom< Qm0_1->Qm0_1 | [ &+[embs[i](qqs[i](alpha_Q_inAs[i]*sigma((projs[i](Qm0_1.j))@@qqs[i]))) : i in [1..#pl_01_E]] : j in [1..Ngens(Qm0_1)]] >; //maybe I need to use a CRT here? as below
    image_FQm0_1:=function(x)
        if #QQs eq 1 then
            return embs[1](qqs[1](alpha_Q_inAs[1]*sigma(projs[1](x)@@qqs[1])));
        else
            return qm0_1(CRT(PPs_nus_prod_powers,[(alpha_Q_inAs[i]*sigma(projs[i](x)@@qqs[i])) : i in [1..#pl_01_E]]));
        end if;
    end function;
    FQm0_1:=hom< Qm0_1->Qm0_1 | [ image_FQm0_1(Qm0_1.j) : j in [1..Ngens(Qm0_1)]] >;
    
    Qm0,qm0:=Quotient(J,p^(m0)*J);
    assert forall{ x : x in Generators(Qm0) | qm0(x@@qm0) eq x};
    pr:=map< Qm0_1->Qm0 | x:->qm0(x@@qm0_1), y:->qm0_1(y@@qm0) >;
    assert forall{ x : x in Generators(Qm0_1) | x eq pr(x)@@pr};

    //FQm0:=hom<Qm0->Qm0 | x:-> pr(FQm0_1(x@@pr)) >;
    FQm0:=hom<Qm0->Qm0 | [  pr(FQm0_1(Qm0.i@@pr)) : i in [1..Ngens(Qm0)] ] >;
    assert forall{ x : x in Generators(Qm0_1) | FQm0(pr(x)) eq pr(FQm0_1(x))};

    mp:=hom<Qm0_1->Qm0_1 | [ p*(Qm0_1.j) : j in [1..Ngens(Qm0_1)] ]>;
    assert mp eq hom<Qm0_1->Qm0_1 | [ qm0_1(p*(Qm0_1.j)@@qm0_1) : j in [1..Ngens(Qm0_1)] ]>;

    z_gamma_s:=[];
    for i in [1..Ngens(Qm0)] do
        gamma:=Qm0.i;
        x_gamma:=gamma@@pr;
        z_gamma:=(mp(x_gamma))@@FQm0_1;
        Append(~z_gamma_s,z_gamma);
    end for;
    VQm0:=hom<Qm0->Qm0 | [ pr(z_gamma_s[i]) : i in [1..Ngens(Qm0)] ] >;

    assert forall{ g : g in Generators(Qm0) | FQm0(VQm0(g)) eq p*g };
    assert forall{ g : g in Generators(Qm0) | VQm0(FQm0(g)) eq p*g };

    vprintf Algorithm_3,2 : "FQ and VQ are computed\n";

    is_F_V_stable:=function(I)
        I_Qm0:=sub<Qm0 | [qm0(z) : z in ZBasis(I) ]>;
        return I_Qm0 eq I_Qm0 + 
                        sub<Qm0 | [FQm0(z) : z in Generators(I_Qm0)] > +
                        sub<Qm0 | [VQm0(z) : z in Generators(I_Qm0)] >;
    end function;

    Delta_isom_classes_WR_F_V:=[ ];
    vprintf Algorithm_3,2 : "Started checking for F-V stability for the ...\n";
    for iI in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        vprintf Algorithm_3,2 : "%oth ideal from WR_01_idls_with_ext_i_to_OA_F_V_stable...\n",iI;
    // FIXME I need to make sure that I_P = O_{A,P} for every prime P of slope = 0 or = 1
        I:=WR_01_idls_with_ext_i_to_OA_F_V_stable[iI];
        if is_F_V_stable(I) then
            assert Order(I) eq WR;
            II:=Delta_inverse_ideal(I);
            S:=MultiplicatorRing(II);
            I`DeltaEndomorphismRing:=S;
            Append(~Delta_isom_classes_WR_F_V,I);
        end if;
    end for;

    return Delta_isom_classes_WR_F_V , pl_01_R;
end intrinsic;


/*
 
    AttachSpec("~/AlgEt/spec");
    Attach("DieudonneModules.m");
    Attach("IsomorphismClasses.m");

    //SetVerbose("DieudonneModules_L",2);
    SetVerbose("Algorithm_3",2);
    SetDebugOnError(true);

    PP<x>:=PolynomialRing(Integers());
    //h:=x^4 + 4;
    //h:=x^2 + 4;
    //h:=x^4 + 2*x^3 + 4*x^2 + 4*x + 4;
    h:=x^4 - 2*x^3 + 4*x^2 - 8*x + 16;
    h:=x^4 + x^3 - 2*x^2 + 4*x + 16;
    coeff:=Coefficients(h);
    g:=Degree(h) div 2;
    q:=Truncate(ConstantCoefficient(h)^(1/g));
    printf "%o = ",h;
    t,p,a:=IsPrimePower(q);
    assert t; delete t;
    E:=EtaleAlgebra(h);
    pi:=PrimitiveElement(E);
    R:=Order([pi,q/pi]);
    isom:=IsomorphismClassesAbelianVarieties(R);
    #isom,#ICM(R);

*/













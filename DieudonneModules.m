/* vim: set syntax=magma : */
/*
    TODO
    - 'Duality', i.e. the induced complex conjugation on A, allow us to compute only for place with slope <= 1/2.
        Need to implement it.
*/

declare verbose DieudonneModules,3;
declare verbose DieudonneModules_L,3;
declare verbose Algorithm_2,3;
declare verbose Algorithm_3,3;
declare verbose sigma,3;

declare attributes AlgEtQ    : sigma_fin_prec;
declare attributes AlgEtQOrd : units_quotient_fixed_sigma;
declare attributes AlgEtQIdl : DeltaEndomorphismRing,
                               SlopeE;

is_ring_hom_quotient_NF:=function(f,R,I)
// given an order R in some number field, I an ideal of R and f a map L->L
// it returns wheter f:R/I->R/I is a ring homomorphism
    L:=NumberField(R);
    Q,mQ:=quo<R|I>;
    gs:=[ L!b : b in Basis(R) ];
    vprintf sigma,2 : "gs = %o\n",gs;
    vprintf sigma,2 : "fs = %o\n",[ f(i) : i in gs ];
    fs:=[ R!f(i) : i in gs ]; 
    fsQ:=[ mQ(i) : i in fs ]; 
    test_add:=forall{i : i,j in [1..#gs] | mQ(R!f(gs[i]+gs[j])) eq (fsQ[i]+fsQ[j]) };
    test_mult:=forall{i : i,j in [1..#gs] | mQ(R!f(gs[i]*gs[j])) eq mQ(fs[i]*fs[j]) };
    return test_add and test_mult;
end function;

is_ring_hom_quotient_AlgEt:=function(f,R,I)
// given an order R in some AlgEt L, I an ideal of R and f a map L->L
// it returns wheter f:R/I->R/I is a ring homomorphism
    L:=Algebra(R);
    Q,mQ:=ResidueRing(R,I);
    gs:=[ L!(g@@mQ) : g in Generators(Q)];
    fs:=[ f(i) : i in gs ]; 
    fsQ:=[ mQ(f(i)) : i in gs ]; 
    test_add:=forall{i : i,j in [1..#gs] | mQ(f(gs[i]+gs[j])) eq (fsQ[i]+fsQ[j]) };
    test_mult:=forall{i : i,j in [1..#gs] | mQ(f(gs[i]*gs[j])) eq mQ(fs[i]*fs[j]) };
    return test_add and test_mult;
end function;

intrinsic SlopeE(P::AlgEtQIdl)->RngIntElt
{Given a maximal ideal P of the maximal order of the commutative endomorphism algebra E=Q[pi] of abelian varieties over Fq, with q=p^a, it returns the slope of P, which is defined as val_P(pi)/(a*e_P) where val_P(pi) is the valuation of pi at P and e_P is the ramification index of P.}
    if not assigned P`SlopeE then
        require IsMaximal(Order(P)) and IsPrime(P): "The input needs to be a maximal ideal of the maximal order.";
        E:=Algebra(P);
        pi:=PrimitiveElement(E);
        h:=DefiningPolynomial(E);
        g:=Degree(h) div 2;
        q:=Truncate(ConstantCoefficient(h)^(1/g));
        t,p,a:=IsPrimePower(q);
        assert t;
        val_pi:=Valuation(pi,P);
        eP:=RamificationIndex(P);
        P`SlopeE:=val_pi/(a*eP);
    end if;
    return P`SlopeE;
end intrinsic;

intrinsic SlopeR(P::AlgEtQIdl)->RngIntElt
{Given a maximal ideal P of any order of the commutative endomorphism algebra E=Q[pi] of abelian varieties over Fq, with q=p^a, it returns the slope of P, which is defined as val_PP(pi)/(a*e_PP) where val_PP(pi) is the valuation of pi at any maximal ideal PP of the maximal order above P and e_PP is the ramification index of PP.}
    if not assigned P`SlopeE then
        PP:=PrimesAbove(MaximalOrder(Algebra(P))!!P)[1];
        P`SlopeE:=SlopeE(PP);
    end if;
    return P`SlopeE;
end intrinsic;

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
        return [ P : P in PrimesAbove(p*MaximalOrder(E)) | 0 lt sp and sp lt 1 where sp:=SlopeE(P) ]; 
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
   
    // ################### 
    // Global Representatives: L and sigma_L
    // ###################
    
    // the following gives a very small polynomial hL
    if a eq 1 then
        hFq:=[0,1]; // I force L to be Q[x]/(x) so that A = E
        hL:=Parent(h) ! hFq; 
    else
        Fp:=GF(p);
        Fpy<y>:=PolynomialRing(Fp);
        Fq:=GF(q);
        U,u:=MultiplicativeGroup(Fq);
        hL:=Parent(h)!MinimalPolynomial(u(U.1));
        assert Degree(hL) eq a;
    end if;
    L:=NumberField(hL : DoLinearExtension:=true);
    OL:=MaximalOrder(L);
    zb_OL:=Basis(OL);
    PL:=Factorization(p*OL);
    assert #PL eq 1 and PL[1,2] eq 1; // L has a unique prime above p, which is unramified.
    PL:=PL[1,1];
    normPL:=Index(OL,PL);
    
    sigma_L_mod_PLm:=function(m)
    // Given a non-negative integer m returns a map L:->L which 
    // induces the a ring homomorphism on OL/PL^m
    // representing the Frobenius automorphism of L \otimes Qp.
    // If m = 0 then it just returns the identity.
        /*
        // The following code seems to work correctly if we increase a bit 'by hand' the precision m.
        // This is probably caused by the call FrobeniusAutomorphism. My guess is that it computes a root of
        // some polynomial in Lp, and this requires higher precision than the one given.
        // Alternatively the precision loss could happen in applying mLp and @@mLp. Go figure.
        if m eq 0 then
            return map<L->L | x:->x >;
        end if;
        Lp,mLp:=Completion(L,PL:Precision:=m);
        sigma_Lp:=FrobeniusAutomorphism(Lp);
        sigma_L:=map< L->L | x:->x@mLp@sigma_Lp@@mLp >;
        assert is_ring_hom_quotient_NF(sigma_L,OL,PL^m);
        */

        // new version
        if m eq 0 then
            return map<L->L | x:->x >;
        end if;
        Q,mQ:=quo<OL|PL^m>;
        frob:=mQ(L.1); // L.1 generates F_q = (OL/pOL)^*
        repeat
            old:=frob;
            frob:=frob^q;
        until frob eq old;
        zeta:=frob@@mQ; // zeta is congruent to an inertial element mod m
        // Let E=Z[zeta]. I need to buind an explicit isomorphism E/p^m*E -> OL/p^mOL
        LL<zz>:=NumberField(MinimalPolynomial(zeta) : DoLinearExtension:=true);
        isom:=iso<LL->L|[zeta]>;
        ELL:=EquationOrder(LL);
        sigma_ELL:=map<ELL->ELL | x:->&+[Eltseq(x)[i]*zz^(p*(i-1)):i in [1..Degree(L)]]>;
        F:=FreeAbelianGroup(Degree(L));
        mOL1:=map<OL->F | x:->F!Eltseq(x), y:->OL!Eltseq(y)>;
        QOL,mOL2:=quo<F | [ mOL1(b) : b in Basis(p^m*OL) ]>;
        mOL:=mOL1*mOL2;
        mELL1:=map<ELL->F | x:->F!Eltseq(x), y:->ELL!Eltseq(y)>;
        QELL,mELL2:=quo<F | [ mELL1(b) : b in Basis(p^m*ELL) ]>;
        mELL:=mELL1*mELL2;
        isomQ:=iso<QELL->QOL | [ QELL.i@@mELL@isom@mOL : i in [1..Ngens(QELL)]] >;
        sigma_L:=map<OL->OL | x:-> x@mOL@@isomQ@@mELL@sigma_ELL@mELL@isomQ@@mOL >;
        assert is_ring_hom_quotient_NF(sigma_L,OL,PL^m);
        return sigma_L;
    end function;

    // ################### 
    // Global Representatives: A
    // ###################

    fac_h_L:=Factorization( PolynomialRing(L) ! h );
    assert forall{ g : g in fac_h_L| g[2] eq 1 }; // h is assumed to be squarefree
    nfs_A:=[ NumberField(g[1] : DoLinearExtension:=true ) : g in fac_h_L ];
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
        pi_i:=PrimitiveElement(nfs_A[i]);
        pi_i:=nfs_A_abs[i]!pi_i;
        Append(~pi_A_comps,pi_i);
    end for;
    pi_A:=A!pi_A_comps;
    assert MinimalPolynomial(pi_A) eq h;
    assert forall{ i : i in [1..#nfs_A] | Evaluate(fac_h_L[i][1],pi_A_comps[i]) eq 0 };
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
    assert forall{ i : i,j in ZBasis(MaximalOrder(E)) | Delta_map(i+j) eq Delta_map(i)+Delta_map(j) };
    assert forall{ i : i,j in ZBasis(MaximalOrder(E)) | Delta_map(i*j) eq Delta_map(i)*Delta_map(j) };

    // #######################
    // tilde W_R: order isomorphic to W \otimes R
    // #######################
  
    pi_A_bar:=q/pi_A;
    gens_WR:=&cat[[ z,z*pi_A,z*pi_A_bar ] : z in zb_OL_inA] cat [pi_A, pi_A_bar];
    WR:=Order(gens_WR);

    // test
    assert pi_A in WR;
    assert q/pi_A in WR;
    assert Index(OA,WR) ge Index(MaximalOrder(E),R);
    // end test

    // #######################
    // tilde sigma (on A): acts as the L-Forbenius on L-coeffs when A is written as L+pi*L+...+pi^(deg(h)-1)L
    // #######################

    // We have defined A = prod_i L[x]/(h_i(x)).
    // In order to compute sigma, we need to understand the action of the Frobenius sigma_L of L.
    // To do so, we need to represent A as W:=L + pi*L + ... +pi^(deg(h)-1)L and compute L-isomorphism mAW:A->W.
    Vs:=[];
    vs:=<>;
    for i in [1..#nfs_A] do
        V,v:=VectorSpace(nfs_A[i],L); // v:nfs_A[i]->V
        Append(~Vs,V);
        Append(~vs,v);
    end for;
    D,embs,projs:=DirectSum(Vs); // mAD: A -> D isom
    mAD:=map<A->D |  x :-> &+[ embs[i](vs[i](nfs_A[i]!Components(x)[i])) : i in [1..#nfs_A] ] ,
                     y :-> A!< nfs_A_abs[i]!(projs[i](y))@@vs[i] : i in [1..#nfs_A] > >;
    // we compute the image of pows_pi_A in D 
    pows_pi_D:=[ mAD(x) : x in pows_pi_A ];
    W:=KSpace(L,Degree(h));
    isom:=iso< W->D | pows_pi_D >;
    mAW:=map< A->W | x:->mAD(x)@@isom, y:-> isom(y)@@mAD >;

    sigma_A_mod_I:=function(I)
    // FIXME: OL/PL^m simeq Z[zz]/p^mZ[zz]. I construct sigma_L using the second presentation.
    // So I think that I cannot use OA/I directly, but I should find an iso with R/I'R with R = OE \otimes Z[zz]...
    //
    //
    // Given an ideal I of OA such that OA/I is an OL/PL^m-module for some m, 
    // returns a map A:->A that induces sigma on OA/I, together with the precision m.
    // The returned map does not depend on I, but only on m.
    // The map and m are cached in an attribute.
        A:=Algebra(I);
        assert Order(I) eq OA;
        // If OA/I is an OL/PL^m-module from some m, then PL is the only prime of OL in its support.
        // It follows that m is the length of OA/I as an OL-module, which can be computed using the formula
        // |OL/PL|^m = |OA/I|
        normI:=Index(OA,I);
        t,m:=IsPowerOf(normI,normPL);

        //m:=30*m; printf "Warning increasing the precision\n";

        assert t;

        if not assigned A`sigma_fin_prec or A`sigma_fin_prec[2] lt m then
            sigma_L:=sigma_L_mod_PLm(m);
            sigma:=map< A-> A | x:-> (W![sigma_L(c) : c in Eltseq(mAW(x))])@@mAW >;
            //assert forall{ g : g in ZBasis(OA) | sigma(g) in OA };
            //assert is_ring_hom_quotient_AlgEt(sigma,OA,I);
            A`sigma_fin_prec:=<sigma,m>;
        end if;
        return Explode(A`sigma_fin_prec);
    end function;
    
    // OLD TEST: probably, they don't make sense when applied to something only defined on finite quotients
    // vprintf sigma,2 : "sigma: asserts"; 
    // assert x eq sigma(x) where x := Delta_map(pi);
    // vprintf sigma,2 : "."; 
    // assert forall{ x : x in [ Delta_map(y) : y in ZBasis(MaximalOrder(E))] | x eq sigma(x) };
    // vprintf sigma,2 : "."; 
    // assert forall{ x : x in ZBasis(OA) | sigma(x) in OA };
    // vprintf sigma,2 : "."; 
    // // test: sigma is a ring hom on OA/q*OA
    // Q,mQ:=ResidueRing(OA,q*OA);
    // gensQinA:=[ g@@mQ : g in Generators(Q) ];
    // assert forall{i : i,j in gensQinA | mQ(sigma(i+j)) eq mQ(sigma(i)) + mQ(sigma(j)) };
    // vprintf sigma,2 : "."; 
    // assert forall{i : i,j in gensQinA | mQ(sigma(i*j)) eq mQ(sigma(i)*sigma(j)) };
    // vprintf sigma,2 : "dome\n"; 

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
        pp:=Setseq({ oneS meet (S!!P) : P in pp });
        assert forall{P : P in pp | IsPrime(P)};
        return pp;
    end function;

    //////////////////
    // Units quotient
    //////////////////
    // Let S be an order in A', containing R'. We want to compute OA'^*/S^*\Delta'(O_E'^*)

    units_quotient_01:=function(S)
    // Given an order S in A, representing an order S' in A' returns U=OA'^*/S'^* and a map u:U->OA,
    // together with an ideal I of OA such that OA'/S' = (OA/I)/(S/I).
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
            return U,u,OneIdeal(OA);
        end if;
        indff:=Index(S,ff);
        assert forall{P : P in primes_01_S_above_ff | indff mod Index(S,P) eq 0 };
        ks:=[ Valuation(indff,p) div Valuation(Index(S,P),p) : P in primes_01_S_above_ff ];
        prod:=&*([ primes_01_S_above_ff[i]^ks[i] : i in [1..#primes_01_S_above_ff]]);
        ff_prod:=ff+prod;
        assert not 1 in ff_prod;
        assert OneIdeal(S) meet S!!(OA!!ff_prod) eq ff_prod;        
      
        I:=OA!!(ff_prod);
        R,r:=ResidueRingUnits(I);
        gens:=ResidueRingUnitsSubgroupGenerators(ff_prod);
        U,u0:=quo<R | [ g@@r : g in gens]>;
        u:=map<U->Algebra(S) |  x:-> r(x@@u0), y:->u0(y@@r) >;
        return U,u,I;
    end function;

    fixed_pts_sigma:=function(S)
    // Given an order S in A, representing an order S' in A', 
    // which is stable by the action of sigma (eg. WR),
    // returns U,u,F,m where
    // - U=OA'^*/S'^*,
    // - u is a map u:U->OA giving representatives 
    // - F is the subgroup of elements of U=OA'^*/S'^* fixed by sigma
        U,u,I:=units_quotient_01(S); //u:U->A
        Ugens_inA:=[ u(U.i) : i in [1..Ngens(U)] ];
        vprintf Algorithm_2,2 : "Computed OA'^*/S^* ...\n";
        vprintf Algorithm_2,2 : "... which has generators in tilde{OA} : %o\n", PrintSeqAlgEtQElt( Ugens_inA );
        sigma:=sigma_A_mod_I(I);
        // Question: sigma is defined only mod I. Can it send a unit to a zero-div? 
        // Is so it will create troubles in the next line
        id_sigma:=hom< U->U | [ (x/sigma(x))@@u : x in Ugens_inA ]>;
        F:=Kernel(id_sigma);
        return U,u,F;
    end function;

    // only for WR: F = Delta(OE')^*W'R^*/W'R^* inside OA'^*/W'R^*
    U,u,F:=fixed_pts_sigma(WR);
    vprintf Algorithm_2,2 : "Computed OA'^*/W'_R^* ...\n";
    units_quotient_fixed_sigma_WR_gens:=[u(F.i) : i in [1..Ngens(F)]];
    vprintf Algorithm_2,2 : "Generators of Delta(OE^*)W'_R^* in U : %o\n", PrintSeqAlgEtQElt( units_quotient_fixed_sigma_WR_gens);
    delete U,u,F;

    units_quotient_fixed_sigma:=function(S)
    // Given an order S in A, representing an order S' in A', returns Q,q where
    // Q = OA'^*/S'^*Delta(OE'^*) 
    // q is a map Q->OA giving representatives
        if not assigned S`units_quotient_fixed_sigma then
            U,u:=units_quotient_01(S); //u:U=OA'^*/S'^* -> A
            fixed_pts_gens:=[ g@@u : g in units_quotient_fixed_sigma_WR_gens];
            Q,q0:=quo<U|fixed_pts_gens>; //q0: U->U/F=Q
            q:=map<Q->Algebra(S) |  x:->u(x@@q0), y:->q0(y@@u) >;
            S`units_quotient_fixed_sigma:=<Q,q>;
        end if;
        return Explode(S`units_quotient_fixed_sigma);
    end function;

    vprintf Algorithm_2,2 : "units_quotient_fixed_sigma finished\n";

    exponents_from_Waterhouse:=function(P)
        f_nu:=InertiaDegree(P);
        g_nu:=GCD(a,f_nu); //q=p^a
        e_nu:=RamificationIndex(P);
        exps:=[];
        cp:=CartesianProduct([ [0..e_nu] : i in [1..g_nu]]);
        for tup0 in cp do
            tup:=[ tup0[i] : i in [1..g_nu] ];
            if &+tup eq Integers()!(g_nu*Valuation(pi,P)/a) then
                exp:=[ i eq 1 select 0 else Self(i-1) + tup[i-1] : i in [1..g_nu]];
                Append(~exps,exp);
            end if;
        end for;
        return exps;
    end function;
    
    // ####################
    // Algorithm 2
    // ####################

    vprintf Algorithm_2,2 : "\n\n################\nAlgorithm 2\n################\n";

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
    vprintf Algorithm_2,2 : "F-V stable O_A' ideals = %o \n",exps_01;
    pp_A_01:=&cat(pp_A_nus);
    nice_unifs_01:=Uniformizers(pp_A_01);
    vprintf Algorithm_2,2 : "nice_unifs_01 = %o\n", PrintSeqAlgEtQElt(nice_unifs_01);

    // We compute the W'_R-isomorpshim classes of W'_R-ideals.
    k:=Valuation(Index(OA,WR),p);
    WR_01:=Order( ZBasis(WR) cat ZBasis(OA!!&*[ P^(k*RamificationIndex(P)) : P in pp_A_01 ]));
    // WR_00 order is locally equal to WR' at every place of slope 01 and to OA everywhere else
    wk_01:=[ SmallRepresentative(WR!!I) : I in WKICM(WR_01)];
    vprintf Algorithm_2,2 : "[OA:WR] = %o\n",Index(OA,WR);
    vprintf Algorithm_2,2 : "[OA:WR_01] = %o\n",Index(OA,WR_01);
    vprintf Algorithm_2,2 : "number of W_R'-isomorphism classes = %o\n",#wk_01;

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
        QS,qS:=units_quotient_fixed_sigma(S); // this is now cached in an attributed
        gammas:=[ qS(x) : x in QS ];
        vprintf Algorithm_2,2 : "valsJ = %o\n", valsJ;
        vprintf Algorithm_2,2 : "deltas = %o\n", PrintSeqAlgEtQElt(deltas);
        vprintf Algorithm_2,2 : "gammas = %o\n", PrintSeqAlgEtQElt(gammas);
        assert forall{ d : d in deltas | not IsZeroDivisor(d) };
        assert forall{ g : g in gammas | not IsZeroDivisor(g) };
        II:=[ (d^-1)*g*I : d in deltas, g in gammas ];
        vprintf Algorithm_2,2 : "#II = %o\n",#II;
        vprintf Algorithm_2,2 : "valuations of the of extensions O_A' of the ideals in II = %o\n",[ [ Valuation(OA!!ii,P) : P in pp_A_01 ] : ii in II ];
        WR_01_idls_with_ext_i_to_OA_F_V_stable cat:=II;
    end for;

    vprintf Algorithm_2,2 : "number of Delta'-isomorphism classes with FV-stable extension to O_A' = %o\n",#WR_01_idls_with_ext_i_to_OA_F_V_stable;
   
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
 
    vprintf Algorithm_3,2 : "\n\n################\nAlgorithm 3\n################\n";
    exps:=exps_01[1];
    J:=WR !! Ideal(OA,&*[nice_unifs_01[i]^exps[i] : i in [1..#pp_A_01]]);
    vprintf Algorithm_3,2 : "vals of the F-V stable OA-ideal J chosen for the container = %o\n",[ Valuation(OA!!J,P) : P in pp_A_01 ];

    // We scale the ideals I by elements of E so that they are in J
    // We want to keep J/xI small
    for i in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        I:=WR_01_idls_with_ext_i_to_OA_F_V_stable[i];
        x:=ShortElement(Delta_inverse_ideal(ColonIdeal(J,I)));
        I:=Delta_map(x)*I;
        assert I subset J;
        WR_01_idls_with_ext_i_to_OA_F_V_stable[i]:=I;
    end for;
    vprintf Algorithm_3,2 : "Ideals are now Delta-scaled in J with indices = %o\n",[Index(J,I) : I in WR_01_idls_with_ext_i_to_OA_F_V_stable];

    vpNks:=[ Valuation(Index(J,I),p) : I in WR_01_idls_with_ext_i_to_OA_F_V_stable ];
    //vpNks:=[ Valuation(Exponent(Quotient(J,I)),p) : I in WR_01_idls_with_ext_i_to_OA_F_V_stable ]; //forming these quotients it is sometimes much more expensive then just working with a slightly larger m0
    m0:=Maximum(vpNks);

    //m1:=m0+52; "WARNING: m0 is forced now from ",m0,"to",m1; m0:=m1; //to force it bigger
    
    // We defind sigma so that will induce a ring hom on Q = OA/PPs_nu_m0_1_prod
    sigma:=sigma_A_mod_I(p^(m0+1)*OA); // Here, we might be asking for a higher precision than 
                                       // what we need later since we are also considering primes
                                       // of slope 0 and 1. 
                                       // I don't think it will slow down the code in a noticable way.

    vprintf Algorithm_3 : "m0 = %o\n",m0;
    vprintf Algorithm_3 : "vp(Nk)'s = %o\n",vpNks;
    vprintf Algorithm_3 : "v_nu(pi) for all nu's = %o\n",[ Valuation( pi, P ) : P in pl_01_E ];
    vprintf Algorithm_3 : "e_nu for all nu's = %o\n",[ RamificationIndex(P) : P in pl_01_E ];
    vprintf Algorithm_3 : "f_nu for all nu's = %o\n",[ InertiaDegree(P) : P in pl_01_E ];
    vprintf Algorithm_3 : "g_nu for all nu's = %o\n",[ GCD(a,InertiaDegree(P)) : P in pl_01_E ];

    QQs:=[];
    qqs:=<>;
    alpha_Q_inAs:=[];
    PPs_nus_prod_powers:=[];
    for inu->nu in pl_01_E do
        vprintf Algorithm_3,2 : "computing alpha_Q for %oth place of %o\n",inu,#pl_01_E;
        //TODO Add duality here
        PPs_nu:=primes_of_A_above_place_of_E(A,nu);
        f_nu:=InertiaDegree(nu);
        g_nu:=GCD(a,f_nu); //q=p^a
        assert #PPs_nu eq g_nu;

        Rs_nu:=[];
        rs_nu:=<>;
        Us_nu:=[];
        us_nu:=<>;
        PPs_nu_m0_1:=[];
        for PP in PPs_nu do
            PP_m0_1:=PP^(RamificationIndex(PP)*(m0+1));
            Append(~PPs_nu_m0_1,PP_m0_1);
            R,r:=ResidueRing(OA,PP_m0_1);
            vprintf Algorithm_3,2 : "R,r computed\n";
            U,u:=ResidueRingUnits(OA,PP_m0_1);
            vprintf Algorithm_3,2 : "U,u computed\n";
            Append(~Rs_nu,R);
            Append(~rs_nu,r);
            Append(~Us_nu,U);
            Append(~us_nu,u);
        end for;
        PPs_nu_m0_1_prod:=&*PPs_nu_m0_1;
        Append(~PPs_nus_prod_powers,PPs_nu_m0_1_prod);

        Q,embs,projs:=DirectSum(Rs_nu);
        pr:=map<Algebra(OA) -> Q | x:->&+[embs[i](rs_nu[i](x)) : i in [1..g_nu]], 
                                   y:->CRT( PPs_nu_m0_1 ,[projs[i](y)@@rs_nu[i] : i in [1..g_nu]])>;
        
        pi_Q:=pr(pi_A);

        vprintf Algorithm_3,2 : "asserts for Q";
        assert forall{ x : x in Generators(Q) | pr(x@@pr) eq x};
        vprintf Algorithm_3,2 : ".";
        assert is_ring_hom_quotient_AlgEt(sigma,OA,PPs_nu_m0_1_prod);
        vprintf Algorithm_3,2 : ".done\n";



        U,U_embs,U_projs:=DirectSum(Us_nu);
        U_pr:=map<Algebra(OA) -> U | x:->&+[U_embs[i](x@@us_nu[i]) : i in [1..g_nu]], 
                                     y:->CRT( PPs_nu_m0_1 ,[(U_projs[i](y))@us_nu[i] : i in [1..g_nu]])>;
        vprintf Algorithm_3,2 : "asserts for U";
        assert forall{ x : x in Generators(U) | U_pr(x@@U_pr) eq x};
        vprintf Algorithm_3,2 : ".";
        //we test that sigma is multiplicative on U
        assert forall{ i : i,j in Generators(U) | U_pr(sigma((i+j)@@U_pr)) eq  U_pr(sigma(i@@U_pr)*sigma(j@@U_pr))};
        vprintf Algorithm_3,2 : ".done\n";

        vprintf Algorithm_3,2 : "Q and U are computed\n";

        image_phi:=function(gamma)
            beta:=&+[i lt g_nu select U_embs[i]((One(A))@@us_nu[i]) else U_embs[i](gamma) : i in [1..g_nu]]; 
            beta_inA:=beta@@U_pr;    
            img:=(&*[ i eq 1 select beta_inA else sigma(Self(i-1)) : i in [1..a] ]);
            vprintf Algorithm_3,2 : "img = %o , sigma(img) = %o\n",img,sigma(img);
            assert U_pr(sigma(img)) eq U_pr(img);
            img:=U_pr(img);
            return img;
        end function;
        //phi:=hom<Us_nu[g_nu]->U | x:->image_phi(x) >;
        phi:=hom<Us_nu[g_nu]->U | [ image_phi(Us_nu[g_nu].i) : i in [1..Ngens(Us_nu[g_nu])]] >;
        
        u_nu:=Uniformizers([nu])[1]; // in E
        val_nu:=Valuation(pi,nu); // in E
        w_nu:=pi/(u_nu^val_nu); // in E
        w:=U_pr(Delta_map(w_nu)); // in E->A->U
        gamma_Ugnu:=w@@phi;
        gamma_A:=(&+[i lt g_nu select U_embs[i](One(A)@@us_nu[i]) else U_embs[i](gamma_Ugnu) : i in [1..g_nu]])@@U_pr; // in A
        beta_Q:=&+[i lt g_nu select embs[i](rs_nu[i](One(A))) else embs[i](rs_nu[i](Delta_map(u_nu^(Integers()!(val_nu*g_nu/a))))) : i in [1..g_nu]]; 
        alpha_A:=gamma_A*(beta_Q@@pr);
        assert pr(&*[ i eq 1 select alpha_A else sigma(Self(i-1)) : i in [1..a] ]) eq pi_Q;
        
        Append(~QQs,Q);
        Append(~qqs,pr);
        Append(~alpha_Q_inAs,alpha_A);
    end for;
    vprintf Algorithm_3,2 : "all alpha_Q's are computed\n";
// end of unit argument

    primes_01_WR:=Setseq(Seqset( &cat[primes_of_S_above_place_of_E(WR,P) : P in pl_01_E]));
    // Need M such that P^M*J c p^(m0+1)J, locally at P, for each P in primes_01_WR.
    // By looking at the composition series, one deduces that M \geq Truncate(Log(Index(WR,P),Index(J,p^(m0+1)J))
    // will do.
    size:=(p^(m0+1))^AbsoluteDimension(A);
    M:=Max( [ Truncate(Log(Index(WR,P),size)) : P in primes_01_WR] );
    PP01:=(&*(primes_01_WR))^M;
    
    Qm0_1,qm0_1:=Quotient(J,p^(m0+1)*J+PP01*J);
    Qm0,qm0:=Quotient(J,p^(m0)*J+PP01*J);
    // these quotiens are isomorphic to the (0,1)-part of J/p^(m0+1)J and J/p^m0J


    pr:=map< Qm0_1->Qm0 | x:->qm0(x@@qm0_1), y:->qm0_1(y@@qm0) >;
    assert forall{ z : z in ZBasis(J) | pr(qm0_1(z)) eq qm0(z) };
    alpha:=CRT( PPs_nus_prod_powers, alpha_Q_inAs );
            
    vprintf Algorithm_3,2 : "alpha = %o\n",PrintSeqAlgEtQElt([alpha])[1];
    // CHECKME : I think that sigma in the next line is alreadu computed to the right precision.
    FQm0:=hom<Qm0->Qm0 | [ qm0(alpha*sigma(Qm0.i@@qm0)) : i in [1..Ngens(Qm0)] ]>;
    FQm0_1:=hom<Qm0_1->Qm0_1 | [ qm0_1(alpha*sigma(Qm0_1.i@@qm0_1)) : i in [1..Ngens(Qm0_1)] ]>;
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
        IFV_Qm0:=I_Qm0 + 
                        sub<Qm0 | [FQm0(z) : z in Generators(I_Qm0)] > +
                        sub<Qm0 | [VQm0(z) : z in Generators(I_Qm0)] >;
        vprintf Algorithm_3,2 : "[I_Q+F_Q(I_Q)+V_Q(I_Q):I_Q] = %o\n",Index(IFV_Qm0,sub<IFV_Qm0|I_Qm0>);
        return I_Qm0 eq IFV_Qm0;
    end function;

    Delta_isom_classes_WR_F_V:=[ ];
    vprintf Algorithm_3,2 : "Started checking for F-V stability for the ...\n";
    for iI in [1..#WR_01_idls_with_ext_i_to_OA_F_V_stable] do
        vprintf Algorithm_3,2 : "%oth ideal from WR_01_idls_with_ext_i_to_OA_F_V_stable...\n",iI;
        I:=WR_01_idls_with_ext_i_to_OA_F_V_stable[iI];
        vprintf Algorithm_3,2 : "[J:I] = %o\n",Index(J,I);
        vprintf Algorithm_3,2 : "[I:p^m0*J] = %o\n",Index(I,p^m0*J);
        assert IsCoprime(Denominator(Index(I,p^m0*J)),p);
        if is_F_V_stable(I) then
            vprint Algorithm_3,2 : "...it is F-V stable\n";
            assert Order(I) eq WR;
            II:=Delta_inverse_ideal(I);
            S:=MultiplicatorRing(II);
            I`DeltaEndomorphismRing:=S;
            Append(~Delta_isom_classes_WR_F_V,I);
        else
            vprint Algorithm_3,2 : "...it is not F-V stable\n";
        end if;
    end for;

    return Delta_isom_classes_WR_F_V , pl_01_R;
end intrinsic;


/*
 

*/














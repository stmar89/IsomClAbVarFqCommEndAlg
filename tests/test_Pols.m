/* vim: set syntax=magma : */

    SetAssertions(2);
    SetColumns(0);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    Attach("~/PolsAbVarFpCanLift/ResRefCond.m");

    //SetVerbose("alpha_at_precision",2);

    PP<x>:=PolynomialRing(Integers());

    sp:=function(x)
        return StripWhiteSpace(Sprint(x));
    end function;
    pretty_fac_polys:=function(h)
        fac:=Factorization(h);
        assert forall{g:g in fac|g[2] eq 1};
        fac:=[g[1]:g in fac];
        if #fac eq 1 then
            out:=sp(h);
        else
            out:=sp(&cat["("*Sprint(g)*")":g in fac]);
        end if;
        return out;
    end function;

    test_class:=function(h,freq,verbose)
        assert IsSquarefree(h);
        if IsIrreducible(h) then
            printf "\n%o irreducible",sp(h);
        else
            printf "\n%o=%o",sp(h),pretty_fac_polys(h);
        end if;

        isog:=IsogenyClass(h);
        g:=Dimension(isog);
        q:=FiniteField(isog);
        t,p,a:=IsPrimePower(q); assert t;
        if pRank(isog) eq Dimension(isog)-1 then
            //inert
            _,ll,_:=PlacesOfQFAbove_p(isog);
            assert #ll eq 1;
            P:=ll[1];
            val:=Valuation(Algebra(P)!p,P);
            assert val in {1,2};
            inert:=val eq 1 select "inert" else "ramified";
            printf "\nexample over F%o of dimension %o and p-rank %o %o. The correct frequency is %o\n",q,Dimension(isog),pRank(isog),inert,freq;
        else
            printf "\nexample over F%o of dimension %o and p-rank %o. The correct frequency is %o\n",q,Dimension(isog),pRank(isog),freq;
        end if;
        printf "places of E <sl,g_nu,conj_st,rho> = %o\n",sp([<Slope(nu),GCD(a,InertiaDegree(nu)),
                IsConjugateStable(nu) select "t" else "f",
                BarOnIdeal(isog,P) eq P select "t" else "f" where P:=PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)[1]>
                    :nu in PlacesAboveRationalPrime(DeligneAlgebra(isog),p)]);

        iso:=IsomorphismClassesCommEndAlg(isog:dual:=true );
        if IsOrdinary(isog) then
            assert #iso eq #ICM(ZFVOrder(isog));
        end if;
        printf "number of isomorphism classes = %o\n",#iso;
        oo:=OverOrders(ZFVOrder(isog));
        ind_oo:=[Index(MaximalOrder(DeligneAlgebra(isog)),S):S in oo];
        ParallelSort(~ind_oo,~oo);
        at_p:={@ X where _,X:=IsomDataCommEndAlg(A):A in iso @};
        away_from_p:={@ X where X:=IsomDataCommEndAlg(A):A in iso @};
        
        if verbose then
            printf "number of overorders of ZFV = %o\n",#oo;
            printf "[OE:End] = %o\n",sp([Index(MaximalOrder(DeligneAlgebra(isog)),EndomorphismRing(A)):A in iso]);
            printf "End conj st = %o\n",sp([IsConjugateStable(EndomorphismRing(A)) select "t" else "f":A in iso]);
            printf "which End = %o\n",sp([Index(oo,EndomorphismRing(A)):A in iso]);
            printf "which at_p = %o\n",sp([Index(at_p,X) where _,X:=IsomDataCommEndAlg(A):A in iso]);
            printf "which away_from_p = %o\n",sp([Index(away_from_p,X) where X:=IsomDataCommEndAlg(A):A in iso]);
            printf "Pics = %o\n",sp([#PicardGroup(EndomorphismRing(A)):A in iso]);
            printf "size of Auts = %o\n",sp([#TorsionSubgroup(UnitGroup(EndomorphismRing(A))):A in iso]);
            printf "is prod = %o\n",sp([IsProductOfOrdersInFactorAlgebras(EndomorphismRing(A)) select "t" else "f":A in iso]);
        end if;

        printf "Computing duals: ";
        for A in iso do
            printf ".";
            _:=DualAbelianVarietyCommEndAlg(A);
        end for;
        printf "done!\n";

        PHIs:=AllCMTypes(IsogenyClass(iso[1]));
        all_freqs:=[];
        for iPHI->PHI in PHIs do
            ST:=ShimuraTaniyama(isog,PHI:MethodRationalSplittingField:="Magma");
            ResRefl:=IsResidueReflexFieldEmbeddable(isog,PHI:MethodRationalSplittingField:="Magma");
            freqs:=[];
            for iA->A in iso do
                pp:=PrincipalPolarizationsUpToIsomorphism(A,PHI);
                aut:=UnitGroup(EndomorphismRing(A));
                aut_pp:=TorsionSubgroup(aut);
                Append(~freqs,Sprintf("%o/%o",#pp,#aut_pp));
            end for;
            Append(~all_freqs,&+eval(Sprint(freqs)));
            if verbose then
                printf "%o-th CM-type : %o\tST,ResRefl=%o,%o\t%o\n",iPHI,&+eval(Sprint(freqs)),ST select "t" else "f",ResRefl select "t" else "f",StripWhiteSpace(Sprint(freqs));
            else
                printf "%o-th CM-type : %o\tST,ResRefl=%o,%o\n",iPHI,&+eval(Sprint(freqs)),ST select "t" else "f",ResRefl select "t" else "f";
            end if;
        end for;
        if verbose then
            testI:=[Index(I + DinvM,I meet DinvM) mod p ne 0 where DinvM:=DeltaInverseIdealpPart(isog,M)
 where I,M:=GeneralizedDeligneModule(AV) : AV in iso];
            testIv:=[Index(Iv + Ibart,Iv meet Ibart) mod p ne 0 where Ibart:=TraceDualIdeal(ComplexConjugate(I)) where Iv:=DualAbelianVarietyCommEndAlg(AV) where I:=GeneralizedDeligneModule(AV) : AV in iso];
            //testDDinvI:=[I ne Delta_inverse_ideal(DeltaIdeal(isog,I)) where I:=GeneralizedDeligneModule(AV):AV in iso];
            testDIM:=[Index(M+DI,M meet DI) mod p ne 0  where DI:=DeltaIdeal(isog,I) where I,M:=GeneralizedDeligneModule(AV):AV in iso];
            testDIvMv:=[Index(M+DI,M meet DI) mod p ne 0 where DI:=DeltaIdeal(isog,I) where I,M:=DualAbelianVarietyCommEndAlg(AV):AV in iso];
//            L,OL,PL,normPL,A,pi_A,OA,Delta_map,WR,sigma_OA_mod_I,Delta_inverse_ideal,primes_of_A_above_place_of_E,primes_of_S_of_slope_in_01,A_as_vector_space_over_L_data,bar_onA:=DieudonneAlgebraCommEndAlg(isog);
//            if assigned isog`delta_Hilbert90 then
//                delta:=isog`delta_Hilbert90;
//            else
//                delta:=One(A);
//            end if;
//            testMdeltaM:=[ Index(DM+DdM,DM meet DdM) mod p ne 0 where DM:=pPartDeltaInverseIdeal(isog,M) where DdM:=pPartDeltaInverseIdeal(isog,delta*M) where I,M:=GeneralizedDeligneModule(AV) : AV in iso]; 
//            testMvdeltaMv:=[ Index(DM+DdM,DM meet DdM) mod p ne 0 where DM:=pPartDeltaInverseIdeal(isog,Mv) where DdM:=pPartDeltaInverseIdeal(isog,bar_onA(delta)*Mv) where _,Mv:=DualAbelianVarietyCommEndAlg(AV) : AV in iso]; 
//            testIbtMv:=[Index(Ibt+DMv,Ibt meet DMv) mod p ne 0 where Ibt:=TraceDualIdeal(ComplexConjugate(I)) where I,_:=GeneralizedDeligneModule(AV) where DMv:=pPartDeltaInverseIdeal(isog,Mv) where _,Mv:=DualAbelianVarietyCommEndAlg(AV) : AV in iso];
//            printf "I==Delta^-1(M) (at p)= %o\n",testI;
//            printf "Iv==bar{I}^t (at p)  = %o\n",testIv;
//            printf "Delta(I)W == M (at p)= %o\n",testDIM;
//            printf "Delta(Iv)W == Mv (p) = %o\n",testDIvMv;
//            printf "Delta^-1(M) == Delta^-1(delta*M) (p) = %o\n",testMdeltaM;
//            printf "Delta^-1(Mv) == Delta^-1(bar(delta)*Mv) (p) = %o\n",testMvdeltaMv;
//            printf "bar{I}^t == Delta^-1(Mv) (p) = %o\n",testIbtMv;
        end if;
        return all_freqs;
    end function;

    // test_non_ord_Fq:=procedure()
    //     // non-ordinary example
    //     h:=x^6 - x^5 - 3*x^4 + 45*x^3 - 27*x^2 - 81*x + 729;
    //     // correct frequency = 20
    //     assert IsSquarefree(h);
    //     isog:=IsogenyClass(h);
    //     g:=Dimension(isog);
    //     q:=FiniteField(isog);
    //     printf "\nnon ordinary example over F%o. The correct frequency is 20\n",q;
    //     t,p,a:=IsPrimePower(q); assert t;
    //     //iso:=IsomorphismClasses(isog); // this could take up to a couple of hours. 
    //                                      // we have precomputed the data which we load in the next 5 lines of code
    //     fld:="~/IsomClAbVarFqCommEndAlg/examples/";
    //     input_ls:=Pipe("ls " cat fld,"");
    //     file:="3.9.ab_ad_bt";
    //     str:=Read(fld cat file);
    //     iso:=LoadAbVarFqCommEndAlg(isog,str);
    //     printf "number of isomorphism classes = %o\n",#iso;
    //     PHIs:=AllCMTypes(IsogenyClass(iso[1]));
    //     for iPHI->PHI in PHIs do
    //         freqs:=[];
    //         for iA->A in iso do
    //             //printf "Computing the princ pols of the %o-th isomorphism class ... ",iA;
    //             pp:=princ_pols_up_to_iso(A,PHI);
    //             //printf "got = %o\n",#pp;
    //             Append(~freqs,#pp/#TorsionSubgroup(UnitGroup(EndomorphismRing(A))));
    //         end for;
    //         printf "frequencies for the %o-th CM-type = %o\n",iPHI,&+(freqs);
    //         print freqs;
    //     end for;
    // end procedure;

    // test_non_ord_Fq_2:=procedure()
    //     // non-ordinary example
    //     h:=x^6 + 11*x^5 + 60*x^4 + 208*x^3 + 480*x^2 + 704*x + 512;
    //     // correct frequency = 9/8
    //     assert IsSquarefree(h);
    //     isog:=IsogenyClass(h);
    //     g:=Dimension(isog);
    //     q:=FiniteField(isog);
    //     printf "\nnon ordinary example over F%o. The correct frequency is 9/8\n",q;
    //     t,p,a:=IsPrimePower(q); assert t;
    //     //iso:=IsomorphismClasses(isog); // this could take up to a couple of hours. 
    //                                      // we have precomputed the data which we load in the next 5 lines of code
    //     fld:="~/IsomClAbVarFqCommEndAlg/examples/";
    //     input_ls:=Pipe("ls " cat fld,"");
    //     file:="3.8.l_ci_ia";
    //     str:=Read(fld cat file);
    //     iso:=LoadAbVarFqCommEndAlg(isog,str);
    //     printf "number of isomorphism classes = %o\n",#iso;
    //     PHIs:=AllCMTypes(IsogenyClass(iso[1]));
    //     for iPHI->PHI in PHIs do
    //         freqs:=[];
    //         for iA->A in iso do
    //             //printf "Computing the princ pols of the %o-th isomorphism class ... ",iA;
    //             pp:=princ_pols_up_to_iso(A,PHI);
    //             //printf "got = %o\n",#pp;
    //             Append(~freqs,#pp/#TorsionSubgroup(UnitGroup(EndomorphismRing(A))));
    //         end for;
    //         printf "frequencies for the %o-th CM-type = %o\n",iPHI,&+(freqs);
    //         print freqs;
    //     end for;
    // end procedure;

    // test_alm_ord_Fq:=procedure()
    //     h:=x^4+3*x^3+10*x^2+15*x+25;
    //     // correct frequency = 3/2
    //     h:=x^4+x^3+0*x^2+5*x+25;
    //     // correct frequency = 2
    //     assert IsSquarefree(h);
    //     isog:=IsogenyClass(h);
    //     g:=Dimension(isog);
    //     q:=FiniteField(isog);
    //     printf "\nalmost ordinary example over F%o. The correct frequency is \n",q;
    //     t,p,a:=IsPrimePower(q); assert t;
    //     iso:=IsomorphismClassesCommEndAlg(isog);
    //     printf "number of isomorphism classes = %o\n",#iso;
    //     PHIs:=AllCMTypes(IsogenyClass(iso[1]));
    //     for iPHI->PHI in PHIs do
    //         freqs:=[];
    //         for iA->A in iso do
    //             //printf "Computing the princ pols of the %o-th isomorphism class ... ",iA;
    //             pp:=princ_pols_up_to_iso(A,PHI);
    //             //printf "got = %o\n",#pp;
    //             Append(~freqs,#pp/#TorsionSubgroup(UnitGroup(EndomorphismRing(A))));
    //         end for;
    //         printf "frequencies for the %o-th CM-type = %o\n",iPHI,&+(freqs);
    //         //print freqs;
    //     end for;
    // end procedure;

    list_test:=[
        <x^4+16,5/8>
        ,<x^4 - 4*x^2 + 16, 5/12> // all outputs wrong in in 37.59
        ,<x^6 - x^5 + 4*x^3 - 16*x + 64, 17/12> // all outputs wrong in in 113.2
        ,<x^6 - 3*x^5 + 8*x^4 - 16*x^3 + 32*x^2 - 48*x + 64, 5> // all outputs wrong in in 121.5
        ,<x^6 + x^5 - 4*x^3 + 16*x + 64, 17/12> // all outputs wrong in in 123.2
        ,<x^6 - 3*x^5 + 8*x^4 - 20*x^3 + 32*x^2 - 48*x + 64, 3> // all outputs wrong in in 128.2
        ,<x^6 + 3*x^5 + 8*x^4 + 20*x^3 + 32*x^2 + 48*x + 64, 3> // all outputs wrong in in 152.4
        ,<x^4 + 4*x^2 + 16, 7/9> // all outputs wrong in in 172.0
        ,<x^6 - x^5 - 16*x + 64, 5> // all outputs wrong in in 208.1
        ,<x^6 + x^5 + 4*x^4 + 4*x^3 + 16*x^2 + 16*x + 64, 6> // all outputs wrong in in 224.2
        ,<x^6 - x^5 + 4*x^4 - 4*x^3 + 16*x^2 - 16*x + 64, 6> // all outputs wrong in in 244.8
        ,<x^6 + x^5 - 12*x^3 + 16*x + 64, 7/3> // all outputs wrong in in 280.0
        ,<x^6+x^5+8*x^4+4*x^3+32*x^2+16*x+64,28/9> //4-5 minutes, 224 isom cl -- all outputs are wrong 
        ,<PP!Reverse([1,3,2,-4,8,48,64]),5> //p-rank 1, I get 0
        //,<x^6-15*x^5+113*x^4-548*x^3+1808*x^2-3840*x+4096,8> //inert, I get 0, slow?
        ,<x^4-3*x^3+8*x^2-24*x+64,3>
        ,<x^4-x^3+12*x^2-9*x+81,7/4>
        ,<x^4-2*x^3+18*x^2-18*x+81,7/4>
        ,<x^4-7*x^2+49,0>
        ,<x^4+7*x^2+49,7/3>
        ,<x^6+x^5+7*x^4+6*x^3+63*x^2+81*x+729,28>
        //,<x^4-7*x^3+49*x^2-343*x+2401,-1> //interesting action of bar on the primes above nu, but slow.
        //,<x^4-4*x^3+16*x^2-64*x+256,-1>   //interesting action of bar on the primes above nu, but slow.
        ,<PP!Reverse([1,-2,5,-6,20,-32,64]),8> //almost ordinary OUTPUT does not seem constant ... sometimes I get 0
        //,<PP!Reverse([1,-1,5,-44,80,-256,4096]),10> //almost ordinary, too big
        ,<x^8+16,-1> //pRank 0 over prime field
        ,<x^6+6*x^5+20*x^4+50*x^3+100*x^2+150*x+125,15/4> //pRank 0 over Fp
        ,<x^6 - x^5 + x^4 - 2*x^3 + 3*x^2 - 9*x + 27,7/2>
        ,<x^6 + x^5 - x^4 - 2*x^3 - 3*x^2 + 9*x + 27,2>
        ,<x^6 + 3*x^5 + 3*x^4 + x^3 + 9*x^2 + 27*x + 27,2> //I get the wrong numer of isomorphis classes
        ,<x^6 + 3*x^5 + 7*x^4 + 6*x^3 + 35*x^2 + 75*x + 125,11/6>
        ,<x^6 + 4*x^5 - 18*x^3 + 100*x + 125,9/4>
        ,<PP!Reverse([1,-16,129,-639,2064,-4096,4096]),12>
        ,<PP!Reverse([1,-17,140,-701,2240,-4352,4096]),10>
        ,<PP!Reverse([1,10,69,329,1104,2560,4096]),48>
        ,<PP!Reverse([1,-17,139,-692,2224,-4352,4096]),-1> //almost ordinary, don´t know the freq, too big
        ,<PP!Reverse([1,-10,55,-221,880,-2560,4096]),-1> // 200 isom classes, don't know the freq 
        ,<x^6 - 6*x^5 + 91*x^3 - 1536*x + 4096,374> // 1100 isom classes
        ,<PP!Reverse([1,-3,33,-108,528,-768,4096]),12> //almost ordinary, too big I think
    ];


//    // only places which are not conjugate stable. do not know the timings
//    list_test:=[
//    //<x^4 + 81,9/4>
//    //<x^4 - 25*x^2 + 625,25/6>
//    //<x^4 + 625,25/4>
//    //<x^6 - 4*x^5 + 8*x^4 - 12*x^3 + 32*x^2 - 64*x + 64,2>
//    <x^6 - 4*x^5 + 12*x^4 - 28*x^3 + 48*x^2 - 64*x + 64,2>
//    ,<x^6 - 2*x^5 + 4*x^3 - 32*x + 64,4>
//    ,<x^6 - 2*x^5 + 4*x^4 - 12*x^3 + 16*x^2 - 32*x + 64,4>
//    ,<x^6 - 2*x^5 + 4*x^4 - 4*x^3 + 16*x^2 - 32*x + 64,4>
//    ,<x^6 - 2*x^5 + 8*x^4 - 12*x^3 + 32*x^2 - 32*x + 64,4>
//    ,<x^6 - x^5 - 4*x^3 - 16*x + 64,8>
//    ];

    verbose_printing:=false;
    //SetVerbose("Pols",1);
    verbose_printing:=true;

    //SetDebugOnError(true);
    good:=0;
    not_good:=0;
    for pair in list_test do
        h,freq:=Explode(pair);
        try
            t0:=Cputime();
            all_freqs:=test_class(h,freq,verbose_printing);
            t1:=Cputime(t0);
            if freq in all_freqs then
                printf "all GOOD for this example in %o secs, %o MB of RAM in use \n",t1,GetMemoryUsage() div 1024^2;
                good+:=1;
            else
                printf "-----> WRONG OUTPUTS in %o secs, %o MB of RAM in use <-----\n",t1,GetMemoryUsage() div 1024^2;
                not_good+:=1;
            end if;
            printf "--------------------------------------------------------------------\n";
            printf "--- so far we got: OK=%o --- NOT OK=%o \n",good,not_good;
            printf "--------------------------------------------------------------------\n";
        catch e
            e;
            "something went wrong";
        end try;
//        t0:=Cputime();
//        all_freqs:=test_class(h,freq,verbose_printing);
//        t1:=Cputime(t0);
//        if freq in all_freqs then
//            printf "all good in %o secs, %o MB of RAM in use \n",t1,GetMemoryUsage() div 1024^2;
//        else
//            printf "-----> WRONG OUTPUTS in %o secs, %o MB of RAM in use <-----\n",t1,GetMemoryUsage() div 1024^2;
//        end if;
//        printf "--------------------------------------------------------------------\n\n\n";
    end for;
    

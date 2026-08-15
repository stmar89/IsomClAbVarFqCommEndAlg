/* 
    Computes frequencies of non-ordinary, non-almost-ordinary isogeny classes, and check agains JB data.

    Use branch feature-bar_dual_pols on IsomClAbVarFqCommEndAlg

    parallel -j 24 --timeout 86400 --resume-failed \
        --joblog ~/IsomClAbVarFqCommEndAlg/tests/pols_parallel/joblog \
        -a ~/IsomClAbVarFqCommEndAlg/tests/pols_parallel/weil_poly_sqfree_notFp_notord_notalmord.txt \
        magma -b s:={} ~/IsomClAbVarFqCommEndAlg/tests/pols_parallel/20260730_script.m 

*/

    //SetAssertions(2);
    SetColumns(0);
    AttachSpec("~/AbVarFq/spec");
    //AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    Attach("~/PolarizationsFq/magma/misc.m");

    //SetDebugOnError(true);
    //SetVerbose("alpha_at_precision",2);

    PP<x>:=PolynomialRing(Integers());

    compute_freqs:=function(h)
        t0:=Cputime();
        isog:=IsogenyClass(h);
        g:=Dimension(isog);
        q:=FiniteField(isog);
        t,p,a:=IsPrimePower(q); assert t;
        E:=DeligneAlgebra(isog);
        pp0,pp01,pp1:=PlacesOfQFAbove_p(isog);
        pp:=pp0 cat pp01 cat pp1;
        slopes:=[Slope(P):P in pp];
        gnus:=[GCD(a,InertiaDegree(P)):P in pp];
        ParallelSort(~slopes,~pp);
        conj_st:=[ IsConjugateStable(P) select "t" else "f" : P in pp ];
        rho:=[ BarOnIdeal(isog,P) eq P select "t" else "f" where P:=PlacesOfDieudonneAlgebraAbovePlaceOfQF(isog,nu)[1] : nu in pp ];

//        if OpenTest(file_save,"r") then
//            //printf "%o already exists\n",file_save;
//            saving_str:=Read(file_save);
//            iso:=LoadAbVarFqCommEndAlg(isog,saving_str);
//        else
//            //printf "%o DOES NOT exist\n",file_save;
//            iso:=IsomorphismClassesCommEndAlg(isog : DualsCompatible:=true );
//            // to save output
//            saving_str:=SaveAbVarFqCommEndAlg(iso);
//            fprintf file_save,"%o\n",saving_str;
//        end if;
        iso:=IsomorphismClassesCommEndAlg(isog:dual:=true);
        for A in iso do
            _:=DualAbelianVarietyCommEndAlg(A);
        end for;

        PHIs:=AllCMTypes(IsogenyClass(iso[1]));
        all_freqs:=[];
        for iPHI->PHI in PHIs do
            freqs:=[];
            for iA->A in iso do
                pp:=PrincipalPolarizationsUpToIsomorphism(A,PHI);
                Append(~freqs,#pp/#TorsionSubgroup(UnitGroup(EndomorphismRing(A))));
            end for;
            Append(~all_freqs,freqs);
        end for;
        t1:=Cputime(t0);
        sums:=[&+ff:ff in all_freqs];
        output:=Sprintf("%o:a=%o:pRank=%o:slopes=%o:conj_st=%o:rho=%o:gnus=%o:isom.cl.=%o:sums_freqs_all_CMtype=%o:freqs_all_CMtype=%o:time=%o\n",h,a,pRank(isog),slopes,conj_st,rho,gnus,#iso,sums,all_freqs,t1);
        return StripWhiteSpace(output),Seqset(sums),t1;
    end function;

    h:=x^6+4*x^5+12*x^4+28*x^3+48*x^2+64*x+64;

    SetProfile(true);
    output,sums,t1:=compute_freqs(h);
    SetProfile(false);
    G:=ProfileGraph();
    printf "total time taken %o seconds\n",t1;
    ProfilePrintByTotalTime(G:Max:=10);
    // most time seems to be spent on WKICM :-(



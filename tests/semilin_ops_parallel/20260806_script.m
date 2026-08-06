/* 

    Use branch feature-bar_dual_pols on IsomClAbVarFqCommEndAlg

    parallel --resume-failed \
        --joblog ~/IsomClAbVarFqCommEndAlg/tests/semilin_ops_parallel/joblog \
        -a ~/IsomClAbVarFqCommEndAlg/tests/semilin_ops_parallel/input.m \
        magma -b s:={} ~/IsomClAbVarFqCommEndAlg/tests/semilin_ops_parallel/20260806_script.m 

*/

    SetAssertions(2);
    SetColumns(0);
    AttachSpec("~/AbVarFq/spec");
    //AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    Attach("~/PolarizationsFq/magma/misc.m");

    fld:="~/IsomClAbVarFqCommEndAlg/tests/rho_notid_a_4_gnu_4.txt/";
    run:="20260806_";
    
    ok_file:=fld*run*"ok.txt";
    issue_file:=fld*run*"issues.txt";

    //SetDebugOnError(true);
    //SetVerbose("alpha_at_precision",2);

    PP<x>:=PolynomialRing(Integers());
    SetAssertions(2);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    m0:=10;
    try
        cc:=[StringToInteger(c):c in Split(s,"[,]")];
        g:=(#cc-1) div 2;
        q:=Round(cc[1]^(1/g));
        _,p,a:=IsPrimePower(q);
        h:=PP!cc;
        ccs:=StripWhiteSpace(Sprint(cc));
        isog:=IsogenyClass(h);
        conj_pairs,rho_id,rho_notid:=SortPlacesOfQFAbove_p(isog);
        _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        out_str:=Sprintf("%o,%o,%o\ta=%o\t[OA:JOA]=",#conj_pairs,#rho_id,#rho_notid,a);
        plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
        plE:=plE0 cat plE01 cat plE1;
        plA:=&cat[PlacesOfDieudonneAlgebraSortedBySigmaAbovePlaceOfQF(isog,nu):nu in plE];
        inds:=[];
        Js:=[];
        for exps in ExponentsDual(isog) do
            assert #plA eq #exps;
            JOA:=&*[ plA[i]^exps[i] : i in [1..#exps] ]; 
            ind:=Index(OA,JOA);
            test,n:=IsPowerOf(ind,p);
            assert test;
            J:=WR!!JOA;
            ZBasisLLL(J);
            out_str cat:=Sprintf("%o^%o ",p,n);
            Append(~Js,J);
        end for;
        out_str cat:=Sprintf("\t%o",ccs);
        for J in Js do
            _:=SemilinearOperatorsDualComp(isog,J,m0);
        end for;
        fprintf ok_file,"%o\n",out_str;
    catch e
        fprintf issue_file,"%o %o\n",out_str,e`Position;
    end try;

    quit;

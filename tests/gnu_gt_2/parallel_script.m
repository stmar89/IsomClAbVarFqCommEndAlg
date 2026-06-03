/*
*/

    SetAssertions(1);
    SetColumns(0);
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    file_out:="~/IsomClAbVarFqCommEndAlg/tests/gnu_gt_2/output.m";

    PP<x>:=PolynomialRing(Integers());
    h:=PP!(eval(cc));
    times:=[];
    
    tt0:=Cputime();
    for method in ["(0,1)","all"] do
        if assigned isog then delete isog; end if;
        isog:=IsogenyClass(h);
        t0:=Cputime();
        if assigned n_iso then n_iso_old:=n_iso; end if;
        n_iso:=#IsomorphismClassesCommEndAlg(isog:slopesDieudonneModules:=method);
        warning:=not assigned n_iso_old or n_iso_old eq n_iso select "   " else "ERR";
        t1:=Round(Cputime(t0));
        Append(~times,t1);
    end for;
    _,a:=IsPowerOf(FiniteField(isog),CharacteristicFiniteField(isog));
    nus0,nus01,nus1:=PlacesOfQFAbove_p(isog);
    nus:=nus0 cat nus01 cat nus1;
    sl:=[Slope(nu):nu in nus];
    ParallelSort(~sl,~nus);
    sl:=StripWhiteSpace(Sprintf("sl=%o",sl));
    gnus:=StripWhiteSpace(Sprintf("gnus=%o",[GCD(InertiaDegree(nu),a):nu in nus]));
    n_iso:=Sprintf("n_iso=%o",n_iso);
    tt1:=Round(Cputime(tt0));

    output:=Sprintf("tot=%2om %2os \"(0,1)\"=%2om %2os \"all\"=%2om %2os %o %9o %13o %14o %o",
            tt1 div 60,tt1 mod 60,
            times[1] div 60,times[1] mod 60,
            times[2] div 60,times[2] mod 60,
            warning,
            n_iso,
            sl,gnus,StripWhiteSpace(Sprint(Coefficients(h)))
            );
    printf "%o\n",output;
    fprintf file_out,"%o\n",output;

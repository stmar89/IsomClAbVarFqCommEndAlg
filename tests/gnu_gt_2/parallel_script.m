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
    output:=[];

    for method in ["(0,1)","all"] do
        if assigned isog then delete isog; end if;
        isog:=IsogenyClass(h);
        _,a:=IsPowerOf(FiniteField(isog),CharacteristicFiniteField(isog));
        nus0,nus01,nus1:=PlacesOfQFAbove_p(isog)
        nus:=nus0 cat nus01 cat nus1;
        sl:=[Slope(nu):nu in nus];
        ParallelSort(~sl,~nus);
        sl:=StripWhiteSpace(Sprint(sl));
        gnus:=StripWhiteSpace(Sprint([GCD(InertiaDegree(nu),a):nu in nus]));
        t0:=Cputime();
        if assigned n_iso then n_iso_old:=n_iso; end if;
        if IsOrdinary(isog) and method eq "(0,1)" then
            n_iso:=#ICM(ZFVOrder(sog);
            method_print:="ICM"
        else
            n_iso:=#IsomorphismClassesCommEndAlg(isog:slopesDieudonneModules:=method);
            method_print:=method;
        end if;
        warning:=not assigned n_iso_old or n_iso_old eq n_iso select "" else "<------------ outputs are different!";
        t1:=Round(Cputime(t0));
        Append(~output,Sprintf("%20o %20o %20o %5o : isom classes %3o computed in %o mins %o secs %o",label,sl,gnus,method_print,n_iso,t1 div 60,t1 mod 60,warning));
    end for;
    printf "%o\n",Join(output,"\n");
    fprintf file_out,"%o\n",Join(output,"\n");


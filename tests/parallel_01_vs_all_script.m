/*
parallel script, to run on screen
    parallel -j 10 --shuf -a ~/IsomClAbVarFqCommEndAlg/tests/parallel_01_vs_all_input.m magma -b cc:={} ~/IsomClAbVarFqCommEndAlg/tests/parallel_01_vs_all_script.m
*/

    //SetAssertions(2);

    AttachSpec("~/AbVarFq/spec");
    //AttachSpec("~/AlgEt/spec"); // this spec file in is magma since 2.29
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    function Base26Encode(n)
            alphabet := "abcdefghijklmnopqrstuvwxyz";
            s := alphabet[1 + n mod 26]; n := ExactQuotient(n-(n mod 26),26);
            while n gt 0 do
                    s := alphabet[1 + n mod 26] cat s; n := ExactQuotient(n-(n mod 26),26);
            end while;
            return s;
    end function;

    function IsogenyLabel(f)
    // returns the LMFDB label of the isogeny class determined by a Weil polynomial f.
        g:=Degree(f) div 2;
        q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
        str1:=Reverse(Prune(Coefficients(f)))[1..g];
        str2:="";
        for a in str1 do
            if a lt 0 then
                str2:=str2 cat "a" cat Base26Encode(-a) cat "_";
                else
                str2:=str2 cat Base26Encode(a) cat "_";
            end if;
        end for;
        str2:=Prune(str2);
        isog_label:=Sprintf("%o.%o.",g,q) cat str2;
        return isog_label;
    end function;

    PP<x>:=PolynomialRing(Integers());
    // the input variable is called "h"
    h:=PP!Reverse(eval(cc));
    assert IsSquarefree(h);
    label:=IsogenyLabel(h);

    for method in ["(0,1)","all"] do
        if assigned isog then delete isog; end if;
        isog:=IsogenyClass(h);
        sl:=StripWhiteSpace(Sprint(Sort([Slope(nu):nu in nus0 cat nus01 cat nus1 where nus0,nus01,nus1:=PlacesOfQFAbove_p(isog)])));
        t0:=Cputime();
        if assigned iso then n_iso_old:=#iso; end if;
        iso:=IsomorphismClassesCommEndAlg(isog:slopesDieudonneModules:=method);
        warning:=not assigned n_iso_old or n_iso_old eq #iso select "" else "<------------ outputs are different!";
        t1:=Round(Cputime(t0));
        printf "%20o %20o %5o : isom classes %3o computed in %o mins %o secs %o\n",label,sl,method,#iso,t1 div 60,t1 mod 60,warning;
    end for;


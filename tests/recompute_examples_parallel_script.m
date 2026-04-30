/*
parallel script, to run on screen
    parallel -a ~/IsomClAbVarFqCommEndAlg/tests/recompute_examples_parallel_input magma -b h:={} ~/IsomClAbVarFqCommEndAlg/tests/recompute_examples_parallel_script.m
*/

    //SetAssertions(2);

    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/spec"); // this spec file in is magma since 2.29
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
    h:=eval(h);
    assert IsSquarefree(h);
    isog:=IsogenyClass(h);
    g:=Dimension(isog);
    q:=FiniteField(isog);
    t,p,a:=IsPrimePower(q); assert t;
    label:=IsogenyLabel(h);

    t0:=Cputime();
    iso:=IsomorphismClasses(isog);
    t1:=Cputime(t0);
    t1:=Truncate(t1) div 60; // in minutes

    printf "isogeny class %o \tisomorphism classes %o\tcomputed in %o minutes\n",label,#iso,t1;

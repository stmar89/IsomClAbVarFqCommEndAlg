    
    SetAssertions(2);

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
    input:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/weil_poly_all.txt"));
    tot:=#input; perc:=0;
    output:=[];
    for i->cc in input do
        if Truncate(100*i/tot) gt perc then perc+:=1; printf "%o%% ",perc; end if;
        c:=eval(cc);
        g:=(#c-1) div 2;
        if not IsCoprime(c[1],c[g]) then
            if g ge 2 then
                h:=PP!c;
                if IsSquarefree(h) then
                    isog:=IsogenyClass(h:Check:=false);
                    p:=CharacteristicFiniteField(isog);
                    _,a:=IsPowerOf(FiniteField(isog),p);
                    if a gt 2 then
                        plE0,plE01,plE1:=PlacesOfQFAbove_p(isog);
                        if exists{P:P in plE01|GCD(InertiaDegree(P),a) gt 2} then
                            IsogenyLabel(h),h;
                            Append(~output,h);
                        end if;
                    end if;
                end if;
            end if;
        end if;
    end for;

    file_out:="~/IsomClAbVarFqCommEndAlg/tests/gnu_gt_2_output.txt";
    for h in output do
        fprintf file_out,"%o\n",StripWhiteSpace(Sprint(Coefficients(h)));
    end for;

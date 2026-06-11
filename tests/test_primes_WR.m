    SetColumns(0); 
    SetAssertions(2);

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
    //all:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/weil_poly_sq_not_prime.txt"));
    all:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/weil_poly_sq_not_prime-ord-almord.txt"));
    tot:=#all; perc:=0;
    for i->s in all do
        if Truncate(100*i/tot) gt perc then perc+:=1; printf " %o%%",perc; end if;
        t0:=Cputime();
        cc:=[ StringToInteger(c) : c in Split(s,"[ ,]") ];
        g:=(#cc-1) div 2;
        h:=PP!cc;
        isog:=IsogenyClass(h:Check:=false);
        p:=CharacteristicFiniteField(isog);
        _,a:=IsPowerOf(FiniteField(isog),p);
        if a gt 5 then continue; end if; // too expensive
        str:=Sprintf("\na,g=%o,%o\t",a,g);
        _,_,_,_,_,_,OA,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        pp0,pp01,pp1:=PrimesOfSAbove_p(isog,WR);
        str cat:=Sprintf("#pps=%o,%o,%o\tsecs=%o\t%o",#pp0,#pp01,#pp1,Cputime(t0),h);
        if #pp01 gt 1 then
            str;
        end if;
    end for;

    /*

    AttachSpec("~/AbVarFq/spec");
    PP<x>:=PolynomialRing(Integers());
    file1:="~/IsomClAbVarFqCommEndAlg/tests/weil_poly_sq_not_prime.txt";
    file2:="~/IsomClAbVarFqCommEndAlg/tests/weil_poly_sq_not_prime-ord-almord.txt";
    all:=Split(Read("~/IsomClAbVarFqCommEndAlg/tests/weil_poly_all.txt"));
    tot:=#all; perc:=0;
    for i->s in all do
        if Truncate(100*i/tot) gt perc then perc+:=1; printf "%o%% ",perc; end if;
        cc:=[ StringToInteger(c) : c in Split(s,"[ ,]") ];
        g:=(#cc-1) div 2;
        q:=Round(cc[1]^(1/g));
        if not IsPrime(q) then
            h:=PP!cc;
            if IsSquarefree(h) then
                fprintf file1,"%o\n",StripWhiteSpace(s);
                ord:=IsCoprime(cc[g+1],q);
                if ord then continue; end if;
                isog:=IsogenyClass(h:Check:=false);
                f:=pRank(isog);
                if f eq g-1 then continue; end if;
                fprintf file2,"%o\n",StripWhiteSpace(s);
            end if;
        end if;
    end for;
    Pipe("cat ~/IsomClAbVarFqCommEndAlg/tests/weil_poly_all.txt| wc -l","r");
    Pipe("cat " * file1 * "| wc -l","r");
    Pipe("cat " * file2 * "| wc -l","r");

    */

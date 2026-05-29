/*
parallel script, to run on screen
    rm ~/IsomClAbVarFqCommEndAlg/tests/recompute_examples_parallel_output_all.m; \
    rm ~/IsomClAbVarFqCommEndAlg/tests/recompute_examples_parallel_output_01.m; \
    parallel -j 7 -a ~/IsomClAbVarFqCommEndAlg/tests/recompute_examples_parallel_input \
        magma -b h_s:={} ~/IsomClAbVarFqCommEndAlg/tests/recompute_examples_parallel_script.m
*/

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
    // the input variable is called "h_s"
    h_s:=eval(h_s);
    h:=h_s[1];
    slopes:=h_s[2];
    output:="";
    
        output cat:=Sprintf("-------------------------\n");

        isog:=IsogenyClass(h);
        g:=Dimension(isog);
        q:=FiniteField(isog);
        t,p,a:=IsPrimePower(q); assert t;
        t0:=Cputime();
        iso:=IsomorphismClassesCommEndAlg(isog:slopesDieudonneModules:=slopes);
        t1:=Round(Cputime(t0));
        output cat:=Sprintf("%o\n\tUsing slopesDieudonneModules:=%o and SetAssertions(%o),\n\twe got %o isomorphism classes in %o mins %o secs\n",
                IsogenyLabel(h),slopes,GetAssertions(),#iso,t1 div 60,t1 mod 60);
printf "%o Using slopesDieudonneModules:=%o and SetAssertions(%o),\n\twe got %o isomorphism classes in %o mins %o secs\n",IsogenyLabel(h),slopes,GetAssertions(),#iso,t1 div 60,t1 mod 60;
        t0:=Cputime();
        gen_del_mods:=[GeneralizedDeligneModule(A):A in iso];
        t1:=Round(Cputime(t0));
        output cat:=Sprintf("\tGeneralizedDeligneModules computed in %o mins %o secs\n",
                t1 div 60,t1 mod 60);
        nu0,nu01,nu1:=PlacesOfQFAbove_p(isog);
        nus:=nu0 cat nu01 cat nu1;
        data_nus:=[<Slope(nu),RamificationIndex(nu),GCD(a,InertiaDegree(nu))>:nu in nus];
        data_nus:=StripWhiteSpace(Sprint(data_nus));
        output cat:=Sprintf("\t<s_nu,e_nu,g_nu> = %o\n",data_nus);

        R:=ZFVOrder(isog);
        E:=Algebra(R);

        oo:=OverOrders(R);
        OE:=MaximalOrder(E);
        _,P,_:=PrimesOfZFVAbove_p(isog);
        assert #P eq 1;
        P:=P[1];
        // P is the local-local maximal ideal of R above p

        is_maximal_at_01:=function(S)
        // check if the overorder S of R is maximal locally at its local-local part.
            return S!!OneIdeal(OE) eq OneIdeal(S) + S!!OE!!P;
        end function;

        Ep,mEp:=TotallyRealSubAlgebra(E);
        OEp:=MaximalOrder(Ep);
        output cat:=Sprintf("\tp is %o totally split in E^+\n\n",(#PlacesAboveRationalPrime(Ep,p) eq g select "" else "not "));
        OEp:=[mEp(z):z in ZBasis(OEp)];
        contains_OEp:=func< S | forall{z:z in OEp|z in S}>;


        Q,mQ,F,V,_,_,J:=SemilinearOperators(isog);
        ind:=[Index(OE,S):S in oo];
        ParallelSort(~ind,~oo);
        Reverse(~oo);
        ends:=[ EndomorphismRing(A) : A in iso ];
        output cat:=Sprintf("For each overorder S, we print the following string of data:\n\tiS = which overorder of Z[pi,q/pi]\n\t[OE:S]\n\tw(S) = #iso away from DM\n\td(S) = #Dieudonné modules with End S\n\th(S)=#Pic(S)\n\ta numbers of the DM with End S\n\tis S maximal at (0,1)?\n\tdoes S contain O_{E^+}?\n\tindices of minimal overorders\n\n");
        for iS->S in oo do
            dmS:={@ dmA where _,dmA:=IsomDataCommEndAlg(A) : A in iso | EndomorphismRing(A) eq S @};
            wS:={@ wA where wA:=IsomDataCommEndAlg(A) : A in iso | EndomorphismRing(A) eq S @};
            // a-numbers
            a_nums:=[];
            for dm in dmS do
                assert dm subset J;
                M:=sub<Q|[mQ(z):z in ZBasis(dm)]>;
                FM:=sub<M|[M!F(M.i):i in [1..Ngens(M)]]>;
                VM:=sub<M|[M!V(M.i):i in [1..Ngens(M)]]>;
                Append(~a_nums,Ilog(q,Index(M,FM+VM)));
            end for;
            // indices of minimal overorders (to find the place of S in the graph of inclusions)
            ind_min_oo:=[ Index(oo,T) : T in MinimalOverOrders(S) ];
            output cat:=Sprintf("\t%o,%o,%o,%o,%o,%o,%o,%o,%o\n",iS,Index(OE,S),#wS,#dmS,#PicardGroup(S),a_nums,is_maximal_at_01(S),contains_OEp(S),ind_min_oo);
        end for;

    file_output:="~/IsomClAbVarFqCommEndAlg/tests/recompute_examples_parallel_output_" * (slopes eq "all" select "all" else "01") * ".m";
    fprintf file_output,"%o",output;
    quit;

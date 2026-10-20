/*
    parallel -a weil_poly_sqfr_copRK_gt_1_noFp_sorted.txt --j 60 --joblog joblog --timeout 18000 magma -b cc:={} script.m
*/
    
    PP<x>:=PolynomialRing(Integers());

    AttachSpec("../../depends.spec");
    AttachSpec("../../spec");    

    SetClassGroupBounds("GRH");

    file_out:="output.txt";
    
    overorders_maximal_at_ss:=function(R)
    // Returns all the overorders of the Frobenius Order R of a non ordinary isogeny class 
    // which are locally maximal at the local local prime P:=p*R+,pi*R,(q/pi)*R.
        K:=Algebra(R);
        h:=DefiningPolynomial(K);
        g:=Degree(h) div 2;
        _,q:=IsPower(ConstantCoefficient(h),g);
        pi:=PrimitiveElement(K);
        pp:=[ P : P in PrimesAbove(q*R) | pi in P and q/pi in P];
        assert #pp eq 1;
        P:=pp[1];
        OO:=MaximalOrder(K);
        OO1:=R!!OneIdeal(OO);
        OOP:=OO!!P;
        ROP:=R!!(OOP);
        oo:=OverOrders(R);
        output:=[ S : S in oo | OO1 eq ( (R!!OneIdeal(S))+ROP ) ];

        OOP:=PrimesAbove(OOP);
        assert #OOP eq 1;
        OOP:=OOP[1];
        ram:=RamificationIndex(OOP);
        assert ram in {1,2};
        return output,ram;
    end function;

    coeffs:=[StringToInteger(c):c in Split(cc,"[ ,]")];
    h:=PP!coeffs;
    g:=Degree(h) div 2;
    _,q:=IsPower(ConstantCoefficient(h),g);
    isog:=IsogenyClass(h : Check:=false);
    t,p,a:=IsPrimePower(q);
    assert t; delete t;
    prank:=pRank(isog);

    t0:=Cputime();
    iso:=IsomorphismClassesCommEndAlg(isog);
    t1:=Cputime(t0);

    ends:={ EndomorphismRing(X) : X in iso };
    num_isom:=#iso;
    num_test:=0;
    R:=ZFVOrder(isog);
    oo_max_at_ss,ram:=overorders_maximal_at_ss(R);
    is_R_End:=R in ends;
    is_R_End:=is_R_End select "t" else "f";
    End_not_max_at_ss:=exists{S:S in ends|S notin oo_max_at_ss};
    End_not_max_at_ss:=End_not_max_at_ss select "t" else "f"; 
    _,plE01,_:=PlacesOfQFAbove_p(isog);
    max_gnu_01:=Max([GCD(InertiaDegree(P),a): P in plE01]);
    output:=StripWhiteSpace(Sprintf("%o:%o:%o:%o:%o:%o",#iso,t1,max_gnu_01,is_R_End,End_not_max_at_ss,cc));

    printf "%o\n",output;
    fprintf file_out,"%o\n",output;

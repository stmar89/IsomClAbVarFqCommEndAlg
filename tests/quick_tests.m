    PP<x>:=PolynomialRing(Integers());

    AttachSpec("../depends.spec");
    AttachSpec("../spec");    

    SetColumns(0);
    SetClassGroupBounds("GRH");
    
    SetAssertions(2);

    input:=[
        // ordinary
        x^4 + 13*x^3 + 244*x^2 + 2119*x + 26569,
        x^6 - 6*x^5 + 75*x^4 - 276*x^3 + 1875*x^2 - 3750*x + 15625,
        x^8 + 5*x^7 + 24*x^6 + 73*x^5 + 188*x^4 + 365*x^3 + 600*x^2 + 625*x + 625,
        // Centeleghe-Stix (CS), i.e. over the prime field, not ordinary
        x^2 + 101,
        x^8 - x^7 - 125*x + 625,
        x^10 + 2*x^8 - x^7 + 4*x^6 - 24*x^5 + 12*x^4 - 9*x^3 + 54*x^2 + 243,
        // not CS, almost ordinary inert
        x^2 + 121,
        x^4 - 5*x^3 + 242*x^2 - 605*x + 14641,
        x^6 - 7*x^5 + 21*x^4 - 5*x^3 + 525*x^2 - 4375*x + 15625,
        // not CS, almost ordinary ramified
        x^4 + 9*x^3 + 49*x^2 + 3087*x + 117649,
        x^6 + 33*x^4 - 45*x^3 + 825*x^2 + 15625,
        x^8 - 2*x^7 + 6*x^6 - x^5 + 8*x^4 - 4*x^3 + 96*x^2 - 128*x + 256,
        // non of the above
        x^8 - 2*x^7 + 5*x^6 + 6*x^5 - 8*x^4 + 24*x^3 + 80*x^2 - 128*x + 256,
        x^8 + 9*x^6 + 2*x^5 + 48*x^4 + 8*x^3 + 144*x^2 + 256,
        x^8 - 2*x^7 + 7*x^6 - 10*x^5 + 20*x^4 - 40*x^3 + 112*x^2 - 128*x + 256
    ];

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

    test_save_load:=procedure(isog,iso)
    // This procedure run a bunch of tests to check that the saving and loading functions are working properly.
    // A failed assert is triggered if something goes wrong.
        h:=WeilPolynomial(isog);
        str:=SaveAbVarFqCommEndAlg(iso);
        delete isog;
        isog:=IsogenyClass(h);
        iso_test:=LoadAbVarFqCommEndAlg(isog,str);
        assert #iso eq #iso_test;
        _,J,dJ,Q,qm,F,V:=SemilinearOperators(isog);
        assert #Q eq #Quotient(J,dJ);
        for i in [1..#iso_test] do
            assert aNumber(iso_test[i]) eq aNumber(iso[i]);
            I,M,L,S:=IsomDataCommEndAlg(iso[i]);
            II,MM,LL,SS:=IsomDataCommEndAlg(iso_test[i]);
            _:=I eq 2*I; //to assign the Hash
            _:=II eq 2*II; //to assign the Hash
            _:=M eq 2*M; //to assign the Hash
            _:=MM eq 2*MM; //to assign the Hash
            _:=L eq 2*L; //to assign the Hash
            _:=LL eq 2*LL; //to assign the Hash
            assert II`Hash eq I`Hash;
            assert MM`Hash eq M`Hash;
            assert LL`Hash eq L`Hash;
            assert S`Hash eq SS`Hash;
            assert MM subset J;
            MQ:=sub<Q|[qm(z):z in ZBasis(MM)]>;
            FMQ:=sub<Q|[F(MQ.i):i in [1..Ngens(MQ)]]>;
            VMQ:=sub<Q|[V(MQ.i):i in [1..Ngens(MQ)]]>;
            assert FMQ+VMQ subset MQ;
        end for;
    end procedure;

    for h in input do
        g:=Degree(h) div 2;
        _,q:=IsPower(ConstantCoefficient(h),g);
        isog:=IsogenyClass(h : Check:=false);
        t,p,a:=IsPrimePower(q);
        assert t; delete t;
        prank:=pRank(isog);
        is_ord:=prank eq g;
        is_alm_ord:=prank eq g-1;
        is_cs:=q eq p;

        t0:=Cputime();
        iso:=IsomorphismClassesCommEndAlg(isog);
        t1:=Cputime(t0);

        // If the precision of the computed semilinear operator is 0, aNumber will trigger an error.
        // If this is the case, we rerun the computation of the isomorphism classes with increased
        // precision.
        try
            _:=[aNumber(A):A in iso];
        catch e
            delete isog;
            isog:=IsogenyClass(h : Check:=false);
            iso:=IsomorphismClassesCommEndAlg(isog : IncreaseMinimumPrecisionForSemilinearFVBy:=1);
        end try;
            
        test_save_load(isog,iso);

        ends:={ EndomorphismRing(X) : X in iso };
        num_isom:=#iso;
        num_test:=0;
        R:=ZFVOrder(isog);
        ends_test:={};
        descr:="";
        if is_ord then 
            num_test:=#ICM(R);
            ends_test:=Seqset(OverOrders(R));
            descr:="ordinary"; 
        elif p eq q then
            num_test:=#ICM(R);
            ends_test:=Seqset(OverOrders(R));
            descr:="over Fp"; 
        elif is_alm_ord then
            oo_max_at_ss,ram:=overorders_maximal_at_ss(R);
            icm:=&+[ #ICM_bar(S) : S in oo_max_at_ss ];
            ends_test:=Seqset(oo_max_at_ss);
            if ram eq 2 then //ramified
                num_test:=icm;
                descr:="alm. ord. ramif.";
            else //inert
                num_test:=2*icm;
                descr:="alm. ord. inert";
            end if;
        end if;
        if num_test gt 0 then
            if not ( num_isom eq num_test and ends eq ends_test) then
                out:=Sprintf("ERROR !!! <------------------- expected %o classes.",t1,descr,num_test);
            else
                out:="OK";
            end if;
        else
            out:="NA";
        end if;

        printf "Computed %5o isom. cl. in %o secs.\tComparison with previous results: %o.\tThe isogeny class is %o with Weil poly %o\n",num_isom,t1,out,descr,h;
    end for;

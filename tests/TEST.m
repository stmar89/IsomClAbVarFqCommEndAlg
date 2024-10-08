/* vim: set syntax=magma : */

    // Testing on a few classes together with saving loading.

    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    PP<x>:=PolynomialRing(Integers());

    hs:=[
        x^4 - 9*x^3 + 36*x^2 - 72*x + 64, // 1 iso
        x^2 - 3*x + 9,
        x^2 + 9,
        PP![ 16, 8, 8, 2, 1 ], //4 classes
        x^4 + 4*x^2 + 16
        ];

    for h in hs do
        h;
        isog:=IsogenyClass(h);
        time iso:=IsomorphismClasses(isog);
        str:=SaveAbVarFqCommEndAlg(iso);
        delete isog;
        isog:=IsogenyClass(h);
        iso_test:=LoadAbVarFqCommEndAlg(isog,str);
        assert #iso eq #iso_test;
        _,J,dJ,Q,qm,F,V:=SemilinearOperators(isog);
        assert #Q eq #Quotient(J,dJ);
        for i in [1..#iso_test] do
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
    end for;


    // parameters for quick tests
    allow_cs:=false;
    //allow_cs:=true;
    allow_ord:=false;
    //allow_ord:=true;
    //allow_alm_ord:=false;
    allow_alm_ord:=true;
    q_max:=11;

    PP<x>:=PolynomialRing(Integers());
    to_be_excluded:=[
        x^4 - 4*x^3 + 8*x^2 - 32*x + 64, // It seems that WKICM(WR_01) is very big
        x^4 + 4*x^3 + 16*x^2 + 32*x + 64, // too slow (funnily, its twist is not that slow)
        x^4+64,// Terminate. Why?
        x^6 - x^5 + 4*x^3 - 4*x + 8 // Magma internal error ... buh...
        ];

    // TeST on a very big set of inputs: comparing ordinary, cs, almost ordinary data

    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");
    SetAssertions(2);

    overorders_maximal_at_ss:=function(R)
    // R = Z[F,V] of an almost ord isogney clas
        K:=Algebra(R);
        q:=Truncate(ConstantCoefficient(DefiningPolynomial(K))^(2/Dimension(K)));
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

    //SetVerbose("DieudonneModules",2);
    //SetVerbose("Algorithm_3",2);
    SetAssertions(2);
    SetDebugOnError(true);

    all_weil_poly:=Split(Read("weil_poly_all.txt"));

    for cc in all_weil_poly do
        coeff:=eval(cc);
        h:=PP!coeff;
        if IsSquarefree(h) and not h in to_be_excluded then
            g:=Degree(h) div 2;
            q:=Truncate(ConstantCoefficient(h)^(1/g));
            I:=IsogenyClass(h : Check:=false);
            t,p,a:=IsPrimePower(q);
            assert t; delete t;
            prank:=pRank(I);
            is_ord:=prank eq g;
            is_alm_ord:=prank eq g-1;
            is_cs:=q eq p;
            if  (q le q_max)
                and (is_ord select allow_ord else true)
                and (is_alm_ord select allow_alm_ord else true)
                and (is_cs select allow_cs else true) 
                        then
                printf "%50o = ",h;
                    t0:=Cputime();
                    iso:=IsomorphismClasses(I);
                    t1:=Cputime(t0);
                    ends:={ EndomorphismRing(X) : X in iso };
                    num_isom:=#iso;
                    S:=&meet(ends);
                    unique_min_end:=S in ends; // is there a unique minimal end?
                    str:=Sprintf("min end? %o ",unique_min_end select "Y" else "N");
                    jumps:=not forall{ T : T in ends | forall{ TT : TT in MinimalOverOrders(T) | TT in ends } };
                    str cat:=Sprintf("jumps? %o ",jumps select "Y" else "N");
                    printf "%o", str;
                    num_test:=0;
                    R:=ZFVOrder(I);
                    if IsCoprime(coeff[g+1],q) then 
                        num_test:=#ICM(R);
                        ends_test:=Seqset(OverOrders(R));
                        descr:="ord"; 
                    elif p eq q then
                        num_test:=#ICM(R);
                        ends_test:=Seqset(OverOrders(R));
                        descr:="cs"; 
                    else
                        if is_alm_ord then
                            oo:=FindOverOrders(R);
                            oo_max_at_ss,ram:=overorders_maximal_at_ss(R);
                            icm:=&+[ #ICM_bar(S) : S in oo_max_at_ss ];
                            ends_test:=Seqset(oo_max_at_ss);
                            if ram eq 2 then //ramified
                                num_test:=icm;
                                descr:="alm ord - ram";
                            else //inert
                                num_test:=2*icm;
                                descr:="alm ord - inert";
                            end if;
                        end if;
                    end if;
                    if num_test gt 0 then
                        if not ( num_isom eq num_test and ends eq ends_test) then
                            "failure <-------------------",t1,descr,"computed",num_isom,"expected",num_test;
                        else
                            "good",t1,descr;
                        end if;
                    else
                        "can't compare to previous data",t1;
                    end if;
                //catch
                //    e;
                //    e`Object;
                //    e`Position;
                //    "error detected";
                //    break cc;
                //end try;
            end if;
        end if;
    end for;


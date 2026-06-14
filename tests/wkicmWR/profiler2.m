
    SetDebugOnError(true);
    SetAssertions(1);

    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    fld:="~/IsomClAbVarFqCommEndAlg/examples/";
    PP<x>:=PolynomialRing(Integers());
    check:=Split(Pipe("ls " cat fld,"r"));
    inputs:=[
    <x^6-3*x^4+2*x^3-12*x^2+64,"3.4.a_ad_c">,
    <x^6+2*x^5-x^4-6*x^3-4*x^2+32*x+64,"3.4.c_ab_ag">,
    <(x^2-2*x+4)*(x^2+2*x+4),"2.4.a_e">,
    <x^8+x^7+x^6+4*x^5-4*x^4+16*x^3+16*x^2+64*x + 256,"4.4.b_b_e_ae">,
    <x^8 - 6*x^7 + 18*x^6 - 36*x^5 + 68*x^4 - 144*x^3 + 288*x^2 - 384*x + 256,"4.4.ag_s_abk_cq">,
    <x^6 + 11*x^5 + 60*x^4 + 208*x^3 + 480*x^2 + 704*x + 512,"3.8.l_ci_ia">,
    <x^6 - x^5 - 3*x^4 + 45*x^3 - 27*x^2 - 81*x + 729,"3.9.ab_ad_bt">
    ];

    for input in inputs do
        h,file:=Explode(input);
        assert IsSquarefree(h);

        isog:=IsogenyClass(h);
        _,_,_,_,_,_,_,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        t0:=Cputime();
        new:=#WeakEquivalenceClassMonoidWR(isog);
        t_new:=Cputime(t0);

        isog:=IsogenyClass(h);
        _,_,_,_,_,_,_,_,WR:=DieudonneAlgebraCommEndAlg(isog);
        t0:=Cputime();
        old:=#WKICM(WR);
        t_old:=Cputime(t0);

        test:=new eq old select "OK " else "ERR";

        p:=CharacteristicFiniteField(isog);
        q:=FiniteField(isog);
        a:=Ilog(p,q);
        R:=ZFVOrder(isog);
        E:=DeligneAlgebra(isog);
        pi:=PrimitiveElement(E);
        pps:=PrimesAbove(p*R);
        pps0:=[P:P in pps|not pi in P and q/pi in P and not IsInvertible(P)];
        gnus:=[GCD(a,Ilog(p,Index(R,P))):P in pps0];
        
        printf "%o\tt_old=%o\tt_new=%o\tgnus_0=%o\t%o\n",test,t_old,t_new,gnus,file;
    end for;

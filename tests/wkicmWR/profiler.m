
    SetDebugOnError(true);
    SetAssertions(1);

    AttachSpec("~/AbVarFq/spec");
    AttachSpec("~/AlgEt/specMod");
    AttachSpec("~/AlgEt/specMtrx");
    AttachSpec("~/IsomClAbVarFqCommEndAlg/spec");

    fld:="~/IsomClAbVarFqCommEndAlg/examples/";
    PP<x>:=PolynomialRing(Integers());
    check:=Split(Pipe("ls " cat fld,"r"));
    h:=PP![256,-64,176,-40,56,-10,11,-1,1];
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
    pps0:=[P:P in pps|not pi in P and q/pi in P];
    gnus:=[GCD(a,Ilog(p,Index(R,P))):P in pps0];
    
    printf "%o\tt_old=%o\tt_new=%o\tgnus_0=%o\n",test,t_old,t_new,gnus;
